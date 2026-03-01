(**
  module: Common.Types
  description: A modularized type system.

  It incorporates the following features:
  - Polarity (positive/negative) to distinguish data and codata types
  - Chirality (producer/consumer) to distinguish terms
  - Higher-kinded types
  - Generalized algebraic data types
  - Generalized algebraic codata types
  - Algebraic data types automatically promoted to the kind level
*)

module Prim = struct
  open Identifiers
  let fun_sym = Path.of_primitive 1 "fun"
  let apply_sym = Path.access fun_sym "apply"
  let lower_sym = Path.of_primitive 2 "lower"
  let return_sym = Path.access lower_sym "return"
  let raise_sym = Path.of_primitive 3 "raise"
  let thunk_sym = Path.access raise_sym "thunk"
end

module type BASE = sig
  type polarity
  val eq_polarity: polarity -> polarity -> bool
  val code_polarity: polarity
  val data_polarity: polarity
  val polarities: polarity list

  type 'a chiral
  val chiral_map: ('a -> 'b) -> 'a chiral -> 'b chiral
  val strip_chirality: 'a chiral -> 'a
  val mk_producer: 'a -> 'a chiral
  val mk_consumer: 'a -> 'a chiral
  val is_producer: 'a chiral -> bool
  val is_consumer: 'a chiral -> bool
end

(* External types are always positive *)
type ext_type = Int

type data_sort = Data | Codata

module TypeSystem(Base: BASE) = struct

  open Identifiers

  let ( let* ) = Result.bind

  (* Types *)
  type typ =
      Base of Base.polarity (* Base kinds *)
    | Arrow of typ * typ (* Only for kinds *)
    | Ext of ext_type
    | TVar of Ident.t
    | TMeta of Ident.t
    | Sgn of Path.t * typ list (* Signatures; applied data or codata type *)
    | PromotedCtor of Path.t * Path.t * typ list
    | Forall of Ident.t * typ * typ (* ∀(x: k). body, has kind - when x: k implies body: - *)

  let as_typ = fun pol -> Base pol

  type chiral_typ = typ Base.chiral

  let strip_chirality = Base.strip_chirality

  let chiral_map = Base.chiral_map

  let polarity_of_data_sort = function
      Data -> Base.data_polarity | Codata -> Base.code_polarity
    
  let data_sort_as_typ ds = as_typ (polarity_of_data_sort ds)

  (* Constructor or destructor
    In the Melcore language, a destructor syntactically declared as
      dtor: {qi's} main -> argN -> ... -> arg0
    has
      - quantified = qi's
      - existential = [] (we don't allow it)
      - argument_types = [arg0; ...; argN] (in reverse order for easier unification)
      - main = the "this"-type *)
  type xtor =
    { name: Path.t
    ; quantified: (Ident.t * typ) list
    ; existentials: (Ident.t * typ) list
    ; argument_types: chiral_typ list
    (* `main` is the result type of data types and the "this"
      type of codata types *)
    ; main: typ
    }

  (* Declaration 
     
     An instantiated declaration has:
     - param_kinds = [] (no more parameters to bind)
     - type_args = the types that were substituted for parameters
     
     For example, lower[Int] has name=lower, param_kinds=[], type_args=[Int].
  *)
  type dec =
    { name: Path.t
    ; data_sort: data_sort
    ; param_kinds: typ list
    ; type_args: typ list  (* Instantiation arguments, empty for uninstantiated *)
    ; xtors: xtor list
    }

  (* Promoted constructor info *)
  type promoted_ctor_info =
    { quantified : (Ident.t * typ) list
    ; arg_kinds : typ list
    ; result_kind : typ
    }
  
  (* Kind errors *)
  type kind_error =
      Unbound_type_variable of Ident.t
    | Unbound_meta_variable of Ident.t
    | Unknown_data_type of Path.t
    | Unknown_promoted_ctor of Path.t * Path.t
    | Not_a_promoted_type of Path.t
    | Invalid_kind of typ
    | Kind_mismatch of { expected: typ; actual: typ; in_type: typ }
    | Arity_mismatch of { kind: typ option; num_args: int }
    | Arrow_domain_not_typ of typ
    | Arrow_codomain_not_typ of typ
    | Too_many_arguments of { kind: typ; extra_args: typ list }

  let ident_find (v: Ident.t) (tbl: 'a Ident.tbl) (err: kind_error) : ('a, kind_error) result =
    match Ident.find_opt v tbl with Some x -> Ok x | None -> Error err

  let path_find (p: Path.t) (tbl: 'a Path.tbl) (err: kind_error) : ('a, kind_error) result =
    match Path.find_opt p tbl with Some x -> Ok x | None -> Error err

  (* Substitution *)
  type subst = typ Ident.tbl

  (* Context *)
  type context =
    { decs: dec Path.tbl
    ; data_kinds: typ Path.tbl
    ; promoted_ctors: promoted_ctor_info Path.tbl
    ; subst: subst
    ; typ_vars: typ Ident.tbl
    }

  let rec apply_subst sbs t =
    match t with
      TMeta v ->
        (match Ident.find_opt v sbs with
          Some t' -> apply_subst sbs t'
        | None -> t)
    | TVar v ->
        (* Also resolve TVars if mapped (for pattern-bound type vars) *)
        (match Ident.find_opt v sbs with
          Some t' -> apply_subst sbs t'
        | None -> t)
    | Arrow (t1, t2) -> Arrow (apply_subst sbs t1, apply_subst sbs t2)
    | Sgn (name, args) -> Sgn (name, List.map (apply_subst sbs) args)
    | PromotedCtor (data_name, ctor_name, args) ->
        PromotedCtor (data_name, ctor_name, List.map (apply_subst sbs) args)
    | _ -> t

  let rec occurs v t =
    match t with
      TVar v' -> Ident.equal v v'
    | TMeta v' -> Ident.equal v v'
    | Arrow (t1, t2) -> occurs v t1 || occurs v t2
    | Forall (x, k, body) -> occurs v k || (not (Ident.equal v x) && occurs v body)
    | Sgn (_, args) -> List.exists (occurs v) args
    | PromotedCtor (_, _, args) -> List.exists (occurs v) args
    | _ -> false

  let rec apply_fresh_subst sbs t =
    match t with
      TVar v ->
        (match Ident.find_opt v sbs with Some t' -> t' | None -> t)
    | TMeta v ->
        (match Ident.find_opt v sbs with Some t' -> t' | None -> t)
    | Arrow (t1, t2) ->
        Arrow (apply_fresh_subst sbs t1, apply_fresh_subst sbs t2)
    | Sgn (name, args) ->
        Sgn (name, List.map (apply_fresh_subst sbs) args)
    | PromotedCtor (d, c, args) ->
        PromotedCtor (d, c, List.map (apply_fresh_subst sbs) args)
    | Forall (x, k, body) ->
        (* Avoid capture: if x is in sbs, we need to rename *)
        if Ident.contains_key x sbs then
          let x' = Ident.mk (Ident.name x) in
          let body' = apply_fresh_subst (Ident.add x (TVar x') Ident.emptytbl) body in
          Forall (x', apply_fresh_subst sbs k, apply_fresh_subst sbs body')
        else
          Forall (x, apply_fresh_subst sbs k, apply_fresh_subst sbs body)
    | _ -> t

  let rec unify t1 t2 sbs =
    let rec fold_zip acc = function
      | [], [] -> acc
      | x :: xs, y :: ys ->
          Option.bind acc (fun subst' ->
            fold_zip (unify x y subst') (xs, ys))
      | _ -> None
    in
    let t1 = apply_subst sbs t1 in
    let t2 = apply_subst sbs t2 in
    match t1, t2 with
      TVar v1, TVar v2 when Ident.equal v1 v2 -> Some sbs
    | TMeta v1, TMeta v2 when Ident.equal v1 v2 -> Some sbs
    | TMeta v, t | t, TMeta v ->
        if occurs v t then None else Some (Ident.add v t sbs)
    | TVar _, _ | _, TVar _ -> None
    | Arrow (a1, b1), Arrow (a2, b2) ->
        Option.bind (unify a1 a2 sbs) (unify b1 b2)
    | Forall (x1, k1, body1), Forall (x2, k2, body2) ->
        (* Alpha-rename x2 to x1 in body2 for comparison *)
        let renamed = Ident.add x2 (TVar x1) Ident.emptytbl in
        let body2' = apply_fresh_subst renamed body2 in
        Option.bind (unify k1 k2 sbs) (unify body1 body2')
    | Ext e, Ext e' when e = e' -> Some sbs
    | Base pol1, Base pol2 when Base.eq_polarity pol1 pol2 -> Some sbs
    | Sgn (name1, args1), Sgn (name2, args2) when
          Path.equal name1 name2 &&
          List.length args1 = List.length args2 ->
        fold_zip (Some sbs) (args1, args2)
    | PromotedCtor (d1, c1, args1), PromotedCtor (d2, c2, args2) when
          Path.equal d1 d2 && Path.equal c1 c2 &&
          List.length args1 = List.length args2 ->
        fold_zip (Some sbs) (args1, args2)
    | _ -> None

  let equiv sbs t1 t2 =
    match unify t1 t2 sbs with Some _ -> true | None -> false

  let freshen_meta quantified =
    let fresh_vars, subst =
      List.fold_left (fun (vars, s) (v, k) ->
        let fresh = Ident.mk (Ident.name v) in
        ((fresh, k) :: vars, Ident.add v (TMeta fresh) s)
      ) ([], Ident.emptytbl) quantified
    in (List.rev fresh_vars, subst)

  let freshen_rigid quantified =
    let fresh_vars, subst =
      List.fold_left (fun (vars, s) (v, k) ->
        let fresh = Ident.mk (Ident.name v) in
        ((fresh, k) :: vars, Ident.add v (TVar fresh) s)
      ) ([], Ident.emptytbl) quantified
    in (List.rev fresh_vars, subst)

  let freshen_kinds (kinds: typ list) : (Ident.t * typ) list =
    List.map (fun k -> (Ident.fresh (), k)) kinds

  (* A constructor is promotable (can be lifted to the type/kind level) if:
    1. It has no existential variables
    2. All its argument types are producer types (Prd)
    3. Its result type is the canonical form:
        Sgn(typeName, [TVar q1, TVar q2, ...])
      where the variables are exactly the quantified variables, in order. *)
  let is_promotable type_name (ctor: xtor) : bool =
    let no_existentials = (ctor.existentials = []) in
    let only_producer_args =
      List.for_all (Base.is_producer) ctor.argument_types in
    let canonical_result =
      match ctor.main with
        Sgn (name, args) when Path.equal name type_name ->
          List.length args = List.length ctor.quantified &&
          List.for_all2 (fun arg (qvar, _) ->
            match arg with TVar v -> Ident.equal v qvar | _ -> false
          ) args ctor.quantified
      | _ -> false
    in no_existentials && only_producer_args && canonical_result

  (* Check if a declaration can serve as a DataKind (if all constructors
    are promotable). Only data types are promotable. *)
  let is_dec_promotable (dec: dec) : bool =
    (Base.eq_polarity (polarity_of_data_sort dec.data_sort) Base.data_polarity) &&
    List.for_all (is_promotable dec.name) dec.xtors

  (* Helper to sequence result checks over a list *)
  let rec check_all f = function
      [] -> Ok () | x :: xs -> let* _ = f x in check_all f xs

  (* Helper to sequence result checks over two lists *)
  let rec check_all2 f xs ys =
    match xs, ys with
      [], [] -> Ok ()
    | x :: xs', y :: ys' -> let* _ = f x y in check_all2 f xs' ys'
    | _ -> Error (Arity_mismatch { kind = None; num_args = 0 })

  (* Check if a type is a valid kind (can classify types) *)
  let rec valid_kind (ctx: context) (t: typ) : (unit, kind_error) result =
    match t with
      Base _ -> Ok ()
    | Arrow (k1, k2) -> let* _ = valid_kind ctx k1 in valid_kind ctx k2
    | Sgn (name, args) ->
        let* kind =
          path_find name ctx.data_kinds (Not_a_promoted_type name) in
        let* _ = check_all (valid_kind ctx) args in
        let rec arity k =
          match k with Arrow (_, r) -> 1 + arity r | _ -> 0 in
        (match kind, args with
          Base _, [] -> Ok ()
        | Arrow _, _ when List.length args <= arity kind -> Ok ()
        | _, [] -> Ok ()
        | _, _ -> Error (Arity_mismatch {
          kind = Some kind; num_args = List.length args }))
    | TVar v ->
        let* k = ident_find v ctx.typ_vars (Unbound_type_variable v) in
        valid_kind ctx k
    | TMeta v ->
        let* k = ident_find v ctx.typ_vars (Unbound_meta_variable v) in
        valid_kind ctx k
    | _ -> Error (Invalid_kind t)

  (* Infer the kind of a type *)
  let rec infer_kind (ctx: context) (t: typ) : (typ, kind_error) result =
    match t with
      Base _ -> Ok t
    | Ext _ -> Ok (as_typ Base.data_polarity)
    | TVar v -> ident_find v ctx.typ_vars (Unbound_type_variable v)
    | TMeta v ->
        (match Ident.find_opt v ctx.subst with
          Some t' -> infer_kind ctx t'
        | None -> ident_find v ctx.typ_vars (Unbound_meta_variable v))
    | Arrow (t1, t2) ->
        let* k1 = infer_kind ctx t1 in
        let* k2 = infer_kind ctx t2 in
        (* Arrow types at the kind level: both must be valid kinds *)
        let* _ = valid_kind ctx k1 in
        let* _ = valid_kind ctx k2 in
        Ok (as_typ Base.code_polarity) (* Arrow types are negative *)
    | Forall (x, k, body) ->
        (* ∀(x: k). body : - when body : - under x: k *)
        let* _ = valid_kind ctx k in
        let ctx' = { ctx with typ_vars = Ident.add x k ctx.typ_vars } in
        let* _ = check_kind ctx' body (as_typ Base.code_polarity) in
        Ok (as_typ Base.code_polarity)
    | Sgn (name, args) ->
        let* dec = path_find name ctx.decs (Unknown_data_type name) in
        let full_kind = List.fold_right (fun k acc ->
          Arrow (k, acc)
        ) dec.param_kinds (data_sort_as_typ dec.data_sort)
        in
        apply_args ctx full_kind args
    | PromotedCtor (data_name, ctor_name, args) ->
        let key = Path.access data_name (Path.name ctor_name) in
        let* info =
          path_find key ctx.promoted_ctors
            (Unknown_promoted_ctor (data_name, ctor_name)) in
        let num_quantified = List.length info.quantified in
        let num_kind_args = List.length info.arg_kinds in
        let expected_args = num_quantified + num_kind_args in
        if List.length args <> expected_args then
          Error (Arity_mismatch {
            kind = Some info.result_kind; num_args = List.length args })
        else
          let type_args = List.filteri (fun i _ -> i < num_quantified) args in
          let kind_args = List.filteri (fun i _ -> i >= num_quantified) args in
          let ty_subst =
            List.fold_left2 (fun s (v, _) t -> Ident.add v t s)
              Ident.emptytbl info.quantified type_args
          in
          let* _ = check_all2 (fun (_, expected_kind) arg ->
            let expected_kind' = apply_fresh_subst ty_subst expected_kind in
            check_kind ctx arg expected_kind'
          ) info.quantified type_args in
          let subst_arg_kinds =
            List.map (apply_fresh_subst ty_subst) info.arg_kinds in
          let* _ = check_all2 (fun expected_kind arg ->
            check_kind ctx arg expected_kind
          ) subst_arg_kinds kind_args in
          let subst_result = apply_fresh_subst ty_subst info.result_kind in
          Ok subst_result

  (* Apply type arguments to a kind, returning the resulting kind *)
  and apply_args (ctx: context) (kind: typ) (args: typ list)
      : (typ, kind_error) result =
    match kind, args with
      k, [] -> Ok k
    | Arrow (param_kind, result_kind), arg :: rest ->
        let* _ = check_kind ctx arg param_kind in
        apply_args ctx result_kind rest
    | _, extra_args -> Error (Too_many_arguments { kind; extra_args })

  (* Check that a type has the expected kind *)
  and check_kind (ctx: context) (t: typ) (expected_kind: typ)
      : (unit, kind_error) result =
    let* inferred_kind = infer_kind ctx t in
    if equiv ctx.subst inferred_kind expected_kind then Ok ()
    else Error (Kind_mismatch {
      expected = expected_kind; actual = inferred_kind; in_type = t })

  and is_inhabitable (ctx: context) (t: typ) : bool =
    match infer_kind ctx t with
      Ok (Base p) -> List.exists (Base.eq_polarity p) Base.polarities
    | Ok _ | Error _ -> false

  (* Check that a constructor or destructor is well-kinded *)
  let check_xtor_well_kinded
        (ctx: context) (ds: data_sort) (xtor: xtor) : bool =
      let ty_ctx =
      List.fold_left (fun acc (v, k) ->
          { acc with typ_vars = Ident.add v k acc.typ_vars }
        ) ctx (xtor.quantified @ xtor.existentials)
    in
    (* kinds_valid && args_valid && result_valid *)
    List.for_all (fun (_, k) ->
      Result.is_ok (valid_kind ty_ctx k)
    ) (xtor.quantified @ xtor.existentials) &&
    List.for_all (fun ct ->
      (* Argument types must be inhabitable (kind + or -) *)
      is_inhabitable ty_ctx (strip_chirality ct)
    ) xtor.argument_types &&
    Result.is_ok (check_kind ty_ctx xtor.main (data_sort_as_typ ds))

  (* Check that a declaration is well-kinded *)
  let check_dec_well_kinded (ctx: context) (dec: dec) : bool =
    let param_kinds_valid =
      List.for_all (fun k ->
        Result.is_ok (valid_kind ctx k)
      ) dec.param_kinds in
    let ctors_valid =
      List.for_all (check_xtor_well_kinded ctx dec.data_sort) dec.xtors in
    param_kinds_valid && ctors_valid

  (* Build PromotedCtorInfo for a promotable constructor *)
  let build_promoted_ctor_info (ctor: xtor) : promoted_ctor_info =
    { quantified = ctor.quantified
    ; arg_kinds = List.map strip_chirality ctor.argument_types
    ; result_kind = ctor.main
    }

  (* Build promoted constructor entries for a declaration (only if all
    ctors are promotable) *)
  let build_promoted_ctors (d: dec) : (Path.t * promoted_ctor_info) list =
    if is_dec_promotable d then
      List.map (fun (c: xtor) ->
        (Path.access d.name (Path.name c.name), build_promoted_ctor_info c)
      ) d.xtors
    else []

  (* Compute the kind of a data type from its param_kinds *)
  let data_kind_from_param_kinds (param_kinds: typ list) : typ =
    List.fold_right (fun k acc ->
      Arrow (k, acc)
    ) param_kinds (as_typ Base.data_polarity)

  (* Add a declaration to the context *)
  let add_dec (ctx: context) (dec: dec) : context =
    let new_decs = Path.add dec.name dec ctx.decs in
    let is_prom = is_dec_promotable dec in
    let new_data_kinds =
      if is_prom then
        let kind = data_kind_from_param_kinds dec.param_kinds in
        Path.add dec.name kind ctx.data_kinds
      else ctx.data_kinds
    in
    let new_promoted_ctors =
      List.fold_left (fun acc (k, v) ->
        Path.add k v acc
      ) ctx.promoted_ctors (build_promoted_ctors dec)
    in
    { ctx with
      decs = new_decs
    ; data_kinds = new_data_kinds
    ; promoted_ctors = new_promoted_ctors
    }

  (* Add a declaration to the context, checking well-kindedness and promoting
    as data kind, if possible *)
  let add_declaration (ctx: context) (dec: dec) : context option =
    let temp_ctx = { ctx with decs = Path.add dec.name dec ctx.decs } in
    if not (check_dec_well_kinded temp_ctx dec) then None
    else Some (add_dec ctx dec)

  (* Add multiple declarations in sequence *)
  let add_declarations (ctx: context) (decs: dec list) : context option =
    List.fold_left (fun ctx_opt dec ->
      Option.bind ctx_opt (fun ctx -> add_declaration ctx dec)
    ) (Some ctx) decs

  (* Add mutually recursive declarations *)
  let add_declarations_recursive (ctx: context) (decs: dec list) : context option =
    let temp_ctx = List.fold_left add_dec ctx decs in
    let all_valid = List.for_all (check_dec_well_kinded temp_ctx) decs in
    if not all_valid then None
    else Some temp_ctx

  (* Check if a constructor is reachable given scrutinee type arguments *)
  let is_xtor_reachable (_ctx: context) (dec: dec) (xtor: xtor) (scrutinee_args: typ list)
      : subst option =
    let _, fresh_subst = freshen_meta xtor.quantified in
    let fresh_result = apply_fresh_subst fresh_subst xtor.main in
    let scrutinee_type = Sgn (dec.name, scrutinee_args) in
    unify fresh_result scrutinee_type Ident.emptytbl

  (* Check exhaustivity: all reachable constructors must be covered *)
  let check_exhaustive
      (ctx: context) (d: dec) (scrutinee_args: typ list) (covered_ctors: Path.t list)
      : Path.t list =
    List.filter_map (fun (x: xtor) ->
      if not (List.exists (Path.equal x.name) covered_ctors) &&
         Option.is_some (is_xtor_reachable ctx d x scrutinee_args)
      then Some x.name
      else None
    ) d.xtors

  (** Instantiate a declaration with concrete type arguments.
      
      Given a declaration like:
        data List[a: +] where
          Nil : List[a]
          Cons(hd: Prd a, tl: Prd List[a]) : List[a]
      
      And type arguments [Int], produces:
        data List where
          Nil : List
          Cons(hd: Prd Int, tl: Prd List) : List
      
      Also filters xtors to only those that are reachable at this instantiation.
      For example, if we have a GADT:
        data Expr[a: +] where
          IntLit(n: Prd Int) : Expr[Int]
          BoolLit(b: Prd Bool) : Expr[Bool]
      
      Then instantiate_dec expr_dec [Int] would only include IntLit.
  *)
  let instantiate_dec (dec: dec) (type_args: typ list) : dec =
    (* Collect all TMeta identifiers in a type *)
    let rec collect_metas acc t =
      match t with
      | TMeta m -> m :: acc
      | TVar _ | Base _ | Ext _ -> acc
      | Arrow (t1, t2) -> collect_metas (collect_metas acc t1) t2
      | Sgn (_, args) -> List.fold_left collect_metas acc args
      | PromotedCtor (_, _, args) -> List.fold_left collect_metas acc args
      | Forall (_, k, body) -> collect_metas (collect_metas acc k) body
    in
    (* Instantiate a single xtor with a substitution derived from unification.
      For GADTs, xtor.quantified may have different length than type_args,
      so we use the substitution from unifying xtor.main with the target type.
      
      fresh_quant_metas/fresh_exist_metas: the fresh metas created from xtor.quantified/existentials. 
      Only those that still appear in the instantiated types become existentially bound. *)
    let instantiate_xtor (xtor: xtor) ((fresh_quant_metas, fresh_exist_metas): (Ident.t * typ) list * (Ident.t * typ) list) (xtor_subst: subst) : xtor =
      let inst_args = List.map (chiral_map (apply_fresh_subst xtor_subst)) xtor.argument_types in
      let inst_main = apply_fresh_subst xtor_subst xtor.main in
      (* Only keep fresh metas that still appear in the instantiated types *)
      let all_metas = 
        collect_metas (List.fold_left (fun acc ct -> collect_metas acc (strip_chirality ct)) [] inst_args) inst_main in
      let remaining_quant = List.filter (fun (m, _) ->
        List.exists (Ident.equal m) all_metas
      ) fresh_quant_metas in
      let remaining_exist = List.filter (fun (m, _) ->
        List.exists (Ident.equal m) all_metas
      ) fresh_exist_metas in
      { name = xtor.name
      ; quantified = []  (* No longer quantified after instantiation *)
      ; existentials = remaining_quant @ remaining_exist  (* Fresh metas from both become existential *)
      ; argument_types = inst_args
      ; main = inst_main
      }
    in
    (* For GADT filtering, convert TVars in type_args to fresh metas so they can
      unify. This allows filtering like: vec{a}{succ(k)} excludes nil because
      succ(k) can never unify with zero, even though a and k are polymorphic.
      
      We maintain a mapping from generated metas back to original types so we
      can build the correct instantiation substitution. *)
    let tvar_to_meta = ref Ident.emptytbl in
    let rec typ_vars_to_metas t =
      match t with
        TVar v -> 
          (* Check if we already have a meta for this TVar *)
          (match Ident.find_opt v !tvar_to_meta with
            Some m -> TMeta m
          | None ->
              let m = Ident.mk (Ident.name v) in
              tvar_to_meta := Ident.add v m !tvar_to_meta;
              TMeta m)
      | TMeta _ -> t
      | Arrow (t1, t2) -> Arrow (typ_vars_to_metas t1, typ_vars_to_metas t2)
      | Sgn (n, args) -> Sgn (n, List.map typ_vars_to_metas args)
      | PromotedCtor (d, c, args) -> PromotedCtor (d, c, List.map typ_vars_to_metas args)
      | Forall (x, k, body) -> Forall (x, typ_vars_to_metas k, typ_vars_to_metas body)
      | _ -> t
    in
    let meta_type_args = List.map typ_vars_to_metas type_args in
    let meta_scrutinee = Sgn (dec.name, meta_type_args) in
    (* Build reverse mapping: meta -> original TVar *)
    let meta_to_tvar = Ident.of_list
      (List.map (fun (v, m) -> (m, TVar v)) (Ident.to_list !tvar_to_meta)) in
    let reachable_xtors = 
      List.filter_map (fun (xtor: xtor) ->
        (* Check if xtor's main type can unify with the scrutinee type.
          Freshen ALL type params (both quantified and existentials) to metas. *)
        let all_params = xtor.quantified @ xtor.existentials in
        let fresh_all_metas, fresh_subst = freshen_meta all_params in
        let fresh_quant_metas = List.filteri (fun i _ -> i < List.length xtor.quantified) fresh_all_metas in
        let fresh_exist_metas = List.filteri (fun i _ -> i >= List.length xtor.quantified) fresh_all_metas in
        let fresh_main = apply_fresh_subst fresh_subst xtor.main in
        let result = unify fresh_main meta_scrutinee Ident.emptytbl in
        match result with
          Some unified_subst -> 
            (* Compose: fresh_subst maps original vars to metas,
              unified_subst maps those metas to types (possibly containing 
              metas from meta_scrutinee). We need to convert those back to TVars. *)
            let resolve_meta t = apply_fresh_subst meta_to_tvar (apply_subst unified_subst t) in
            let combined_subst = Ident.map_tbl resolve_meta fresh_subst in
            Some (instantiate_xtor xtor (fresh_quant_metas, fresh_exist_metas) combined_subst)
        | None -> None
      ) dec.xtors
    in
    { name = dec.name
    ; data_sort = dec.data_sort
    ; param_kinds = []  (* No more params after instantiation *)
    ; type_args = type_args  (* Store the instantiation arguments *)
    ; xtors = reachable_xtors
    }

  (* Primitives *)

  (* fun[a, b] is the negative (codata) function type.
     apply destructor takes: (continuation: Cns b, arg: Prd a)
     Order: [Cns b; Prd a] = [continuation; argument] *)
  let apply_xtor =
    let a = Ident.mk "a" in
    let b = Ident.mk "b" in
    { name = Prim.apply_sym
    ; quantified =
      [ (a, as_typ Base.data_polarity)
      ; (b, as_typ Base.code_polarity)
      ]
    ; existentials = []
    ; argument_types =
        (* Order: [Cns b; Prd a] = [continuation; argument] *)
        [ Base.mk_consumer (TVar b)
        ; Base.mk_producer (TVar a)
        ]
    ; main = Sgn (Prim.fun_sym, [TVar a; TVar b])
    }
  
  let fun_dec =
    { name = Prim.fun_sym
    ; data_sort = Codata
    ; param_kinds = [as_typ Base.data_polarity; as_typ Base.code_polarity]
    ; type_args = []  (* Uninstantiated *)
    ; xtors = [ apply_xtor ]
    }

  let fun_sgn a b = Sgn (Prim.fun_sym, [a; b])

  (* raise[a] is the positive (data) type wrapping a negative.
    thunk constructor takes: (producer of a) - the wrapped codata value *)
  let thunk_xtor =
    let a = Ident.mk "a" in
    { name = Prim.thunk_sym
    ; quantified = [ (a, as_typ Base.code_polarity) ]
    ; existentials = []
    ; argument_types = [ Base.mk_producer (TVar a) ]  (* Lhs a = producer *)
    ; main = Sgn (Prim.raise_sym, [TVar a])
    }
  
  let raise_dec =
    { name = Prim.raise_sym
    ; data_sort = Data
    ; param_kinds = [as_typ Base.code_polarity]
    ; type_args = []  (* Uninstantiated *)
    ; xtors = [ thunk_xtor ]
    }
  
  let raise_sgn a = Sgn (Prim.raise_sym, [a])

  (* lower[a] is the negative (codata) type wrapping a positive.
    return destructor takes: (continuation: Cns a) - where to send the value *)
  let return_xtor =
    let a = Ident.mk "a" in
    { name = Prim.return_sym
    ; quantified = [ (a, as_typ Base.data_polarity) ]
    ; existentials = []
    ; argument_types = [ Base.mk_consumer (TVar a) ]  (* Rhs a = consumer *)
    ; main = Sgn (Prim.lower_sym, [TVar a])
    }

  let lower_dec =
    { name = Prim.lower_sym
    ; data_sort = Codata
    ; param_kinds = [as_typ Base.data_polarity]
    ; type_args = []  (* Uninstantiated *)
    ; xtors = [ return_xtor ]
    }

  let lower_sgn a = Sgn (Prim.lower_sym, [a])

  (* The empty context has the primitive declarations *)
  let empty_context : context =
    add_declarations
      { subst = Ident.emptytbl
      ; decs = Path.emptytbl
      ; data_kinds = Path.emptytbl
      ; promoted_ctors = Path.emptytbl
      ; typ_vars = Ident.emptytbl
      } 
      [ fun_dec; raise_dec; lower_dec ]
    |> Option.get 

end