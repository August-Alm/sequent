(**
  module: Core.Types
  description: A polarized type system for the core sequent calculus.
*)

open Common.Identifiers

let ( let* ) = Result.bind

(* Types *)
type typ =
  | Typ
  | Int
  | TVar of Ident.t
  | TMeta of Ident.t
  | Arrow of typ * typ
  | Data of Path.t * typ list
  | PromotedCtor of Path.t * Path.t * typ list

(* Constructor *)
type ctor =
  { name : Path.t
  ; quantified : (Ident.t * typ) list
  ; existential : (Ident.t * typ) list
  ; argument_types : typ list
  ; result : typ
  }

(* Declaration *)
type dec =
  { name : Path.t
  ; param_kinds : typ list
  ; ctors : ctor list
  }

(* Promoted constructor info *)
type promoted_ctor_info =
  { quantified : (Ident.t * typ) list
  ; arg_kinds : typ list
  ; result_kind : typ
  }

(* Kind environment *)
type kind_env =
  { decs : dec Path.tbl
  ; data_kinds : typ Path.tbl
  ; promoted_ctors : promoted_ctor_info Path.tbl
  }

(* Kind errors *)
type kind_error =
  | Unbound_type_variable of Ident.t
  | Unbound_meta_variable of Ident.t
  | Unknown_data_type of Path.t
  | Unknown_promoted_ctor of Path.t * Path.t
  | Not_a_promoted_type of Path.t
  | Invalid_kind of typ
  | Kind_mismatch of { expected: typ; actual: typ; in_type: typ }
  | Arity_mismatch of { kind: typ; num_args: int }
  | Arrow_domain_not_typ of typ
  | Arrow_codomain_not_typ of typ
  | Too_many_arguments of { kind: typ; extra_args: typ list }

(* Wrapper for Ident.find_opt returning result *)
let ident_find (v: Ident.t) (tbl: 'a Ident.tbl) (err: kind_error) : ('a, kind_error) result =
  match Ident.find_opt v tbl with
  | Some x -> Ok x
  | None -> Error err

(* Wrapper for Path.find_opt returning result *)
let path_find (p: Path.t) (tbl: 'a Path.tbl) (err: kind_error) : ('a, kind_error) result =
  match Path.find_opt p tbl with
  | Some x -> Ok x
  | None -> Error err

(* Substitution *)
type subst = typ Ident.tbl

let rec apply_subst subst t =
  match t with
    TMeta v ->
      (match Ident.find_opt v subst with
        Some t' -> apply_subst subst t'
      | None -> t)
  | TVar _ -> t
  | Arrow (t1, t2) -> Arrow (apply_subst subst t1, apply_subst subst t2)
  | Data (name, args) -> Data (name, List.map (apply_subst subst) args)
  | PromotedCtor (data_name, ctor_name, args) ->
      PromotedCtor (data_name, ctor_name, List.map (apply_subst subst) args)
  | _ -> t

let rec occurs v t =
  match t with
    TVar v' -> Ident.equal v v'
  | TMeta v' -> Ident.equal v v'
  | Arrow (t1, t2) -> occurs v t1 || occurs v t2
  | Data (_, args) -> List.exists (occurs v) args
  | PromotedCtor (_, _, args) -> List.exists (occurs v) args
  | _ -> false

let rec unify t1 t2 subst =
  let rec fold_zip acc = function
    | [], [] -> acc
    | x :: xs, y :: ys ->
        Option.bind acc (fun subst' -> fold_zip (unify x y subst') (xs, ys))
    | _ -> None
  in
  let t1 = apply_subst subst t1 in
  let t2 = apply_subst subst t2 in
  match t1, t2 with
  | TVar v1, TVar v2 when Ident.equal v1 v2 -> Some subst
  | TVar _, _ | _, TVar _ -> None
  | TMeta v1, TMeta v2 when Ident.equal v1 v2 -> Some subst
  | TMeta v, t | t, TMeta v -> if occurs v t then None else Some (Ident.add v t subst)
  | Arrow (a1, b1), Arrow (a2, b2) -> Option.bind (unify a1 a2 subst) (unify b1 b2)
  | Int, Int -> Some subst
  | Typ, Typ -> Some subst
  | Data (name1, args1), Data (name2, args2) when
        Path.equal name1 name2 && List.length args1 = List.length args2 ->
      fold_zip (Some subst) (args1, args2)
  | PromotedCtor (d1, c1, args1), PromotedCtor (d2, c2, args2) when
        Path.equal d1 d2 && Path.equal c1 c2 &&
        List.length args1 = List.length args2 ->
      fold_zip (Some subst) (args1, args2)
  | _ -> None

let equiv subst t1 t2 =
  match unify t1 t2 subst with Some _ -> true | None -> false

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

let rec apply_fresh_subst subst t =
  match t with
  | TVar v -> (match Ident.find_opt v subst with Some t' -> t' | None -> t)
  | TMeta v -> (match Ident.find_opt v subst with Some t' -> t' | None -> t)
  | Arrow (t1, t2) -> Arrow (apply_fresh_subst subst t1, apply_fresh_subst subst t2)
  | Data (name, args) -> Data (name, List.map (apply_fresh_subst subst) args)
  | PromotedCtor (d, c, args) -> PromotedCtor (d, c, List.map (apply_fresh_subst subst) args)
  | _ -> t

(* A constructor is promotable (can be lifted to the type/kind level) if:
  1. It has no existential variables
  2. Its result type is the canonical form: Data(typeName, [TVar q1, TVar q2, ...])
    where the variables are exactly the quantified variables, in order. *)
let is_promotable type_name (ctor: ctor) : bool =
  let no_existentials = (ctor.existential = []) in
  let canonical_result =
    match ctor.result with
    | Data (name, args) when Path.equal name type_name ->
        List.length args = List.length ctor.quantified &&
        List.for_all2 (fun arg (qvar, _) ->
          match arg with
          | TVar v -> Ident.equal v qvar
          | _ -> false
        ) args ctor.quantified
    | _ -> false
  in
  no_existentials && canonical_result

(* Check if a declaration can serve as a DataKind (all constructors are promotable) *)
let is_dec_promotable (dec: dec) : bool =
  List.for_all (is_promotable dec.name) dec.ctors

(* Helper to sequence result checks over a list *)
let rec check_all f = function
  | [] -> Ok ()
  | x :: xs ->
      let* () = f x in
      check_all f xs

(* Helper to sequence result checks over two lists *)
let rec check_all2 f xs ys =
  match xs, ys with
  | [], [] -> Ok ()
  | x :: xs', y :: ys' -> let* _ = f x y in check_all2 f xs' ys'
  | _ -> Error (Arity_mismatch { kind = Typ; num_args = 0 })

(* Check if a type is a valid kind (can classify types) *)
let rec valid_kind (env: kind_env) (ctx: typ Ident.tbl) (t: typ) : (unit, kind_error) result =
  match t with
  | Typ -> Ok ()
  | Arrow (k1, k2) ->
      let* _ = valid_kind env ctx k1 in
      valid_kind env ctx k2
  | Data (name, args) ->
      let* kind = path_find name env.data_kinds (Not_a_promoted_type name) in
      let* _ = check_all (valid_kind env ctx) args in
      let rec arity k = match k with Arrow (_, r) -> 1 + arity r | _ -> 0 in
      (match kind, args with
      | Typ, [] -> Ok ()
      | Arrow _, _ when List.length args <= arity kind -> Ok ()
      | _, [] -> Ok ()
      | _, _ -> Error (Arity_mismatch { kind; num_args = List.length args }))
  | TVar v ->
      let* k = ident_find v ctx (Unbound_type_variable v) in
      valid_kind env ctx k
  | TMeta v ->
      let* k = ident_find v ctx (Unbound_meta_variable v) in
      valid_kind env ctx k
  | _ -> Error (Invalid_kind t)

(* Infer the kind of a type *)
let rec infer_kind (env: kind_env) (subst: subst) (ctx: typ Ident.tbl) (t: typ) : (typ, kind_error) result =
  match t with
  | Int -> Ok Typ
  | TVar v -> ident_find v ctx (Unbound_type_variable v)
  | TMeta v ->
      (match Ident.find_opt v subst with
      | Some t' -> infer_kind env subst ctx t'
      | None -> ident_find v ctx (Unbound_meta_variable v))
  | Arrow (t1, t2) ->
      let* k1 = infer_kind env subst ctx t1 in
      let* k2 = infer_kind env subst ctx t2 in
      if equiv subst k1 Typ then
        if equiv subst k2 Typ then Ok Typ
        else Error (Arrow_codomain_not_typ t2)
      else Error (Arrow_domain_not_typ t1)
  | Data (name, args) ->
      let* dec = path_find name env.decs (Unknown_data_type name) in
      let full_kind = List.fold_right (fun k acc -> Arrow (k, acc)) dec.param_kinds Typ in
      apply_args env subst ctx full_kind args
  | PromotedCtor (data_name, ctor_name, args) ->
      let key = Path.access data_name (Path.name ctor_name) in
      let* info = path_find key env.promoted_ctors (Unknown_promoted_ctor (data_name, ctor_name)) in
      let num_quantified = List.length info.quantified in
      let num_kind_args = List.length info.arg_kinds in
      let expected_args = num_quantified + num_kind_args in
      if List.length args <> expected_args then
        Error (Arity_mismatch { kind = info.result_kind; num_args = List.length args })
      else
        let type_args = List.filteri (fun i _ -> i < num_quantified) args in
        let kind_args = List.filteri (fun i _ -> i >= num_quantified) args in
        let ty_subst =
          List.fold_left2 (fun s (v, _) t -> Ident.add v t s)
            Ident.emptytbl info.quantified type_args
        in
        let* _ = check_all2 (fun (_, expected_kind) arg ->
          let expected_kind' = apply_fresh_subst ty_subst expected_kind in
          check_kind env subst ctx arg expected_kind'
        ) info.quantified type_args in
        let subst_arg_kinds = List.map (apply_fresh_subst ty_subst) info.arg_kinds in
        let* _ = check_all2 (fun expected_kind arg ->
          check_kind env subst ctx arg expected_kind
        ) subst_arg_kinds kind_args in
        let subst_result = apply_fresh_subst ty_subst info.result_kind in
        Ok subst_result
  | Typ -> Ok Typ

(* Apply type arguments to a kind, returning the resulting kind *)
and apply_args (env: kind_env) (subst: subst) (ctx: typ Ident.tbl) (kind: typ) (args: typ list) : (typ, kind_error) result =
  match kind, args with
  | k, [] -> Ok k
  | Arrow (param_kind, result_kind), arg :: rest ->
      let* _ = check_kind env subst ctx arg param_kind in
      apply_args env subst ctx result_kind rest
  | _, extra_args -> Error (Too_many_arguments { kind; extra_args })

(* Check that a type has the expected kind *)
and check_kind (env: kind_env) (subst: subst) (ctx: typ Ident.tbl) (t: typ) (expected_kind: typ) : (unit, kind_error) result =
  let* inferred_kind = infer_kind env subst ctx t in
  if equiv subst inferred_kind expected_kind then Ok ()
  else Error (Kind_mismatch { expected = expected_kind; actual = inferred_kind; in_type = t })

(* Context *)
type context =
  { subst : subst
  ; kind_env : kind_env
  ; typ_vars : typ Ident.tbl
  ; term_vars : typ Ident.tbl
  }

(* Check that a constructor is well-kinded *)
let check_ctor_well_kinded (env: kind_env) (ctor: ctor) : bool =
  let ty_ctx =
    List.fold_left (fun acc (v, k) -> Ident.add v k acc)
      Ident.emptytbl (ctor.quantified @ ctor.existential)
  in
  let kinds_valid =
    List.for_all (fun (_, k) -> Result.is_ok (valid_kind env ty_ctx k)) (ctor.quantified @ ctor.existential)
  in
  let args_valid =
    List.for_all (fun t ->
      Result.is_ok (check_kind env Ident.emptytbl ty_ctx t Typ)
    ) ctor.argument_types
  in
  let result_valid =
    Result.is_ok (check_kind env Ident.emptytbl ty_ctx ctor.result Typ)
  in
  kinds_valid && args_valid && result_valid

(* Check that a declaration is well-kinded *)
let check_dec_well_kinded (env: kind_env) (dec: dec) : bool =
  let param_kinds_valid =
    List.for_all (fun k -> Result.is_ok (valid_kind env Ident.emptytbl k)) dec.param_kinds in
  let ctors_valid =
    List.for_all (check_ctor_well_kinded env) dec.ctors in
  param_kinds_valid && ctors_valid

(* Create an empty kind environment *)
let empty_kind_env : kind_env =
  { decs = Path.emptytbl
  ; data_kinds = Path.emptytbl
  ; promoted_ctors = Path.emptytbl
  }

(* Create an empty context *)
let empty_context : context =
  { subst = Ident.emptytbl
  ; kind_env = empty_kind_env
  ; typ_vars = Ident.emptytbl
  ; term_vars = Ident.emptytbl
  }

(* Build PromotedCtorInfo for a promotable constructor *)
let build_promoted_ctor_info (ctor: ctor) : promoted_ctor_info =
  { quantified = ctor.quantified
  ; arg_kinds = ctor.argument_types
  ; result_kind = ctor.result
  }

(* Build promoted constructor entries for a declaration (only if all ctors are promotable) *)
let build_promoted_ctors (d: dec) : (Path.t * promoted_ctor_info) list =
  if is_dec_promotable d then
    List.map (fun (c: ctor) ->
      (Path.access d.name (Path.name c.name), build_promoted_ctor_info c)
    ) d.ctors
  else
    []

(* Compute the kind of a data type from its param_kinds *)
let data_kind_from_param_kinds (param_kinds: typ list) : typ =
  List.fold_right (fun k acc -> Arrow (k, acc)) param_kinds Typ

(* Add a declaration to the kind environment *)
let add_dec_to_kind_env (env: kind_env) (dec: dec) : kind_env =
  let new_decs = Path.add dec.name dec env.decs in
  let is_prom = is_dec_promotable dec in
  let new_data_kinds =
    if is_prom then
      let kind = data_kind_from_param_kinds dec.param_kinds in
      Path.add dec.name kind env.data_kinds
    else env.data_kinds
  in
  let new_promoted_ctors =
    List.fold_left (fun acc (k, v) -> Path.add k v acc)
      env.promoted_ctors (build_promoted_ctors dec)
  in
  { decs = new_decs; data_kinds = new_data_kinds; promoted_ctors = new_promoted_ctors }

(* Add a declaration to the context, checking well-kindedness and promoting if possible *)
let add_declaration (ctx: context) (dec: dec) : context option =
  let temp_env = { ctx.kind_env with decs = Path.add dec.name dec ctx.kind_env.decs } in
  if not (check_dec_well_kinded temp_env dec) then None
  else
    let new_kind_env = add_dec_to_kind_env ctx.kind_env dec in
    Some { ctx with kind_env = new_kind_env }

(* Add multiple declarations in sequence *)
let add_declarations (ctx: context) (decs: dec list) : context option =
  List.fold_left (fun ctx_opt dec ->
    match ctx_opt with
    | None -> None
    | Some ctx -> add_declaration ctx dec
  ) (Some ctx) decs

(* Add mutually recursive declarations *)
let add_declarations_recursive (ctx: context) (decs: dec list) : context option =
  let temp_env = List.fold_left add_dec_to_kind_env ctx.kind_env decs in
  let all_valid = List.for_all (check_dec_well_kinded temp_env) decs in
  if not all_valid then None
  else Some { ctx with kind_env = temp_env }

(* Check if a constructor is reachable given scrutinee type arguments *)
let is_ctor_reachable (ctx: context) (dec: dec) (ctor: ctor) (scrutinee_args: typ list) : subst option =
  let _, fresh_subst = freshen_meta ctor.quantified in
  let fresh_result = apply_fresh_subst fresh_subst ctor.result in
  let scrutinee_type = Data (dec.name, scrutinee_args) in
  unify fresh_result scrutinee_type ctx.subst

(* Check exhaustivity: all reachable constructors must be covered *)
let check_exhaustive (ctx: context) (d: dec) (scrutinee_args: typ list) (covered_ctors: Path.t list) : Path.t list =
  List.filter_map (fun (c: ctor) ->
    if not (List.exists (Path.equal c.name) covered_ctors) &&
       Option.is_some (is_ctor_reachable ctx d c scrutinee_args)
    then Some c.name
    else None
  ) d.ctors