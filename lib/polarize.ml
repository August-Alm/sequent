(**
  Module: Polarize
  Description: Translates Lang to the positive fragment of Kore.
*)

module LTy = Lang.Types
module LTm = Lang.Terms
module Sym = Kore.Builtins.Sym
module Ext = Kore.Builtins.Ext
module Prim = Kore.Builtins.Prim
open Kore.Types
open Kore.Terms
open Common.Identifiers

(* All Lang types should be mapped to the positive fragment of Kore *)
let rec map_kinds (k: LTy.kind) =
  match k with
  | LTy.KStar -> Pos
  | LTy.KArrow (k1, k2) -> Arrow (map_kinds k1, map_kinds k2)

(* Shifts from negative to positive polarity *)
let mk_pos tt = TyApp (Prim.pos_t, tt)
(* Shifts from positive to negative polarity *)
let mk_neg tt = TyApp (Prim.neg_t, tt)

(* Helper *)
let rec go expand tt =
  match tt with
  | LTy.TySym s -> TySym s
  | LTy.TyVar x -> TyVar x
  | LTy.TyApp (t1, t2) -> TyApp (go expand t1, go expand t2)
  | LTy.TyFun (t1, t2) ->
    (*
      code (X:+) → (Y:−) where
        ·: X | X → Y ⊢ Y   --- apply(prd X, cns Y)
    *)
    if expand then
      mk_pos (TyApp (TyApp (Prim.fun_t, go expand t1), mk_neg (go expand t2)))
    else (* Use symbol reference instead *)
      mk_pos (TyApp (TyApp (TySym Sym.fun_t, go expand t1), mk_neg (go expand t2)))
  | LTy.TyAll ((a, k), t) ->
    (*
      code ∀(F: k → -) where
        ·{}: | ∀F ⊢{X} F(X)   --- insta{X}(cns F(X))
    *)
    let k = map_kinds k in
    if expand then
      mk_pos (TyApp (Prim.all_t a k, mk_neg (go expand t)))
    else (* Use symbol reference instead *)
      mk_pos (TyApp (TySym (Sym.all_t k), mk_neg (go expand t)))
  | LTy.TyDef (Data dec) -> TyPos (go_dec true dec)
  | LTy.TyDef (Code dec) -> mk_pos (TyNeg (go_dec false dec))
  (* Box primitive types *)
  | LTy.TyPrim Int -> TyApp (Prim.box_t, Ext.int_t)

and go_dec is_data (dec: LTy.ty_dec) =
  { name = dec.LTy.symbol
  ; arguments =
      List.map (fun (x_opt, k) ->
        (Option.map (go false) x_opt, map_kinds k)
      ) dec.LTy.arguments
  ; xtors =
      List.map (fun (xtor: LTy.ty_xtor) ->
        { parent = xtor.LTy.parent
        ; name = xtor.LTy.symbol
        ; quantified =
            List.map (fun (x, k) -> (x, map_kinds k)
            ) xtor.LTy.quantified
        ; parameters =
            (if is_data then
              List.map (fun t -> Lhs (go false t)
              ) xtor.LTy.sources
            else
              (* Last source is the consumed codomain *)
              let ps, c =
                Utility.split_at_last xtor.LTy.sources
              in
              List.map (fun t -> Lhs (go false t)) ps
              @ [Rhs (go false c)])
        ; parent_arguments =
            List.map (fun t -> go false t) xtor.LTy.arguments
        ; constraints =
            Option.map (List.map (fun (x, t) -> (x, go false t)
            )) xtor.LTy.constraints
        }
      ) dec.LTy.xtors
  }
  
(** Maps a data type to a signature *)
let map_data = go_dec true

(** Maps a codata type to a signature *)
let map_code = go_dec false

(** Maps Lang types to positive Kore types *)
let map_type (tt: LTy.typ) =
  go false tt

module KindSet = Set.Make(struct
  type t = variable * kind
  let compare (_, k1) (_, k2) = Sym.compare_kinds k1 k2
end)

let rec alls_from_trm (ks: KindSet.t) (trm: LTm.typed_term) =
  alls_from_typ ks (LTm.get_type trm)

and alls_from_typ (ks: KindSet.t) (tt: LTy.typ) =
  match tt with
  | LTy.TySym _ -> ks
  | LTy.TyVar _ -> ks
  | LTy.TyApp (t1, t2) -> alls_from_typ (alls_from_typ ks t1) t2
  | LTy.TyFun (t1, t2) -> alls_from_typ (alls_from_typ ks t1) t2
  | LTy.TyAll ((a, k), t) -> alls_from_typ (KindSet.add (a, map_kinds k) ks) t
  | LTy.TyDef (Data dec) | LTy.TyDef (Code dec) -> alls_from_dec ks dec
  | LTy.TyPrim _ -> ks

and alls_from_dec (ks: KindSet.t) (dec: LTy.ty_dec) =
  let ks = List.fold_left (fun ks (t_opt, _) ->
    match t_opt with
    | None -> ks
    | Some t -> alls_from_typ ks t
  ) ks dec.LTy.arguments
  in
  List.fold_left alls_from_xtor ks dec.LTy.xtors

and alls_from_xtor (ks: KindSet.t) (xtor: LTy.ty_xtor) =
  let ks = List.fold_left alls_from_typ ks xtor.LTy.sources in
  let ks = List.fold_left alls_from_typ ks xtor.LTy.arguments in
  match xtor.LTy.constraints with
  | None -> ks
  | Some cs ->
    List.fold_left (fun ks (_, t) ->
      alls_from_typ ks t
    ) ks cs
  
let alls_from_typed_term_def (ks: KindSet.t) (def: LTm.typed_term_def) =
  let ks = List.fold_left (fun ks (_, t) ->
    alls_from_typ ks t
  ) ks def.LTm.term_args in
  let ks = alls_from_typ ks def.LTm.return_type in
  alls_from_trm ks def.LTm.body

let alls_from_typed_defs (defs: LTm.typed_definitions) =
  let ks =
    List.fold_left (fun ks (_, d) ->
      alls_from_typed_term_def ks d
    ) KindSet.empty defs.LTm.term_defs
  in
  let ks =
    List.fold_left (fun ks (_, (dec, _)) ->
      match dec with
      | LTy.Data d -> alls_from_dec ks d
      | LTy.Code d -> alls_from_dec ks d
    ) ks defs.LTm.type_defs
  in
  KindSet.to_list ks

(** Extracts all the signatures, including primitive ones, and kind-checks
  them in the process. *)
let signatures (defs: LTm.typed_definitions) =
  let primitives =
    List.fold_left (fun sgns (a, k) ->
      add_def sgns Negative (Prim.all_sgn a k)
    ) Prim.signatures (alls_from_typed_defs defs)
  in
  List.fold_left (fun sgns (_, (dec, _)) ->
    match dec with
    | LTy.Data dec -> add_def sgns Positive (map_data dec)
    | LTy.Code dec -> add_def sgns Negative (map_code dec)
  ) primitives defs.LTm.type_defs

(* Helper: Count the number of function arrows in a type *)
let rec count_fun_arrows (ty: LTy.typ) : int =
  match ty with
  | LTy.TyAll (_, t2) -> count_fun_arrows t2  (* Skip type abstraction *)
  | LTy.TyFun (_, t2) -> 1 + count_fun_arrows t2
  | _ -> 0

(* Helper: Collect arguments from nested applications *)
let rec collect_args (tm: LTm.typed_term) : (LTm.typed_term * LTm.typed_term list) =
  match tm with
  | LTm.TyTmApp (t, u, _) ->
    let (head, args) = collect_args t in
    (head, args @ [u])
  | _ -> (tm, [])

(* Helper: Collect both type arguments and term arguments from
  nested applications and instantiations *)
let rec collect_type_and_term_args (tm: LTm.typed_term) 
    : (LTm.typed_term * LTy.typ list * LTm.typed_term list) =
  match tm with
  | LTm.TyTmApp (t, u, _) ->
    let (head, ty_args, tm_args) = collect_type_and_term_args t in
    (head, ty_args, tm_args @ [u])
  | LTm.TyTmIns (t, ty_arg, _, _) ->
    let (head, ty_args, tm_args) = collect_type_and_term_args t in
    (head, ty_args @ [ty_arg], tm_args)
  | _ -> (tm, [], [])

(* Helper: Get function argument types from a function type *)
let rec get_arg_types (ty: LTy.typ) : LTy.typ list =
  match ty with
  | LTy.TyFun (t1, t2) -> t1 :: get_arg_types t2
  | _ -> []

(* Helper: Get return type from a function type *)
let rec get_return_type (ty: LTy.typ) : LTy.typ =
  match ty with
  | LTy.TyFun (_, t2) -> get_return_type t2
  | _ -> ty

 (** Translates Lang terms to Kore producers (LHS terms) *)
let rec map_term (sgns: signatures) (trm: LTm.typed_term) : Kore.Terms.term =
  match trm with
  | LTm.TyTmVar (x, _) -> Variable x
  | LTm.TyTmSym (s, ty) ->
    let alpha = Ident.fresh () in
    MuLhsPos (map_type ty, alpha, Call (s, [], [Variable alpha]))
  | LTm.TyTmApp (t, u, ty_ret) ->
    (* Collect all type and term arguments from nested applications and instantiations *)
    let (head, ty_args, tm_args) =
      collect_type_and_term_args (LTm.TyTmApp (t, u, ty_ret))
    in
    (match head with
    | LTm.TyTmSym (sym, sym_ty) ->
      (* This is an application of a top-level symbol *)
      let required_arity = count_fun_arrows sym_ty in
      let provided_arity = List.length tm_args in
      
      if provided_arity = required_arity then
        (* Fully applied - generate Call statement with type arguments *)
        let alpha = Ident.fresh () in
        let ty = map_type sym_ty in
        let tys = List.map map_type ty_args in
        let args = List.map (map_term sgns) tm_args in
        MuLhsPos (ty, alpha, Call (sym, tys, args @ [Variable alpha]))
      
      else if provided_arity < required_arity then
        (* Partially applied - generate lambda for remaining arguments *)
        (* foo(u) where foo: a -> b -> c becomes:
           fun (y: b) => foo(u, y) 
           which is: new { $app(this, y, α) => μβ.Call(foo, [u, y], [β]) | α } *)
        let arg_types = get_arg_types sym_ty in
        let remaining_arg_types = Utility.drop provided_arity arg_types in
        let final_return_ty = get_return_type sym_ty in  (* The final return type, not the partial app type *)
        
        (* Generate nested lambdas for each remaining argument *)
        let rec make_lambdas remaining_tys provided_args =
          match remaining_tys with
          | [] -> 
            (* All arguments provided - make the call with collected type args *)
            let alpha = Ident.fresh () in
            let ty = map_type sym_ty in
            let tys = List.map map_type ty_args in
            let args = List.map (map_term sgns) provided_args in
            MuLhsPos (ty, alpha, Call (sym, tys, args @ [Variable alpha]))
          | arg_ty :: rest_tys ->
            (* Create lambda for this argument *)
            let x = Ident.fresh () in
            let y = Ident.fresh () in
            let ta = Ident.fresh () in
            let tb = Ident.fresh () in
            (* The result type after applying this and all remaining arguments *)
            let result_ty = 
              if rest_tys = [] then map_type final_return_ty
              else List.fold_right (fun arg_ty acc -> 
                TyApp (TyApp (Prim.fun_t, map_type arg_ty), acc)
              ) rest_tys (map_type final_return_ty)
            in
            let result_sng =
              match result_ty with
              | 
            New (result_ty, [{
              CTm.xtor = CTy.Prim.app_dtor_sym;
              CTm.type_vars = [ta; tb];
              CTm.variables = [x];
              CTm.covariables = [y];
              CTm.statement = CTm.Cut (
                make_lambdas rest_tys (provided_args @ [LTm.TyTmVar (x, arg_ty)]),
                result_ty,
                CTm.Covar y
              )
            }]
        in
        make_lambdas remaining_arg_types tm_args
      
      else
        (* Over-applied - this shouldn't happen in well-typed code *)
        failwith "convert: over-applied function (type checking should have caught this)"
    | _ ->
      (* General application using $app destructor *)
      let ty_arg = LTm.get_type u in
      let x = Ident.fresh () in
      (* μx.< conv t | $apply{ty_arg}{ty_ret}(x, conv u) > *)
      CTm.Mu (x, CTm.Cut (
        convert t,
        (* Function type: ty_arg -> ty_ret *)
        CTy.TyApp (CTy.TyApp (CTy.TyDef (CTy.Prim (CTy.Prim.fun_sym,
          CTy.KArrow (CTy.KStar, CTy.KArrow (CTy.KStar, CTy.KStar)))),
            convert_typ ty_arg), convert_typ ty_ret),
        CTm.Destructor (CTy.Prim.app_dtor_sym, (
          [convert_typ ty_arg; convert_typ ty_ret],
          [CTm.Var x],
          [CTm.MuTilde (x, CTm.Cut (convert u, convert_typ ty_arg, CTm.Covar x))]
        ))
      ))
    )

  | LTm.TyTmIns (t, ty_arg, k, ty_result) ->
    (* Type instantiation: check if this is part of a function call pattern *)
    (* If t is a symbol or becomes a symbol after collecting args, handle as Call *)
    let (head, all_ty_args, all_tm_args) = collect_type_and_term_args (LTm.TyTmIns (t, ty_arg, k, ty_result)) in
    (match head with
    | LTm.TyTmSym (_, _) when all_ty_args <> [] && all_tm_args = [] ->
      (* Just type instantiation, no term args yet *)
      let x = Ident.fresh () in
      CTm.Mu (x, CTm.Cut (
        convert t,
        CTy.TyApp (CTy.TyDef (CTy.Prim (CTy.Prim.all_sym k, CTy.KArrow (CTy.KArrow (k, CTy.KStar), CTy.KStar))), convert_typ ty_result),
        CTm.Destructor (CTy.Prim.ins_dtor_sym k, (
          [convert_typ ty_result; convert_typ ty_arg],
          [],
          [CTm.Covar x]
        ))
      ))
    | _ ->
      (* Use old forall encoding *)
      let x = Ident.fresh () in
      CTm.Mu (x, CTm.Cut (
        convert t,
        CTy.TyApp (CTy.TyDef (CTy.Prim (CTy.Prim.all_sym k, CTy.KArrow (CTy.KArrow (k, CTy.KStar), CTy.KStar))), convert_typ ty_result),
        CTm.Destructor (CTy.Prim.ins_dtor_sym k, (
          [convert_typ ty_result; convert_typ ty_arg],
          [],
          [CTm.Covar x]
        ))
      ))
    )

  | LTm.TyTmLam (x, _a, body, _ty) ->
    let b = LTm.get_type body in
    let y = Ident.fresh () in
    let ta = Ident.fresh () in
    let tb = Ident.fresh () in
    (* new $fun{a}{b} { $apply{a}{b}(this, x, y) => < conv body | y > } *)
    CTm.Cocase [{
      CTm.xtor = CTy.Prim.app_dtor_sym;
      CTm.type_vars = [ta; tb];
      CTm.variables = [x];
      CTm.covariables = [y];
      CTm.statement = CTm.Cut (convert body, convert_typ b, CTm.Covar y)
    }]

  | LTm.TyTmAll ((a, k), body, _ty) ->
    let b = LTm.get_type body in
    let y = Ident.fresh () in
    (* new $forall{k} { $inst{a: k}(y) => < conv body | y > } *)
    CTm.Cocase [{
      CTm.xtor = CTy.Prim.ins_dtor_sym k;
      CTm.type_vars = [a];
      CTm.variables = [];
      CTm.covariables = [y];
      CTm.statement = CTm.Cut (convert body, convert_typ b, CTm.Covar y)
    }]

  | LTm.TyTmLet (x, t, u, ty) ->
    let t_ty = LTm.get_type t in
    let y = Ident.fresh () in
    (* μy.< conv t | μ̃x.< conv u | y > > *)
    CTm.Mu (y, CTm.Cut (
      convert t,
      convert_typ t_ty,
      CTm.MuTilde (x, CTm.Cut (convert u, convert_typ ty, CTm.Covar y))
    ))

  | LTm.TyTmMatch (t, clauses, ty) ->
    let t_ty = LTm.get_type t in
    let y = Ident.fresh () in
    (* μy.< conv t | case { ctor_i{type_vars}(term_vars) => < conv body_i | y > } > *)
    let patterns = List.map (fun (xtor, type_vars, term_vars, body) ->
      { CTm.xtor = xtor.LTy.symbol
      ; CTm.type_vars = type_vars
      ; CTm.variables = term_vars
      ; CTm.covariables = []  (* Case patterns don't have covariables *)
      ; CTm.statement = CTm.Cut (convert body, convert_typ ty, CTm.Covar y)
      }
    ) clauses in
    CTm.Mu (y, CTm.Cut (
      convert t,
      convert_typ t_ty,
      CTm.Case patterns
    ))

  | LTm.TyTmNew (_ty_opt, clauses, _ty) ->
    (* In Lang: new stream(a) { head{_} => x ; tail{_} => const_stream(x) }
       In Core: cocase { head{a}(k) => <x | k> ; tail{a}(k) => <...| k> }
       
       Note: In Lang, self is implicit (not in pattern bindings).
       In Core, cocase patterns have NO producer variables (no self).
       They only have consumer variables for the return continuation.
       Self appears in destructor APPLICATIONS, not in cocase pattern definitions.
       
       Extract type arguments from the result type to use as type variables in patterns.
       For `new stream(a)`, the type is `TyApp(TyCtor(stream), TyVar(a))`, so we extract `[a]`.
    *)
    let rec extract_type_vars (ty: LTy.typ) : Ident.t list =
      match ty with
      | LTy.TyVar x -> [x]
      | LTy.TyApp (t1, t2) -> extract_type_vars t1 @ extract_type_vars t2
      | _ -> []
    in
    let type_vars_from_result = extract_type_vars _ty in
    
    let patterns = List.map (fun (xtor, _lang_type_vars, term_vars, body) ->
      let body_ty = LTm.get_type body in
      let y = Ident.fresh () in
      { CTm.xtor = xtor.LTy.symbol
      ; CTm.type_vars = type_vars_from_result  (* Use type vars from result type, not Lang pattern *)
      ; CTm.variables = term_vars  (* Just the non-return arguments (empty for head/tail) *)
      ; CTm.covariables = [y]
      ; CTm.statement = CTm.Cut (convert body, convert_typ body_ty, CTm.Covar y)
      }
    ) clauses in
    CTm.Cocase patterns

  | LTm.TyTmCtor (ctor, ty_args, tm_args, _ty) ->
    (* ctor{(Convert.typ ty_args)}((conv tm_args), []) *)
    CTm.Constructor (ctor.LTy.symbol, (
      List.map convert_typ ty_args,
      List.map convert tm_args,
      []
    ))

  | LTm.TyTmDtor (dtor, ty_args, tm_args, _ty) ->
    (* The first tm_arg should be 'self' *)
    (match tm_args with
    | [] -> failwith "convert: destructor must have at least 'self' argument"
    | self :: rest ->
      let self_ty = LTm.get_type self in
      let y = Ident.fresh () in
      (* μy.< conv self | dtor{(Convert.typ ty_args)}((conv rest), y) > *)
      CTm.Mu (y, CTm.Cut (
        convert self,
        convert_typ self_ty,
        CTm.Destructor (dtor.LTy.symbol, (
          List.map convert_typ ty_args,
          List.map convert rest,
          [CTm.Covar y]
        ))
      ))
    )
  | _ -> failwith "map_term: not implemented yet"