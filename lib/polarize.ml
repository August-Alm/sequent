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

(* Instantiate close xtor for a given inner negative type *)
let mk_close_xtor inner_ty =
  { Prim.pos_close with
    parameters = [Lhs inner_ty]
  ; parent_arguments = [inner_ty]
  }

(* Instantiate thunk xtor for a given result type *)
let mk_thunk_xtor ret_ty =
  { Prim.neg_thunk with
    parameters = [Rhs ret_ty]
  ; parent_arguments = [ret_ty]
  }

(* Instantiate box xtor for ext int *)
let mk_box_xtor () =
  { Prim.box_mk with
    parameters = [Lhs Ext.int_t]
  ; parent_arguments = [Ext.int_t]
  }

(* The type Box(ext int) *)
let box_int_ty = TyApp (Prim.box_t, Ext.int_t)

(* Build: cocase {thunk(k') ⇒ ⟨body | k'⟩} : prd ↓[ret_ty] *)
let mk_thunk_cocase ret_ty body =
  let k' = Ident.fresh () in
  New (Prim.neg_sgn, [{
    xtor = mk_thunk_xtor ret_ty
  ; type_vars = []
  ; term_vars = [k']
  ; command = CutPos (ret_ty, body, Variable k')
  }])

(* Build: close(inner) where inner : prd inner_ty *)
let mk_close inner_ty inner =
  Constructor (mk_close_xtor inner_ty, [inner_ty], [inner])

(* Build: thunk(k) : cns ↓[ret_ty] *)
let mk_thunk ret_ty k =
  Destructor (mk_thunk_xtor ret_ty, [ret_ty], [Variable k])

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
  them in the process. Uses two-phase approach for mutually recursive types:
  1. Add all signatures without validating xtor contents
  2. Validate all xtors after all signatures are available *)
let signatures (defs: LTm.typed_definitions) =
  (* Phase 1: Add all signatures without validating xtors *)
  let primitives =
    List.fold_left (fun sgns (a, k) ->
      add_def_unchecked sgns Negative (Prim.all_sgn a k)
    ) Prim.signatures (alls_from_typed_defs defs)
  in
  let user_sigs =
    List.map (fun (_, (dec, _)) ->
      match dec with
      | LTy.Data dec -> (Positive, map_data dec)
      | LTy.Code dec -> (Negative, map_code dec)
    ) defs.LTm.type_defs
  in
  let sgns = List.fold_left (fun sgns (pol, sgn) ->
    add_def_unchecked sgns pol sgn
  ) primitives user_sigs
  in
  (* Phase 2: Validate all user-defined signatures *)
  List.iter (fun (_, sgn) ->
    validate_signature sgns sgn
  ) user_sigs;
  sgns

(* Helper: Decompose a function type into arg types and return type *)
let rec decompose_fun_type (ty: LTy.typ) : LTy.typ list * LTy.typ =
  match ty with
  | LTy.TyAll (_, t2) -> decompose_fun_type t2  (* Skip type abstraction *)
  | LTy.TyFun (t1, t2) ->
    let (args, ret) = decompose_fun_type t2 in
    (t1 :: args, ret)
  | _ -> ([], ty)

let count_fun_arrows ty = List.length (fst (decompose_fun_type ty))
let get_arg_types ty = fst (decompose_fun_type ty)
let get_return_type ty = snd (decompose_fun_type ty)

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

(**
  Build a lambda term in the positive fragment:
    [fun (x: A) ⇒ t] =
      close(cocase {apply(x, k) ⇒ ⟨cocase {thunk(k') ⇒ ⟨[t] | k'⟩} | k⟩})
  
  Arguments:
    - arg_ty: the type A (already mapped to Kore)
    - ret_ty: the type B (already mapped to Kore)
    - x: the bound variable
    - body: the body term (already mapped to Kore)
*)
let build_lambda (arg_ty: tpe) (ret_ty: tpe) (x: variable) (body: term) =
  let k = Ident.fresh () in   (* k : cns ↓[B] *)
  let inner_fun_ty = TyApp (TyApp (Prim.fun_t, arg_ty), mk_neg ret_ty) in
  let apply_xtor = 
    { Prim.fun_apply with
      parameters = [Lhs arg_ty; Rhs (mk_neg ret_ty)]
    ; parent_arguments = [arg_ty; mk_neg ret_ty]
    }
  in
  (* cocase {apply(x, k) ⇒ ⟨cocase{thunk(k') ⇒ ⟨body|k'⟩} | k⟩} *)
  let middle_cocase =
    New (Prim.fun_sgn, [{
      xtor = apply_xtor
    ; type_vars = []
    ; term_vars = [x; k]
    ; command = CutNeg (mk_neg ret_ty, mk_thunk_cocase ret_ty body, Variable k)
    }])
  in
  mk_close inner_fun_ty middle_cocase

(**
  Build an application term in the positive fragment:
    [t u] = μ(k: cns [B]). ⟨[t] | case {close(f) ⇒ ⟨f | apply([u], thunk(k))⟩}⟩
  
  Arguments:
    - arg_ty: type of the argument u (already mapped)
    - ret_ty: type of the result (already mapped)
    - t_term: the function term (already mapped)
    - u_term: the argument term (already mapped)
*)
let build_app (arg_ty: tpe) (ret_ty: tpe) (t_term: term) (u_term: term) =
  let k = Ident.fresh () in
  let f = Ident.fresh () in
  let inner_fun_ty = TyApp (TyApp (Prim.fun_t, arg_ty), mk_neg ret_ty) in
  let apply_xtor =
    { Prim.fun_apply with
      parameters = [Lhs arg_ty; Rhs (mk_neg ret_ty)]
    ; parent_arguments = [arg_ty; mk_neg ret_ty]
    }
  in
  (* apply(u, thunk(k)) *)
  let apply_dtor =
    Destructor (apply_xtor, [arg_ty; mk_neg ret_ty], [u_term; mk_thunk ret_ty k])
  in
  (* case {close(f) ⇒ ⟨f | apply(u, thunk(k))⟩} *)
  let match_term =
    Match (Prim.pos_sgn, [{
      xtor = mk_close_xtor inner_fun_ty
    ; type_vars = []
    ; term_vars = [f]
    ; command = CutNeg (inner_fun_ty, Variable f, apply_dtor)
    }])
  in
  MuLhsPos (ret_ty, k, CutPos (mk_pos inner_fun_ty, t_term, match_term))

(**
  Build a type instantiation in the positive fragment:
    [t{A}] = μ(k: cns [B]). ⟨[t] | case {close(f) ⇒ ⟨f | insta{A}(thunk(k))⟩}⟩
*)
let build_inst (kind: kind) (ty_arg: tpe) (ret_ty: tpe) (t_term: term) =
  let a = Ident.fresh () in
  let k = Ident.fresh () in
  let f = Ident.fresh () in
  let inner_all_ty = TyApp (Prim.all_t a kind, mk_neg ret_ty) in
  (* insta{ty_arg}(thunk(k)) *)
  let insta_xtor = Prim.all_insta a kind in
  let insta_dtor = Destructor (insta_xtor, [ty_arg], [mk_thunk ret_ty k]) in
  (* case {close(f) ⇒ ⟨f | insta{A}(thunk(k))⟩} *)
  let match_term =
    Match (Prim.pos_sgn, [{
      xtor = mk_close_xtor inner_all_ty
    ; type_vars = []
    ; term_vars = [f]
    ; command = CutNeg (inner_all_ty, Variable f, insta_dtor)
    }])
  in
  MuLhsPos (ret_ty, k, CutPos (mk_pos inner_all_ty, t_term, match_term))

(**
  Build a type abstraction in the positive fragment:
    [{a:k} t] =
      close(cocase {insta{a}(k) ⇒ ⟨cocase {thunk(k') ⇒ ⟨〚t〛| k'⟩} | k⟩})
*)
let build_type_abs (a: variable) (kind: kind) (ret_ty: tpe) (body: term) =
  let k = Ident.fresh () in
  let inner_all_ty = TyApp (Prim.all_t a kind, mk_neg ret_ty) in
  let insta_xtor = Prim.all_insta a kind in
  (* cocase {insta{a}(k) ⇒ ⟨cocase{thunk(k')⇒⟨body|k'⟩} | k⟩} *)
  let middle_cocase =
    New (Prim.all_sgn a kind, [{
      xtor = insta_xtor
    ; type_vars = [(a, kind)]
    ; term_vars = [k]
    ; command = CutNeg (mk_neg ret_ty, mk_thunk_cocase ret_ty body, Variable k)
    }])
  in
  mk_close inner_all_ty middle_cocase

(** Translates Lang terms to Kore producers (LHS terms) *)
let rec map_term (sgns: signatures) (trm: LTm.typed_term) : term =
  match trm with
  | LTm.TyTmVar (x, _) -> Variable x

  | LTm.TyTmLam (x, arg_ty, body, _ty) ->
    (* fun (x: A) => t *)
    let ret_ty = LTm.get_type body in
    let arg_ty' = map_type arg_ty in
    let ret_ty' = map_type ret_ty in
    let body' = map_term sgns body in
    build_lambda arg_ty' ret_ty' x body'

  | LTm.TyTmAll ((a, k), body, _ty) ->
    (* {a: k} t *)
    let ret_ty = LTm.get_type body in
    let kind = map_kinds k in
    let ret_ty' = map_type ret_ty in
    let body' = map_term sgns body in
    build_type_abs a kind ret_ty' body'

  | LTm.TyTmApp (t, u, _ty_ret) ->
    (* Collect all type and term arguments *)
    let (head, ty_args, tm_args) =
      collect_type_and_term_args (LTm.TyTmApp (t, u, _ty_ret))
    in
    map_application sgns head ty_args tm_args

  | LTm.TyTmIns (t, ty_arg, k, _ty_result) ->
    (* Collect all type and term arguments *)
    let (head, ty_args, tm_args) =
      collect_type_and_term_args (LTm.TyTmIns (t, ty_arg, k, _ty_result))
    in
    map_application sgns head ty_args tm_args

  | LTm.TyTmSym (_s, _ty) ->
    (* A bare symbol reference - treat as partial application with 0 args *)
    map_application sgns trm [] []

  | LTm.TyTmLet (x, t, u, _ty) ->
    (* let x = t in u  →  μk. ⟨〚t〛| μ̃x. ⟨[u] | k⟩⟩ *)
    let t_ty = LTm.get_type t in
    let u_ty = LTm.get_type u in
    let k = Ident.fresh () in
    let t' = map_term sgns t in
    let u' = map_term sgns u in
    let t_ty' = map_type t_ty in
    let u_ty' = map_type u_ty in
    MuLhsPos (u_ty', k, 
      CutPos (t_ty', t', 
        MuRhsPos (t_ty', x, 
          CutPos (u_ty', u', Variable k))))

  | LTm.TyTmMatch (t, clauses, ty) ->
    (* match t with { C₁(xs) => e₁ ; ... }
       → μk. ⟨[t] | case {C₁(xs) => ⟨[e₁] | k⟩ ; ...}⟩ *)
    let t_ty = LTm.get_type t in
    let k = Ident.fresh () in
    let t' = map_term sgns t in
    let t_ty' = map_type t_ty in
    let ret_ty' = map_type ty in
    let t_sgn = get_signature_of_type sgns t_ty in
    let branches = List.map (fun (xtor, type_vars, term_vars, body) ->
      let body' = map_term sgns body in
      let xtor' = map_xtor sgns xtor in
      (* Get kinds from the xtor's quantified list *)
      let type_vars_with_kinds = 
        List.map2 (fun v (_, k) -> (v, map_kinds k)
        ) type_vars xtor.LTy.quantified
      in
      { xtor = xtor'
      ; type_vars = type_vars_with_kinds
      ; term_vars = term_vars
      ; command = CutPos (ret_ty', body', Variable k)
      }
    ) clauses in
    MuLhsPos (ret_ty', k, CutPos (t_ty', t', Match (t_sgn, branches)))

  | LTm.TyTmNew (_ty_opt, clauses, ty) ->
    (* new { D₁(args) => e₁ ; ... }
       → close(cocase {D₁(args, k) =>
          ⟨cocase{thunk(k') => ⟨[e₁] | k'⟩} | k⟩ ; ...}) *)
    let codata_sgn = get_signature_of_new_type sgns ty in
    let branches = List.map (fun (xtor, type_vars, term_vars, body) ->
      let body_ty = LTm.get_type body in
      let body' = map_term sgns body in
      let body_ty' = map_type body_ty in
      let k = Ident.fresh () in
      let xtor' = map_xtor sgns xtor in
      let type_vars_with_kinds =
        List.map2 (fun v (_, knd) -> (v, map_kinds knd)
        ) type_vars xtor.LTy.quantified
      in
      { xtor = xtor'
      ; type_vars = type_vars_with_kinds
      ; term_vars = term_vars @ [k]
      ; command = CutNeg (mk_neg body_ty', mk_thunk_cocase body_ty' body', Variable k)
      }
    ) clauses in
    let inner_ty = TyNeg codata_sgn in
    mk_close inner_ty (New (codata_sgn, branches))

  | LTm.TyTmCtor (ctor, ty_args, tm_args, ty) ->
    (* Constructor application - may be partial *)
    map_ctor_application sgns ctor ty_args tm_args ty

  | LTm.TyTmDtor (dtor, ty_args, tm_args, ty) ->
    (* Destructor application *)
    map_dtor_application sgns dtor ty_args tm_args ty

  | LTm.TyTmInt (n, _) ->
    (* Integer literal n : Box(ext int)
       [n] = μk. extern lit_n {(v) => ⟨box(v) | k⟩} *)
    let k = Ident.fresh () in
    let v = Ident.fresh () in
    let box_v =
      Constructor (mk_box_xtor (), [Ext.int_t], [Variable v]) in
    let clause =
      { parameters = [v]; body = CutPos (box_int_ty, box_v, Variable k) } in
    MuLhsPos (box_int_ty, k, Extern (Sym.i32_lit n, [], [clause]))

  | LTm.TyTmAdd (t1, t2, _ty) ->
    (* Integer addition e1 + e2 : Box(ext int)
       [e1 + e2] = μk.⟨[e1]| case {box(v1) => ⟨[e2]| case {box(v2) => 
                     extern add(v1, v2) {(v) => ⟨box(v) | k⟩}}}⟩ *)
    let k = Ident.fresh () in
    let v1 = Ident.fresh () in
    let v2 = Ident.fresh () in
    let v = Ident.fresh () in
    let box_xtor = mk_box_xtor () in
    let box_v = Constructor (box_xtor, [Ext.int_t], [Variable v]) in
    let add_clause =
      { parameters = [v]; body = CutPos (box_int_ty, box_v, Variable k) } in
    let add_extern =
      Extern (Sym.i32_add, [Variable v1; Variable v2], [add_clause]) in
    let unbox var cmd =
      Match (Prim.box_sgn,
        [{ xtor = box_xtor; type_vars = []; term_vars = [var]; command = cmd }])
    in
    let t2' = map_term sgns t2 in
    let t1' = map_term sgns t1 in
    MuLhsPos (box_int_ty, k,
      CutPos (box_int_ty, t1', unbox v1
        (CutPos (box_int_ty, t2', unbox v2 add_extern))))

(** Map an application (possibly partial) of a head to type and term arguments *)
and map_application (sgns: signatures) (head: LTm.typed_term) 
    (ty_args: LTy.typ list) (tm_args: LTm.typed_term list) =
  match head with
  | LTm.TyTmSym (sym, sym_ty) ->
    (* Application of a top-level symbol *)
    let required_arity = count_fun_arrows sym_ty in
    let provided_arity = List.length tm_args in
    
    if provided_arity = required_arity then
      (* Fully applied - generate Call *)
      let ret_ty = get_return_type sym_ty in
      let ret_ty' = map_type ret_ty in
      let tys = List.map map_type ty_args in
      let args = List.map (map_term sgns) tm_args in
      let k = Ident.fresh () in
      MuLhsPos (ret_ty', k, Call (sym, tys, args @ [Variable k]))
    
    else if provided_arity < required_arity then
      (* Partial application - generate lambdas for remaining args *)
      let arg_types = get_arg_types sym_ty in
      let remaining_arg_types = Utility.drop provided_arity arg_types in
      let provided_args = List.map (map_term sgns) tm_args in
      build_partial_application sgns sym sym_ty ty_args
      provided_args remaining_arg_types
    
    else
      failwith "map_application: over-applied function"

  | LTm.TyTmCtor (ctor, ctor_ty_args, ctor_tm_args, _) ->
    (* Constructor partially applied through further application *)
    let all_ty_args = ctor_ty_args @ ty_args in
    let all_tm_args = ctor_tm_args @ tm_args in
    map_ctor_application sgns ctor all_ty_args all_tm_args (LTm.get_type head)

  | LTm.TyTmDtor (dtor, dtor_ty_args, dtor_tm_args, _) ->
    (* Destructor applied through further application *)
    let all_ty_args = dtor_ty_args @ ty_args in
    let all_tm_args = dtor_tm_args @ tm_args in
    map_dtor_application sgns dtor all_ty_args all_tm_args (LTm.get_type head)

  | _ ->
    (* General case: apply one argument at a time *)
    let rec apply_args
        (t: term) (t_ty: LTy.typ) (tys: LTy.typ list) (args: LTm.typed_term list) =
      match tys, args with
      | [], [] -> t
      | ty :: rest_tys, [] ->
        (* Type instantiation *)
        let ret_ty = instantiate_forall t_ty ty in
        let kind = get_forall_kind t_ty in
        let t' = build_inst kind (map_type ty) (map_type ret_ty) t in
        apply_args t' ret_ty rest_tys []
      | tys, arg :: rest_args ->
        (* First consume all type args, then term args *)
        let t', t_ty' = 
          List.fold_left (fun (t, ty) ty_arg ->
            let ret_ty = instantiate_forall ty ty_arg in
            let kind = get_forall_kind ty in
            (build_inst kind (map_type ty_arg) (map_type ret_ty) t, ret_ty)
          ) (t, t_ty) tys
        in
        let arg_ty, ret_ty = get_fun_arg_ret t_ty' in
        let arg' = map_term sgns arg in
        let t'' = build_app (map_type arg_ty) (map_type ret_ty) t' arg' in
        apply_args t'' ret_ty [] rest_args
    in
    let head' = map_term sgns head in
    let head_ty = LTm.get_type head in
    apply_args head' head_ty ty_args tm_args

(** Build nested lambdas for partial application of a symbol *)
and build_partial_application
    (sgns: signatures) (sym: symbol) (sym_ty: LTy.typ)
    (ty_args: LTy.typ list) (provided_args: term list)
    (remaining_tys: LTy.typ list) =
  match remaining_tys with
  | [] ->
    (* All arguments collected - make the call *)
    let ret_ty = get_return_type sym_ty in
    let ret_ty' = map_type ret_ty in
    let tys = List.map map_type ty_args in
    let k = Ident.fresh () in
    MuLhsPos (ret_ty', k, Call (sym, tys, provided_args @ [Variable k]))
  | arg_ty :: rest_tys ->
    (* Build lambda for this argument *)
    let x = Ident.fresh () in
    let arg_ty' = map_type arg_ty in
    let inner =
      build_partial_application
        sgns sym sym_ty ty_args 
        (provided_args @ [Variable x]) rest_tys
    in
    let inner_ty = 
      List.fold_right (fun t acc -> 
        mk_pos (TyApp (TyApp (Prim.fun_t, map_type t), mk_neg acc))
      ) rest_tys (map_type (get_return_type sym_ty))
    in
    build_lambda arg_ty' inner_ty x inner

(** Map constructor application (possibly partial) *)
and map_ctor_application
    (sgns: signatures) (ctor: LTy.ty_xtor) 
    (ty_args: LTy.typ list) (tm_args: LTm.typed_term list)
    (result_ty: LTy.typ) =
  let required_arity = List.length ctor.LTy.sources in
  let provided_arity = List.length tm_args in
  
  if provided_arity = required_arity then
    (* Fully applied constructor *)
    let xtor' = map_xtor sgns ctor in
    let tys = List.map map_type ty_args in
    let args = List.map (map_term sgns) tm_args in
    Constructor (xtor', tys, args)
  
  else if provided_arity < required_arity then
    (* Partial constructor application - wrap in lambdas *)
    let remaining_tys =
      Utility.drop provided_arity ctor.LTy.sources
    in
    let provided_args = List.map (map_term sgns) tm_args in
    build_partial_ctor
      sgns ctor ty_args
      provided_args remaining_tys
      result_ty
  
  else
    failwith "map_ctor_application: over-applied constructor"

and build_partial_ctor
    (sgns: signatures) (ctor: LTy.ty_xtor)
    (ty_args: LTy.typ list) (provided_args: term list) 
    (remaining_tys: LTy.typ list)
    (result_ty: LTy.typ) =
  match remaining_tys with
  | [] ->
    let xtor' = map_xtor sgns ctor in
    let tys = List.map map_type ty_args in
    Constructor (xtor', tys, provided_args)
  | arg_ty :: rest_tys ->
    let x = Ident.fresh () in
    let arg_ty' = map_type arg_ty in
    let inner =
      build_partial_ctor sgns ctor ty_args 
        (provided_args @ [Variable x]) rest_tys result_ty
    in
    let inner_ty =
      List.fold_right (fun t acc ->
        mk_pos (TyApp (TyApp (Prim.fun_t, map_type t), mk_neg acc))
      ) rest_tys (map_type result_ty)
    in
    build_lambda arg_ty' inner_ty x inner

(** Map destructor application *)
and map_dtor_application
    (sgns: signatures) (dtor: LTy.ty_xtor)
    (ty_args: LTy.typ list) (tm_args: LTm.typed_term list)
    (result_ty: LTy.typ) =
  (* Destructors need at least self argument *)
  match tm_args with
  | [] -> failwith "map_dtor_application: destructor needs self argument"
  | self :: rest ->
    let self_ty = LTm.get_type self in
    let self' = map_term sgns self in
    let self_ty' = map_type self_ty in
    let ret_ty' = map_type result_ty in
    let xtor' = map_xtor sgns dtor in
    let tys = List.map map_type ty_args in
    let args = List.map (map_term sgns) rest in
    let k = Ident.fresh () in
    let f = Ident.fresh () in
    let inner_ty = TyNeg (get_codata_signature sgns self_ty) in
    let dtor_term = Destructor (xtor', tys, args @ [mk_thunk ret_ty' k]) in
    (* μk. ⟨self | case{close(f) ⇒ ⟨f | D(args, thunk(k))⟩}⟩ *)
    MuLhsPos (ret_ty', k,
      CutPos (self_ty', self',
        Match (Prim.pos_sgn, [{
          xtor = mk_close_xtor inner_ty
        ; type_vars = []
        ; term_vars = [f]
        ; command = CutNeg (inner_ty, Variable f, dtor_term)
        }])))

(** Helper: get signature from a type (data or codata) *)
and get_signature (sgns: signatures) (ty: LTy.typ) =
  match ty with
  | LTy.TyDef (LTy.Data dec) -> map_data dec
  | LTy.TyDef (LTy.Code dec) -> map_code dec
  | LTy.TySym s -> let sgn, _, _ = get_def sgns s in sgn
  | LTy.TyApp (t, _) -> get_signature sgns t
  | _ -> failwith "get_signature: not a data/codata type"

and get_signature_of_type sgns ty = get_signature sgns ty
and get_signature_of_new_type sgns ty = get_signature sgns ty
and get_codata_signature sgns ty = get_signature sgns ty

(** Map a Lang xtor to Kore xtor *)
and map_xtor (_sgns: signatures) (xtor: LTy.ty_xtor) =
  { parent = xtor.LTy.parent
  ; name = xtor.LTy.symbol
  ; quantified =
      List.map (fun (v, k) -> (v, map_kinds k)
      ) xtor.LTy.quantified
  ; parameters =
      List.map (fun t -> Lhs (map_type t)
      ) xtor.LTy.sources
  ; parent_arguments =
      List.map map_type xtor.LTy.arguments
  ; constraints =
      Option.map (List.map (fun (v, t) -> (v, map_type t)
      )) xtor.LTy.constraints
  }

(** Helper: instantiate a forall type *)
and instantiate_forall (ty: LTy.typ) (arg: LTy.typ) =
  match ty with
  | LTy.TyAll ((a, _), body) -> 
    LTy.subst (Ident.add a arg Ident.emptytbl) body
  | _ -> failwith "instantiate_forall: not a forall type"

(** Helper: get kind from forall *)
and get_forall_kind (ty: LTy.typ) =
  match ty with
  | LTy.TyAll ((_, k), _) -> map_kinds k
  | _ -> failwith "get_forall_kind: not a forall type"

(** Helper: get function argument and return types *)
and get_fun_arg_ret (ty: LTy.typ) =
  match ty with
  | LTy.TyFun (a, b) -> (a, b)
  | _ -> failwith "get_fun_arg_ret: not a function type"