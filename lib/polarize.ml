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
let rec collect_args
    (tm: LTm.typed_term): (LTm.typed_term * LTm.typed_term list) =
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
  let k' = Ident.fresh () in  (* k' : cns [B] *)
  (* 
    The function type is: ↑([A] → ↓[B])
    Inner codata type: [A] → ↓[B]
  *)
  let inner_fun_ty = TyApp (TyApp (Prim.fun_t, arg_ty), mk_neg ret_ty) in
  let inner_fun_sgn = Prim.fun_sgn in
  (* Build instantiated apply xtor for this specific function type *)
  let apply_xtor = 
    { Prim.fun_apply with
      parameters = [Lhs arg_ty; Rhs (mk_neg ret_ty)]
    ; parent_arguments = [arg_ty; mk_neg ret_ty]
    }
  in
  (* Inner: cocase {thunk(k') ⇒ ⟨body | k'⟩} : prd ↓[B] *)
  let neg_ret_ty = mk_neg ret_ty in
  let neg_sgn = Prim.neg_sgn in
  let thunk_xtor =
    { Prim.neg_thunk with
      parameters = [Rhs ret_ty]
    ; parent_arguments = [ret_ty]
    }
  in
  let inner_cocase =
    New (neg_sgn, [{
      xtor = thunk_xtor
    ; type_vars = []
    ; term_vars = [k']
    ; command = CutPos (ret_ty, body, Variable k')
    }])
  in
  (* Middle: cocase {apply(x, k) ⇒ ⟨inner_cocase | k⟩} : prd ([A] → ↓[B]) *)
  let middle_cocase =
    New (inner_fun_sgn, [{
      xtor = apply_xtor
    ; type_vars = []
    ; term_vars = [x; k]
    ; command = CutNeg (neg_ret_ty, inner_cocase, Variable k)
    }])
  in
  (* Outer: close(middle_cocase) : prd ↑([A] → ↓[B]) *)
  let close_xtor =
    { Prim.pos_close with
      parameters = [Lhs inner_fun_ty]
    ; parent_arguments = [inner_fun_ty]
    }
  in
  Constructor (close_xtor, [inner_fun_ty], [middle_cocase])

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
  let k = Ident.fresh () in   (* k: cns [B] - the final result continuation *)
  let f = Ident.fresh () in   (* f: prd ([A] → ↓[B]) - the unwrapped function *)
  (*
    Function type: ↑([A] → ↓[B])
    After unwrapping close: [A] → ↓[B]
  *)
  let inner_fun_ty = TyApp (TyApp (Prim.fun_t, arg_ty), mk_neg ret_ty) in
  let outer_fun_ty = mk_pos inner_fun_ty in
  let pos_sgn = Prim.pos_sgn in
  let close_xtor =
    { Prim.pos_close with
      parameters = [Lhs inner_fun_ty]
    ; parent_arguments = [inner_fun_ty]
    }
  in
  (* thunk(k) : cns ↓[B] *)
  let thunk_xtor =
    { Prim.neg_thunk with
      parameters = [Rhs ret_ty]
    ; parent_arguments = [ret_ty]
    }
  in
  let thunk_k = Destructor (thunk_xtor, [ret_ty], [Variable k]) in
  (* apply(u_term, thunk(k)) : cns ([A] → ↓[B]) *)
  let apply_xtor =
    { Prim.fun_apply with
      parameters = [Lhs arg_ty; Rhs (mk_neg ret_ty)]
    ; parent_arguments = [arg_ty; mk_neg ret_ty]
    }
  in
  let apply_dtor =
    Destructor (apply_xtor, [arg_ty; mk_neg ret_ty], [u_term; thunk_k])
  in
  (* case {close(f) ⇒ ⟨f | apply(u, thunk(k))⟩} : cns ↑([A] → ↓[B]) *)
  let match_term =
    Match (pos_sgn, [{
      xtor = close_xtor
    ; type_vars = []
    ; term_vars = [f]
    ; command = CutNeg (inner_fun_ty, Variable f, apply_dtor)
    }])
  in
  (* μk. ⟨t | match⟩ *)
  MuLhsPos (ret_ty, k, CutPos (outer_fun_ty, t_term, match_term))

(**
  Build a type instantiation in the positive fragment:
    [t{A}] = μ(k: cns [B]). ⟨[t] | case {close(f) ⇒ ⟨f | insta{A}(thunk(k))⟩}⟩
*)
let build_inst (kind: kind) (ty_arg: tpe) (ret_ty: tpe) (t_term: term) =
  let a = Ident.fresh () in   (* type variable for the forall *)
  let k = Ident.fresh () in   (* k: cns [B] *)
  let f = Ident.fresh () in   (* f: prd (∀F) where F applied to ty_arg = ret_ty *)
  (*
    Forall type: ↑(∀(a:k). ↓[B])
    Inner: ∀(a:k). ↓[B]
  *)
  let inner_all_ty = TyApp (Prim.all_t a kind, mk_neg ret_ty) in
  let outer_all_ty = mk_pos inner_all_ty in
  let pos_sgn = Prim.pos_sgn in
  let close_xtor =
    { Prim.pos_close with
      parameters = [Lhs inner_all_ty]
    ; parent_arguments = [inner_all_ty]
    }
  in
  (* thunk(k): cns ↓[B] *)
  let thunk_xtor =
    { Prim.neg_thunk with
      parameters = [Rhs ret_ty]
    ; parent_arguments = [ret_ty]
    }
  in
  let thunk_k = Destructor (thunk_xtor, [ret_ty], [Variable k]) in
  (* insta{ty_arg}(thunk(k)): cns (∀(a:k). ↓[B]) *)
  let insta_xtor = Prim.all_insta a kind in
  let insta_dtor = Destructor (insta_xtor, [ty_arg], [thunk_k]) in
  (* case {close(f) ⇒ ⟨f | insta{A}(thunk(k))⟩} *)
  let match_term =
    Match (pos_sgn, [{
      xtor = close_xtor
    ; type_vars = []
    ; term_vars = [f]
    ; command = CutNeg (inner_all_ty, Variable f, insta_dtor)
    }])
  in
  MuLhsPos (ret_ty, k, CutPos (outer_all_ty, t_term, match_term))

(**
  Build a type abstraction in the positive fragment:
    [{a:k} t] =
      close(cocase {insta{a}(k) ⇒ ⟨cocase {thunk(k') ⇒ ⟨〚t〛| k'⟩} | k⟩})
*)
let build_type_abs (a: variable) (kind: kind) (ret_ty: tpe) (body: term) =
  let k = Ident.fresh () in   (* k: cns ↓[B] *)
  let k' = Ident.fresh () in  (* k': cns [B] *)
  let inner_all_ty = TyApp (Prim.all_t a kind, mk_neg ret_ty) in
  let all_sgn = Prim.all_sgn a kind in
  let insta_xtor = Prim.all_insta a kind in
  (* Inner: cocase {thunk(k') ⇒ ⟨body | k'⟩} *)
  let neg_ret_ty = mk_neg ret_ty in
  let neg_sgn = Prim.neg_sgn in
  let thunk_xtor =
    { Prim.neg_thunk with
      parameters = [Rhs ret_ty]
    ; parent_arguments = [ret_ty]
    }
  in
  let inner_cocase =
    New (neg_sgn, [{
      xtor = thunk_xtor
    ; type_vars = []
    ; term_vars = [k']
    ; command = CutPos (ret_ty, body, Variable k')
    }])
  in
  (* Middle: cocase {insta{a}(k) ⇒ ⟨inner | k⟩} *)
  let middle_cocase =
    New (all_sgn, [{
      xtor = insta_xtor
    ; type_vars = [(a, kind)]
    ; term_vars = [k]
    ; command = CutNeg (neg_ret_ty, inner_cocase, Variable k)
    }])
  in
  (* Outer: close(middle) *)
  let close_xtor =
    { Prim.pos_close with
      parameters = [Lhs inner_all_ty]
    ; parent_arguments = [inner_all_ty]
    }
  in
  Constructor (close_xtor, [inner_all_ty], [middle_cocase])

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
    let _ty' = map_type ty in
    let codata_sgn = get_signature_of_new_type sgns ty in
    let branches = List.map (fun (xtor, type_vars, term_vars, body) ->
      let body_ty = LTm.get_type body in
      let body' = map_term sgns body in
      let body_ty' = map_type body_ty in
      let k = Ident.fresh () in
      let k' = Ident.fresh () in
      let xtor' = map_xtor sgns xtor in
      (* Get kinds from the xtor's quantified list *)
      let type_vars_with_kinds =
        List.map2 (fun v (_, knd) -> (v, map_kinds knd)
        ) type_vars xtor.LTy.quantified
      in
      (* Inner thunk cocase *)
      let neg_body_ty = mk_neg body_ty' in
      let thunk_xtor =
        { Prim.neg_thunk with
          parameters = [Rhs body_ty']
        ; parent_arguments = [body_ty']
        }
      in
      let inner_cocase =
        New (Prim.neg_sgn, [{
          xtor = thunk_xtor
        ; type_vars = []
        ; term_vars = [k']
        ; command = CutPos (body_ty', body', Variable k')
        }])
      in
      { xtor = xtor'
      ; type_vars = type_vars_with_kinds
      ; term_vars = term_vars @ [k]  (* Add continuation parameter *)
      ; command = CutNeg (neg_body_ty, inner_cocase, Variable k)
      }
    ) clauses in
    (* The codata itself - need to wrap in close for positive fragment *)
    let inner_codata = New (codata_sgn, branches) in
    let inner_ty = TyNeg codata_sgn in
    let close_xtor =
      { Prim.pos_close with
        parameters = [Lhs inner_ty]
      ; parent_arguments = [inner_ty]
      }
    in
    Constructor (close_xtor, [inner_ty], [inner_codata])

  | LTm.TyTmCtor (ctor, ty_args, tm_args, ty) ->
    (* Constructor application - may be partial *)
    map_ctor_application sgns ctor ty_args tm_args ty

  | LTm.TyTmDtor (dtor, ty_args, tm_args, ty) ->
    (* Destructor application *)
    map_dtor_application sgns dtor ty_args tm_args ty

  | LTm.TyTmInt (n, _) ->
    (* Integer literal n : Box(ext int)
       〚n〛= μk. extern lit_n {(v) => ⟨box(v) | k⟩}
       where v : prd (ext int), box(v) : prd Box(ext int), k : cns Box(ext int)
    *)
    let k = Ident.fresh () in
    let v = Ident.fresh () in
    let box_ty = TyApp (Prim.box_t, Ext.int_t) in  (* Box(ext int) *)
    let box_xtor =
      { Prim.box_mk with
        parameters = [Lhs Ext.int_t]
      ; parent_arguments = [Ext.int_t]
      }
    in
    let box_v = Constructor (box_xtor, [Ext.int_t], [Variable v]) in
    let clause = { parameters = [v]; body = CutPos (box_ty, box_v, Variable k) } in
    MuLhsPos (box_ty, k, Extern (Sym.i32_lit n, [], [clause]))

  | LTm.TyTmAdd (t1, t2, _ty) ->
    (* Integer addition e1 + e2 : Box(ext int)
       〚e1 + e2〛= μk. ⟨〚e1〛| case {box(v1) => ⟨〚e2〛| case {box(v2) => 
                         extern add(v1, v2) {(v) => ⟨box(v) | k⟩}}}⟩
       
       Both e1 and e2 have type Box(ext int), so we unbox, call extern, rebox.
    *)
    let k = Ident.fresh () in
    let v1 = Ident.fresh () in
    let v2 = Ident.fresh () in
    let v = Ident.fresh () in
    let box_ty = TyApp (Prim.box_t, Ext.int_t) in  (* Box(ext int) *)
    let box_xtor =
      { Prim.box_mk with
        parameters = [Lhs Ext.int_t]
      ; parent_arguments = [Ext.int_t]
      }
    in
    (* box(v) for the result *)
    let box_v = Constructor (box_xtor, [Ext.int_t], [Variable v]) in
    (* extern add(v1, v2) {(v) => ⟨box(v) | k⟩} *)
    let add_clause =
      { parameters = [v]; body = CutPos (box_ty, box_v, Variable k) }
    in
    let add_extern =
      Extern (Sym.i32_add, [Variable v1; Variable v2], [add_clause])
    in
    (* case {box(v2) => extern add ...} for unboxing e2 *)
    let unbox2 = Match (Prim.box_sgn,
      [{ xtor = box_xtor
      ; type_vars = []
      ; term_vars = [v2]
      ; command = add_extern
      }])
    in
    (* case {box(v1) => ⟨〚e2〛| unbox2⟩} for unboxing e1 *)
    let t2' = map_term sgns t2 in
    let unbox1 = Match (Prim.box_sgn,
      [{ xtor = box_xtor
      ; type_vars = []
      ; term_vars = [v1]
      ; command = CutPos (box_ty, t2', unbox2)
      }])
    in
    (* μk. ⟨〚e1〛| unbox1⟩ *)
    let t1' = map_term sgns t1 in
    MuLhsPos (box_ty, k, CutPos (box_ty, t1', unbox1))

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
    (* μk. ⟨self | D(args, thunk(k))⟩ *)
    (* Need to wrap continuation in thunk for negative codomain *)
    let thunk_xtor =
      { Prim.neg_thunk with
        parameters = [Rhs ret_ty']
      ; parent_arguments = [ret_ty']
      }
    in
    let thunk_k = Destructor (thunk_xtor, [ret_ty'], [Variable k]) in
    let dtor_term = Destructor (xtor', tys, args @ [thunk_k]) in
    let inner_ty = TyNeg (get_codata_signature sgns self_ty) in
    (* Need to unwrap close first if self is shifted *)
    let f = Ident.fresh () in
    let close_xtor =
      { Prim.pos_close with
        parameters = [Lhs inner_ty]
      ; parent_arguments = [inner_ty]
      }
    in
    MuLhsPos (ret_ty', k,
      CutPos (self_ty', self',
        Match (Prim.pos_sgn, [{
          xtor = close_xtor
        ; type_vars = []
        ; term_vars = [f]
        ; command = CutNeg (inner_ty, Variable f, dtor_term)
        }])))

(** Helper: get signature from a data type *)
and get_signature_of_type (sgns: signatures) (ty: LTy.typ) =
  match ty with
  | LTy.TyDef (LTy.Data dec) -> map_data dec
  | LTy.TySym s ->
    let sgn, _, _ = get_def sgns s in sgn
  | LTy.TyApp (t, _) -> get_signature_of_type sgns t
  | _ -> failwith "get_signature_of_type: not a data type"

(** Helper: get signature from a codata type used in new *)
and get_signature_of_new_type (sgns: signatures) (ty: LTy.typ) =
  (* The type is ↑(codata), we need to extract the codata signature *)
  match ty with
  | LTy.TyDef (LTy.Code dec) -> map_code dec
  | LTy.TySym s ->
    let sgn, _, _ = get_def sgns s in sgn
  | LTy.TyApp (t, _) -> get_signature_of_new_type sgns t
  | _ -> failwith "get_signature_of_new_type: not a codata type"

(** Helper: get codata signature *)
and get_codata_signature (sgns: signatures) (ty: LTy.typ) =
  get_signature_of_new_type sgns ty

(** Map a Lang xtor to Kore xtor *)
and map_xtor (_sgns: signatures) (xtor: LTy.ty_xtor) =
  { parent = xtor.LTy.parent
  ; name = xtor.LTy.symbol
  ; quantified =
      List.map (fun (v, k) -> (v, map_kinds k)
      ) xtor.LTy.quantified
  ; parameters =
      List.map (fun t -> Lhs (map_type t)) xtor.LTy.sources
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