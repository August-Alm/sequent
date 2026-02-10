(**
  Module: Polarize
  Description: Translates Lang to polarized Kore.
  
  - Lang data types → Kore positive types (data)
  - Lang codata types → Kore negative types (codata)
  - Functions A → B: codomain wrapped in ¬ only if B is positive
*)

module LTy = Lang.Types
module LTm = Lang.Terms
module Sym = Kore.Builtins.Sym
module Ext = Kore.Builtins.Ext
module Prim = Kore.Builtins.Prim
open Kore.Types
open Kore.Terms
open Common.Identifiers

(* Map Lang kinds to Kore kinds *)
let rec map_kinds (k: LTy.kind) =
  match k with
  | LTy.KStar -> Pos  (* Default to Pos for now; refined by actual type def *)
  | LTy.KArrow (k1, k2) -> Arrow (map_kinds k1, map_kinds k2)

(* Logical negation / continuation: ¬(X:+) *)
let mk_neg tt = TyApp (Prim.neg_t, tt)

(* Raise: ↑(A:-) - wraps negative in positive *)
let mk_raise tt = TyApp (Prim.raise_t, tt)

(* Lower: ↓(A:+) - wraps positive in negative (thunk) *)
let mk_lower tt = TyApp (Prim.lower_t, tt)

(* Check if a Lang type is positive (data or primitive) *)
let rec is_positive_type (tt: LTy.typ) : bool =
  match tt with
  | LTy.TySym _ -> true  (* Assume symbol references are positive for now *)
  | LTy.TyVar _ -> true  (* Type variables assumed positive *)
  | LTy.TyApp (t1, _) -> is_positive_type t1
  | LTy.TyFun (_, _) -> false  (* Functions are NEGATIVE (codata) *)
  | LTy.TyAll (_, _) -> false  (* Foralls are NEGATIVE (codata) *)
  | LTy.TyDef (Data _) -> true
  | LTy.TyDef (Code _) -> false  (* Codata is negative *)
  | LTy.TyPrim _ -> true  (* Primitives are positive *)

(* Instantiate ret xtor for a given inner positive type *)
let mk_ret_xtor inner_ty =
  { Prim.neg_ret with
    quantified = []
  ; parameters = [Lhs inner_ty]
  ; parent_arguments = [inner_ty]
  }

(* Instantiate close xtor for a given inner negative type *)
let mk_close_xtor inner_ty =
  { Prim.raise_close with
    quantified = []
  ; parameters = [Lhs inner_ty]
  ; parent_arguments = [inner_ty]
  }

(* Instantiate thunk xtor for a given result type *)
let mk_thunk_xtor ret_ty =
  { Prim.lower_thunk with
    quantified = []
  ; parameters = [Rhs ret_ty]
  ; parent_arguments = [ret_ty]
  }

(* Instantiate box xtor for ext int *)
let mk_box_xtor () =
  { Prim.box_mk with
    quantified = []
  ; parameters = [Lhs Ext.int_t]
  ; parent_arguments = [Ext.int_t]
  }

(* The type Box(ext int) *)
let box_int_ty = TyApp (Prim.box_t, Ext.int_t)

(* Build: cocase {ret(v) ⇒ ⟨body | μ̃v.cmd⟩} - no, wait...
   Actually for ¬(X), we have ret(prd X), so:
   Build: cocase {ret(k') ⇒ ⟨body | k'⟩} doesn't make sense either.
   
   The ¬ type receives a value, so to create a ¬X we do:
   cocase {ret(v) ⇒ cmd_using_v}
*)

(* Build: cocase {thunk(k') ⇒ ⟨body | k'⟩} : prd ↓[ret_ty] *)
let mk_thunk_cocase ret_ty body =
  let k' = Ident.fresh () in
  New (Prim.lower_sgn, [{
    xtor = mk_thunk_xtor ret_ty
  ; type_vars = []
  ; term_vars = [k']
  ; command = CutPos (ret_ty, body, Variable k')
  }])

(* Build: close(inner) where inner : prd inner_ty *)
let mk_close inner_ty inner =
  Constructor (mk_close_xtor inner_ty, [], [inner])

(* Build: thunk(k) : cns ↓[ret_ty] *)
let mk_thunk ret_ty k =
  Destructor (mk_thunk_xtor ret_ty, [], [Variable k])

(* Build: ret(v) : cns ¬[pos_ty] - destructor to send value to continuation *)
let mk_ret pos_ty v =
  Destructor (mk_ret_xtor pos_ty, [], [v])

(* Helper: translate Lang type to Kore type
   - Data types → positive (TyPos)
   - Codata types → negative (TyNeg)
   - Functions A → B → negative function type (stays negative!)
   - Forall {a:k} T → negative forall type (stays negative!)
   
   Codomain wrapping: only wrap in ¬ when the codomain is positive.
*)
let rec go expand tt =
  match tt with
  | LTy.TySym s -> TySym s
  | LTy.TyVar x -> TyVar x
  | LTy.TyApp (t1, t2) -> TyApp (go expand t1, go expand t2)
  | LTy.TyFun (t1, t2) ->
    (*
      [A → B] = code (X:+) → (Y:-) where apply(prd X, cns Y)
      
      The codomain Y:
      - If B is positive (data/primitive): Y = ¬[B] (continuation)
      - If B is negative (codata/function): Y = [B] directly
      
      The whole function type is NEGATIVE (codata).
    *)
    let arg_ty = go expand t1 in
    let codomain_ty = 
      if is_positive_type t2 then
        mk_neg (go expand t2)  (* ¬[B] for positive B *)
      else
        go expand t2  (* [B] directly for negative B *)
    in
    if expand then
      TyApp (TyApp (Prim.fun_t, arg_ty), codomain_ty)
    else
      TyApp (TyApp (TySym Sym.fun_t, arg_ty), codomain_ty)
  | LTy.TyAll ((a, k), t) ->
    (*
      [{a:k} T] = code ∀(F: k → -) where insta{X}(cns F(X))
      
      Same codomain handling as functions.
      The whole forall type is NEGATIVE (codata).
    *)
    let kind = map_kinds k in
    let codomain_ty =
      if is_positive_type t then
        mk_neg (go expand t)
      else
        go expand t
    in
    if expand then
      TyApp (Prim.all_t a kind, codomain_ty)
    else
      TyApp (TySym (Sym.all_t kind), codomain_ty)
  | LTy.TyDef (Data dec) -> TyPos (go_dec true dec)
  | LTy.TyDef (Code dec) -> TyNeg (go_dec false dec)  (* Codata stays negative! *)
  (* Box primitive types *)
  | LTy.TyPrim Int -> TyApp (Prim.box_t, Ext.int_t)

and go_dec _is_data (dec: LTy.ty_dec) =
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
            (* All parameters are producers (Lhs) - including continuation for codata *)
            List.map (fun t -> Lhs (go false t)
            ) xtor.LTy.sources
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
  Build a lambda term:
    [fun (x: A) ⇒ t] where t : B
    
  Since function types are now NEGATIVE, a lambda is a cocase (New) directly.
  No ↑ wrapping needed.
    
  If B is positive:
    cocase {apply(x, k) ⇒ ⟨k | ret([t])⟩}
    where k : cns ¬[B]
    
  If B is negative:
    cocase {apply(x, k) ⇒ ⟨[t] | k⟩}
    where k : cns [B]
*)
let build_lambda (arg_ty: tpe) (ret_ty: tpe) (ret_is_pos: bool) (x: variable) (body: term) =
  let k = Ident.fresh () in
  let codomain_ty = if ret_is_pos then mk_neg ret_ty else ret_ty in
  let apply_xtor = 
    { Prim.fun_apply with
      quantified = []
    ; parameters = [Lhs arg_ty; Lhs codomain_ty]  (* k is producer now! *)
    ; parent_arguments = [arg_ty; codomain_ty]
    }
  in
  (* Build the body command *)
  let body_cmd =
    if ret_is_pos then
      (* k : prd ¬[B] (a cocase representing the return continuation)
         To return body : prd [B], we invoke k with neg.ret(body)
         ⟨k | neg.ret(body)⟩ : sends body to the caller's continuation *)
      let neg_ret_xtor =
        { Prim.neg_ret with
          quantified = []
        ; parameters = [Lhs ret_ty]
        ; parent_arguments = [ret_ty]
        }
      in
      let invoker = Destructor (neg_ret_xtor, [], [body]) in
      CutNeg (codomain_ty, Variable k, invoker)
    else
      (* k : prd [B] (body is negative), need to cut properly *)
      CutNeg (ret_ty, Variable k, body)
  in
  (* Lambda is just a cocase - function type is negative *)
  New (Prim.fun_sgn, [{
    xtor = apply_xtor
  ; type_vars = []
  ; term_vars = [x; k]
  ; command = body_cmd
  }])

(**
  Build an application term:
    [t u] where t : A → B
    
  Since function types are now NEGATIVE, t is a codata value.
  We apply by sending a destructor (apply) to it.
    
  If B is positive:
    μk. ⟨[t] | apply([u], cocase{ret(r) => ⟨r|k⟩})⟩
    where k : cns [B], and we build a cocase that forwards received value to k:
    - cocase{ret(r) => ⟨r|k⟩} : prd ¬[B]
    - When function invokes this with ret(result), we get result and forward to k
    
  If B is negative:
    μk. ⟨[t] | apply([u], k)⟩
    where k : prd [B] directly (continuation is the value)
*)
let build_app (arg_ty: tpe) (ret_ty: tpe) (ret_is_pos: bool) (t_term: term) (u_term: term) =
  let k = Ident.fresh () in
  let codomain_ty = if ret_is_pos then mk_neg ret_ty else ret_ty in
  let fun_ty = TyApp (TyApp (Prim.fun_t, arg_ty), codomain_ty) in
  (* Use the full polymorphic xtor, but with concrete type arguments *)
  let apply_xtor = Prim.fun_apply in
  (* Build the continuation argument to apply *)
  let cont_arg =
    if ret_is_pos then
      (* Build cocase{ret(r) => ⟨r|k⟩} : prd ¬[B]
         When function calls ret(result), we forward result to k *)
      let r = Ident.fresh () in
      let neg_ret_xtor =
        { Prim.neg_ret with
          quantified = []
        ; parameters = [Lhs ret_ty]
        ; parent_arguments = [ret_ty]
        }
      in
      New (Prim.neg_sgn, [{
        xtor = neg_ret_xtor
      ; type_vars = []
      ; term_vars = [r]
      ; command = CutPos (ret_ty, Variable r, Variable k)
      }])
    else
      (* k directly : prd [B] (where B is negative) *)
      Variable k
  in
  let apply_dtor =
    Destructor (apply_xtor, [], [u_term; cont_arg])
  in
  (* Use MuLhsPos for positive return, MuLhsNeg for negative return *)
  if ret_is_pos then
    MuLhsPos (ret_ty, k, CutNeg (fun_ty, t_term, apply_dtor))
  else
    MuLhsNeg (ret_ty, k, CutNeg (fun_ty, t_term, apply_dtor))

(**
  Build a type instantiation:
    [t{A}] where t : {a:k} B
    
  Since forall types are NEGATIVE, t is a codata value.
  We apply by sending a destructor (insta) to it.
    
  If B is positive:
    μk. ⟨[t] | insta{A}(cocase{ret(r) => ⟨r|k⟩})⟩
    where we build a cocase that forwards received value to k
    
  If B is negative:
    μk. ⟨[t] | insta{A}(k)⟩
*)
let build_inst (kind: kind) (ty_arg: tpe) (ret_ty: tpe) (ret_is_pos: bool) (t_term: term) =
  let a = Ident.fresh () in
  let k = Ident.fresh () in
  let codomain_ty = if ret_is_pos then mk_neg ret_ty else ret_ty in
  let all_ty = TyApp (Prim.all_t a kind, codomain_ty) in
  let insta_xtor = Prim.all_insta a kind in
  (* Build the continuation argument to insta *)
  let cont_arg =
    if ret_is_pos then
      (* Build cocase{ret(r) => ⟨r|k⟩} : prd ¬[B] *)
      let r = Ident.fresh () in
      let neg_ret_xtor =
        { Prim.neg_ret with
          quantified = []
        ; parameters = [Lhs ret_ty]
        ; parent_arguments = [ret_ty]
        }
      in
      New (Prim.neg_sgn, [{
        xtor = neg_ret_xtor
      ; type_vars = []
      ; term_vars = [r]
      ; command = CutPos (ret_ty, Variable r, Variable k)
      }])
    else
      Variable k
  in
  let insta_dtor = Destructor (insta_xtor, [ty_arg], [cont_arg]) in
  (* Use MuLhsPos for positive return, MuLhsNeg for negative return *)
  if ret_is_pos then
    MuLhsPos (ret_ty, k, CutNeg (all_ty, t_term, insta_dtor))
  else
    MuLhsNeg (ret_ty, k, CutNeg (all_ty, t_term, insta_dtor))

(**
  Build a type abstraction:
    [{a:k} t] where t : B
    
  Since forall types are NEGATIVE (codata), we just build a cocase.
  The continuation k : prd codomain_ty is provided by the caller.
  We invoke k with the result via neg.ret if positive, or cut directly if negative.
*)
let build_type_abs (a: variable) (kind: kind) (ret_ty: tpe) (ret_is_pos: bool) (body: term) =
  let k = Ident.fresh () in
  let codomain_ty = if ret_is_pos then mk_neg ret_ty else ret_ty in
  let insta_xtor = Prim.all_insta a kind in
  let body_cmd =
    if ret_is_pos then
      (* k : prd ¬[B], invoke with neg.ret(body) *)
      let neg_ret_xtor =
        { Prim.neg_ret with
          quantified = []
        ; parameters = [Lhs ret_ty]
        ; parent_arguments = [ret_ty]
        }
      in
      let invoker = Destructor (neg_ret_xtor, [], [body]) in
      CutNeg (codomain_ty, Variable k, invoker)
    else
      (* k : prd [B] (negative type), cut properly *)
      CutNeg (ret_ty, Variable k, body)
  in
  (* Type abstraction is just a cocase - forall type is negative *)
  New (Prim.all_sgn a kind, [{
    xtor = insta_xtor
  ; type_vars = [(a, kind)]
  ; term_vars = [k]
  ; command = body_cmd
  }])

(** Translates Lang terms to Kore producers (LHS terms) *)
let rec map_term (sgns: signatures) (trm: LTm.typed_term) : term =
  match trm with
  | LTm.TyTmVar (x, _) -> Variable x

  | LTm.TyTmLam (x, arg_ty, body, _ty) ->
    (* fun (x: A) => t *)
    let ret_ty_lang = LTm.get_type body in
    let arg_ty' = map_type arg_ty in
    let ret_ty' = map_type ret_ty_lang in
    let ret_is_pos = is_positive_type ret_ty_lang in
    let body' = map_term sgns body in
    build_lambda arg_ty' ret_ty' ret_is_pos x body'

  | LTm.TyTmAll ((a, k), body, _ty) ->
    (* {a: k} t *)
    let ret_ty_lang = LTm.get_type body in
    let kind = map_kinds k in
    let ret_ty' = map_type ret_ty_lang in
    let ret_is_pos = is_positive_type ret_ty_lang in
    let body' = map_term sgns body in
    build_type_abs a kind ret_ty' ret_is_pos body'

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
       Now codata types stay negative! The handler k receives:
       - For positive body: k : cns ¬[body_ty], send via ret
       - For negative body: k : cns [body_ty], send directly
    *)
    let codata_sgn = get_signature_of_new_type sgns ty in
    let branches = List.map (fun (xtor, type_vars, term_vars, body) ->
      let body_ty_lang = LTm.get_type body in
      let body' = map_term sgns body in
      let body_ty' = map_type body_ty_lang in
      let body_is_pos = is_positive_type body_ty_lang in
      let k = Ident.fresh () in
      let xtor' = map_xtor sgns xtor in
      let type_vars_with_kinds =
        List.map2 (fun v (_, knd) -> (v, map_kinds knd)
        ) type_vars xtor.LTy.quantified
      in
      let codomain_ty = if body_is_pos then mk_neg body_ty' else body_ty' in
      let body_cmd =
        if body_is_pos then
          (* k : prd ¬B, invoke with neg.ret(body) 
             ⟨k | ret(body)⟩ *)
          let neg_ret_xtor =
            { Prim.neg_ret with
              quantified = []
            ; parameters = [Lhs body_ty']
            ; parent_arguments = [body_ty']
            }
          in
          let invoker = Destructor (neg_ret_xtor, [], [body']) in
          CutNeg (codomain_ty, Variable k, invoker)
        else
          (* k : prd B (negative type), cut: ⟨k | body⟩ *)
          CutNeg (body_ty', Variable k, body')
      in
      { xtor = xtor'
      ; type_vars = type_vars_with_kinds
      ; term_vars = term_vars @ [k]
      ; command = body_cmd
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
        let ret_is_pos = is_positive_type ret_ty in
        let kind = get_forall_kind t_ty in
        let t' = build_inst kind (map_type ty) (map_type ret_ty) ret_is_pos t in
        apply_args t' ret_ty rest_tys []
      | tys, arg :: rest_args ->
        (* First consume all type args, then term args *)
        let t', t_ty' = 
          List.fold_left (fun (t, ty) ty_arg ->
            let ret_ty = instantiate_forall ty ty_arg in
            let ret_is_pos = is_positive_type ret_ty in
            let kind = get_forall_kind ty in
            (build_inst kind (map_type ty_arg) (map_type ret_ty) ret_is_pos t, ret_ty)
          ) (t, t_ty) tys
        in
        let arg_ty, ret_ty = get_fun_arg_ret t_ty' in
        let ret_is_pos = is_positive_type ret_ty in
        let arg' = map_term sgns arg in
        let t'' = build_app (map_type arg_ty) (map_type ret_ty) ret_is_pos t' arg' in
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
    (* Compute the inner type - a chain of functions ending in ret_ty *)
    let final_ret_ty = get_return_type sym_ty in
    let inner_ty_lang = 
      List.fold_right (fun t acc -> LTy.TyFun (t, acc)) rest_tys final_ret_ty
    in
    let inner_ty = map_type inner_ty_lang in
    let inner_is_pos = is_positive_type inner_ty_lang in
    build_lambda arg_ty' inner_ty inner_is_pos x inner

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
    (* Compute inner type - chain of functions ending in result_ty *)
    let inner_ty_lang =
      List.fold_right (fun t acc -> LTy.TyFun (t, acc)) rest_tys result_ty
    in
    let inner_ty = map_type inner_ty_lang in
    let inner_is_pos = is_positive_type inner_ty_lang in
    build_lambda arg_ty' inner_ty inner_is_pos x inner

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
    let ret_is_pos = is_positive_type result_ty in
    let xtor' = map_xtor sgns dtor in
    let tys = List.map map_type ty_args in
    let args = List.map (map_term sgns) rest in
    let k = Ident.fresh () in
    let f = Ident.fresh () in
    let inner_ty = TyNeg (get_codata_signature sgns self_ty) in
    (* Build continuation argument based on result polarity *)
    let cont_arg =
      if ret_is_pos then
        (* cocase{ret(r) => ⟨r|k⟩} : prd ¬[ret_ty] *)
        let r = Ident.fresh () in
        New (Prim.neg_sgn, [{
          xtor = mk_ret_xtor ret_ty'
        ; type_vars = []
        ; term_vars = [r]
        ; command = CutPos (ret_ty', Variable r, Variable k)
        }])
      else
        Variable k
    in
    let dtor_term = Destructor (xtor', tys, args @ [cont_arg]) in
    (* μk. ⟨self | case{close(f) ⇒ ⟨f | D(args, cont)⟩}⟩ *)
    MuLhsPos (ret_ty', k,
      CutPos (self_ty', self',
        Match (Prim.raise_sgn, [{
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