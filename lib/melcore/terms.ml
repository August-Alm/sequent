(**
  module: Melcore.Terms
  description: Abstract syntax for the Melcore language.
*)

open Common.Identifiers
open Types.MelcoreBase
open Types.MelcoreTypes

type var = Ident.t
type sym = Path.t

type term =
  (* n *)
    Int of int
  (* t + u *)
  | Add of term * term
  (* t - u *)
  | Sub of term * term
  (* x *)
  | Var of var
  (* name; reference to top-level definition *)
  | Sym of sym
  (* t(u) *)
  | App of term * term
  (* t{ty} *)
  | Ins of term * typ
  (* fun x => t or fun(x: a) => t *)
  | Lam of var * (typ option) * term
  (* all {a: k} t *)
  | All of (var * typ) * term
  (* let x = t in u *)
  | Let of var * term * term
  (* match t with { branches } *)
  | Match of term * (branch list)
  (* new { branches } or new ty { branches }*)
  | New of (typ option) * (branch list)
  (* ctor{ai's}(ti's); type and term arguments;
    first path is type name, second path is ctor name *)
  | Ctor of sym * sym * (typ list) * (term list)
  (* dtor{ai's}(ti's); type and term arguments;
    first path is type name, second path is dtor name *)
  | Dtor of sym * sym * (typ list) * (term list)
  (* ifz t then u else v *)
  | Ifz of term * term * term

and branch =
  (* xtor(ti's) => t; type and term arguments, and return *)
  sym * var list * var list * term

(* Typed terms: AST with type annotations *)
type typed_term =
    TypedInt of int
  | TypedAdd of typed_term * typed_term
  | TypedSub of typed_term * typed_term
  | TypedVar of var * typ
  | TypedSym of sym * typ
  | TypedApp of typed_term * typed_term * typ
  (* trm, t, k, ty -- trm{t: k} : ty *)
  | TypedIns of typed_term * typ * typ * typ
  | TypedLam of var * typ * typed_term * typ
  (* (a, k), trm, ty -- Λa:k.trm : ty *)
  | TypedAll of (var * typ) * typed_term * typ
  | TypedLet of var * typed_term * typed_term * typ
  | TypedMatch of typed_term * typed_clause list * typ
  | TypedNew of typed_clause list * typ
  | TypedCtor of sym * sym * typ list * typed_term list * typ
  | TypedDtor of sym * sym * typ list * typed_term list * typ
  | TypedIfz of typed_term * typed_term * typed_term * typ

and typed_clause =
  sym * var list * var list * typed_term

let get_type (tm: typed_term) : typ =
  match tm with
    TypedInt _ -> Ext Int
  | TypedAdd (_, _) -> Ext Int
  | TypedSub (_, _) -> Ext Int
  | TypedVar (_, ty) -> ty
  | TypedSym (_, ty) -> ty
  | TypedApp (_, _, ty) -> ty
  | TypedIns (_, _, _, ty) -> ty
  | TypedLam (_, _, _, ty) -> ty
  | TypedAll (_, _, ty) -> ty
  | TypedLet (_, _, _, ty) -> ty
  | TypedMatch (_, _, ty) -> ty
  | TypedNew (_, ty) -> ty
  | TypedCtor (_, _, _, _, ty) -> ty
  | TypedDtor (_, _, _, _, ty) -> ty
  | TypedIfz (_, _, _, ty) -> ty

(** Substitute type variables (Unbound) in all type annotations of a typed term.
    Used for type-level beta reduction: (Λa. body){ty_arg} -> body[ty_arg/a] *)
let rec subst_type_in_typed_term (sbs: subst) (tm: typed_term) : typed_term =
  let go = subst_type_in_typed_term sbs in
  let go_typ = apply_fresh_subst sbs in
  let go_clause (xtor_name, ty_vars, tm_vars, body) =
    (xtor_name, ty_vars, tm_vars, go body)
  in
  match tm with
    TypedInt n -> TypedInt n
  | TypedAdd (t1, t2) -> TypedAdd (go t1, go t2)
  | TypedSub (t1, t2) -> TypedSub (go t1, go t2)
  | TypedVar (x, ty) -> TypedVar (x, go_typ ty)
  | TypedSym (path, ty) -> TypedSym (path, go_typ ty)
  | TypedApp (f, arg, ty) -> TypedApp (go f, go arg, go_typ ty)
  | TypedIns (t, ty_arg, k, ty) -> TypedIns (go t, go_typ ty_arg, k, go_typ ty)
  | TypedLam (x, a, body, ty) -> TypedLam (x, go_typ a, go body, go_typ ty)
  | TypedAll ((x, k), body, ty) -> TypedAll ((x, k), go body, go_typ ty)
  | TypedLet (x, t1, t2, ty) -> TypedLet (x, go t1, go t2, go_typ ty)
  | TypedMatch (scrut, branches, ty) ->
      TypedMatch (go scrut, List.map go_clause branches, go_typ ty)
  | TypedNew (branches, ty) ->
      TypedNew (List.map go_clause branches, go_typ ty)
  | TypedCtor (d, c, ty_args, args, ty) ->
      TypedCtor (d, c, List.map go_typ ty_args, List.map go args, go_typ ty)
  | TypedDtor (d, c, ty_args, args, ty) ->
      TypedDtor (d, c, List.map go_typ ty_args, List.map go args, go_typ ty)
  | TypedIfz (cond, then_br, else_br, ty) ->
      TypedIfz (go cond, go then_br, go else_br, go_typ ty)

(** Substitute a term variable with a typed term in a typed term.
    Used for term-level beta reduction: (λx. body) arg -> body[arg/x] *)
let rec subst_term_in_typed_term (x: Ident.t) (replacement: typed_term) (tm: typed_term) : typed_term =
  let go = subst_term_in_typed_term x replacement in
  let go_clause (xtor_name, ty_vars, tm_vars, body) =
    (* Don't substitute if x is shadowed by a term binding *)
    if List.exists (Ident.equal x) tm_vars then
      (xtor_name, ty_vars, tm_vars, body)
    else
      (xtor_name, ty_vars, tm_vars, go body)
  in
  match tm with
    TypedInt n -> TypedInt n
  | TypedAdd (t1, t2) -> TypedAdd (go t1, go t2)
  | TypedSub (t1, t2) -> TypedSub (go t1, go t2)
  | TypedVar (y, ty) -> 
      if Ident.equal x y then replacement else TypedVar (y, ty)
  | TypedSym (path, ty) -> TypedSym (path, ty)
  | TypedApp (f, arg, ty) -> TypedApp (go f, go arg, ty)
  | TypedIns (t, ty_arg, k, ty) -> TypedIns (go t, ty_arg, k, ty)
  | TypedLam (y, a, body, ty) -> 
      if Ident.equal x y then tm  (* x is shadowed *)
      else TypedLam (y, a, go body, ty)
  | TypedAll ((a, k), body, ty) -> TypedAll ((a, k), go body, ty)
  | TypedLet (y, t1, t2, ty) ->
      let t1' = go t1 in
      if Ident.equal x y then TypedLet (y, t1', t2, ty)  (* x is shadowed in t2 *)
      else TypedLet (y, t1', go t2, ty)
  | TypedMatch (scrut, branches, ty) ->
      TypedMatch (go scrut, List.map go_clause branches, ty)
  | TypedNew (branches, ty) ->
      TypedNew (List.map go_clause branches, ty)
  | TypedCtor (d, c, ty_args, args, ty) ->
      TypedCtor (d, c, ty_args, List.map go args, ty)
  | TypedDtor (d, c, ty_args, args, ty) ->
      TypedDtor (d, c, ty_args, List.map go args, ty)
  | TypedIfz (cond, then_br, else_br, ty) ->
      TypedIfz (go cond, go then_br, go else_br, ty)

(** Normalize a typed term:
    - Beta-reduce term applications to weak head normal form (WHNF)
    - Strongly reduce type instantiations (recurse under all binders)
    - Inline let-bound values (lambdas, foralls, ints)
    
    WHNF means we reduce until the head is not a redex, but don't reduce
    under term-level binders (lambdas). Type instantiations are reduced
    strongly because they don't have computational content.
*)
let rec normalize (tm: typed_term) : typed_term =
  (* First, normalize the head to expose any redexes *)
  match tm with
  (* Type instantiation: always reduce strongly *)
  | TypedIns (f, ty_arg, k, result_ty) ->
      let f' = normalize f in
      (match f' with
      | TypedAll ((tv, _k'), body, _forall_ty) ->
          (* (Λa. body){ty_arg} → body[ty_arg/a], then continue normalizing *)
          let sbs = Ident.add tv ty_arg Ident.emptytbl in
          let reduced = subst_type_in_typed_term sbs body in
          normalize reduced
      (* Expose redex: ((λx. body) arg){ty} → first beta-reduce *)
      | TypedApp (TypedLam (x, _a, lam_body, _fun_ty), arg, _app_ty) ->
          let reduced = subst_term_in_typed_term x arg lam_body in
          normalize (TypedIns (reduced, ty_arg, k, result_ty))
      | _ ->
          (* Can't reduce further, but normalize under Ins for strong reduction *)
          TypedIns (f', ty_arg, k, result_ty))
  
  (* Term application: reduce to WHNF *)
  | TypedApp (f, arg, result_ty) ->
      let f' = normalize f in
      (match f' with
      | TypedLam (x, _a, body, _fun_ty) ->
          (* (λx. body) arg → body[arg/x], then continue normalizing *)
          let reduced = subst_term_in_typed_term x arg body in
          normalize reduced
      (* Expose redex: (Λa. body){ty} arg → first type-instantiate *)
      | TypedIns (TypedAll ((tv, _k'), body, _forall_ty), ty_arg, _, _) ->
          let sbs = Ident.add tv ty_arg Ident.emptytbl in
          let inst_body = subst_type_in_typed_term sbs body in
          normalize (TypedApp (inst_body, arg, result_ty))
      | _ ->
          (* Can't reduce head, return with normalized function *)
          TypedApp (f', arg, result_ty))
  
  (* Let: inline values to expose redexes *)
  | TypedLet (x, t1, t2, ty) ->
      let t1' = normalize t1 in
      (match t1' with
      | TypedLam _ | TypedAll _ | TypedInt _ ->
          (* Inline value and continue normalizing *)
          let inlined = subst_term_in_typed_term x t1' t2 in
          normalize inlined
      | _ ->
          (* Can't inline, just return with normalized bound term *)
          TypedLet (x, t1', t2, ty))
  
  (* For TypedAll, recurse into body for strong type reduction *)
  | TypedAll ((a, k), body, ty) ->
      TypedAll ((a, k), normalize body, ty)
  
  (* Lambda: don't reduce under binder for WHNF, but do normalize type instantiations *)
  | TypedLam (x, a, body, ty) ->
      (* Only normalize type-level stuff in body, not full reduction *)
      TypedLam (x, a, normalize_types_only body, ty)
  
  (* Other forms: already in WHNF, but normalize subterms for type instantiations *)
  | TypedInt _ -> tm
  | TypedVar _ -> tm
  | TypedSym _ -> tm
  | TypedAdd (t1, t2) -> TypedAdd (normalize t1, normalize t2)
  | TypedSub (t1, t2) -> TypedSub (normalize t1, normalize t2)
  | TypedMatch (scrut, branches, ty) ->
      TypedMatch (normalize scrut, List.map normalize_clause branches, ty)
  | TypedNew (branches, ty) ->
      TypedNew (List.map normalize_clause branches, ty)
  | TypedCtor (d, c, ty_args, args, ty) ->
      TypedCtor (d, c, ty_args, List.map normalize args, ty)
  | TypedDtor (d, c, ty_args, args, ty) ->
      TypedDtor (d, c, ty_args, List.map normalize args, ty)
  | TypedIfz (cond, then_br, else_br, ty) ->
      TypedIfz (normalize cond, normalize then_br, normalize else_br, ty)

and normalize_clause (xtor_name, ty_vars, tm_vars, body) =
  (xtor_name, ty_vars, tm_vars, normalize body)

(** Normalize only type instantiations, not term applications.
    Used under lambdas where we want strong type reduction but WHNF for terms. *)
and normalize_types_only (tm: typed_term) : typed_term =
  match tm with
  | TypedIns (f, ty_arg, k, result_ty) ->
      let f' = normalize_types_only f in
      (match f' with
      | TypedAll ((tv, _k'), body, _forall_ty) ->
          let sbs = Ident.add tv ty_arg Ident.emptytbl in
          let reduced = subst_type_in_typed_term sbs body in
          normalize_types_only reduced
      | _ -> TypedIns (f', ty_arg, k, result_ty))
  | TypedAll ((a, k), body, ty) ->
      TypedAll ((a, k), normalize_types_only body, ty)
  | TypedLam (x, a, body, ty) ->
      TypedLam (x, a, normalize_types_only body, ty)
  | TypedApp (f, arg, ty) ->
      TypedApp (normalize_types_only f, normalize_types_only arg, ty)
  | TypedLet (x, t1, t2, ty) ->
      TypedLet (x, normalize_types_only t1, normalize_types_only t2, ty)
  | TypedAdd (t1, t2) ->
      TypedAdd (normalize_types_only t1, normalize_types_only t2)
  | TypedSub (t1, t2) ->
      TypedSub (normalize_types_only t1, normalize_types_only t2)
  | TypedMatch (scrut, branches, ty) ->
      TypedMatch (normalize_types_only scrut, 
        List.map (fun (x, tv, tm, b) -> (x, tv, tm, normalize_types_only b)) branches, ty)
  | TypedNew (branches, ty) ->
      TypedNew (List.map (fun (x, tv, tm, b) -> (x, tv, tm, normalize_types_only b)) branches, ty)
  | TypedCtor (d, c, ty_args, args, ty) ->
      TypedCtor (d, c, ty_args, List.map normalize_types_only args, ty)
  | TypedDtor (d, c, ty_args, args, ty) ->
      TypedDtor (d, c, ty_args, List.map normalize_types_only args, ty)
  | TypedIfz (cond, then_br, else_br, ty) ->
      TypedIfz (normalize_types_only cond, normalize_types_only then_br, 
        normalize_types_only else_br, ty)
  | TypedInt _ | TypedVar _ | TypedSym _ -> tm

type term_def =
  { name: sym
  ; type_params: (var * typ) list  (* type parameters with their kinds *)
  ; term_params: (var * typ) list  (* term parameters with their types *)
  ; return_type: typ
  ; body: term
  }

type typed_term_def =
  { name: sym
  ; type_params: (var * typ) list
  ; term_params: (var * typ) list
  ; return_type: typ
  ; body: typed_term
  }

type definitions = term_def Path.tbl
type typed_definitions = typed_term_def Path.tbl

(* Type checking context *)
type tc_context =
  { tyctx: context           (* Type-level context from MelcoreTypes *)
  ; term_vars: typ Ident.tbl (* Term variable types *)
  ; defs: definitions        (* Top-level definitions *)
  }

(* Create an initial tc_context from type declarations and term definitions *)
let make_tc_context (type_defs: dec list) (term_defs: definitions) : tc_context =
  (* Build type-level context with declarations *)
  let tyctx = List.fold_left (fun ctx (dec: dec) ->
    { ctx with decs = Path.add dec.name dec ctx.decs }
  ) empty_context type_defs in
  { tyctx; term_vars = Ident.emptytbl; defs = term_defs }

(* ========================================================================= *)
(* Type Checking Errors                                                      *)
(* ========================================================================= *)

type check_error =
    UnboundVariable of var
  | UnboundSymbol of sym
  | UnboundDeclaration of sym
  | UnboundXtor of sym * sym
  | TypeMismatch of { expected: typ; actual: typ }
  | ExpectedFun of typ
  | ExpectedForall of typ
  | ExpectedData of typ
  | ExpectedCodata of typ
  | XtorArityMismatch of { xtor: sym; expected: int; got: int }
  | TypeArgArityMismatch of { xtor: sym; expected: int; got: int }
  | NonExhaustive of { dec: sym; missing: sym list }
  | UnificationFailed of typ * typ
  | KindError of kind_error

let ( let* ) = Result.bind

(* ========================================================================= *)
(* Context Helpers                                                           *)
(* ========================================================================= *)

let lookup_var (ctx: tc_context) (v: var) : (typ, check_error) result =
  match Ident.find_opt v ctx.term_vars with
    Some t -> Ok t | None -> Error (UnboundVariable v)

let extend_var (ctx: tc_context) (v: var) (t: typ) : tc_context =
  { ctx with term_vars = Ident.add v t ctx.term_vars }

let extend_vars (ctx: tc_context) (bindings: (var * typ) list) : tc_context =
  List.fold_left (fun ctx (v, t) -> extend_var ctx v t) ctx bindings

let extend_tyvar (ctx: tc_context) (v: var) (k: typ) : tc_context =
  { ctx with tyctx = { ctx.tyctx with typ_vars = Ident.add v k ctx.tyctx.typ_vars } }

let extend_tyvars (ctx: tc_context) (bindings: (var * typ) list) : tc_context =
  List.fold_left (fun ctx (v, k) -> extend_tyvar ctx v k) ctx bindings

let lookup_def (ctx: tc_context) (p: Path.t) : (term_def, check_error) result =
  match Path.find_opt p ctx.defs with
    Some d -> Ok d | None -> Error (UnboundSymbol p)

let lookup_dec (ctx: tc_context) (p: Path.t) : (dec, check_error) result =
  match Path.find_opt p ctx.tyctx.decs with
    Some d -> Ok d | None -> Error (UnboundDeclaration p)

let find_xtor (dec: dec) (xtor_name: Path.t) : xtor option =
  List.find_opt (fun (x: xtor) -> Path.equal x.name xtor_name) dec.xtors

(* ========================================================================= *)
(* Fresh Variables and Unification                                           *)
(* ========================================================================= *)

(** Create a fresh type metavariable *)
let fresh_meta () : typ = TMeta (Ident.fresh ())

(** Unify two types, returning updated substitution or error *)
let unify_or_error
    (t1: typ) (t2: typ) (sbs: subst) : (subst, check_error) result =
  match unify t1 t2 sbs with
    Some sbs' -> Ok sbs' | None -> Error (UnificationFailed (t1, t2))

(* ========================================================================= *)
(* Type Extraction Helpers                                                   *)
(* ========================================================================= *)

(** Extract function domain and codomain, with polarity handling *)
let expect_fun (sbs: subst) (t: typ) : (typ * typ, check_error) result =
  let t' = apply_subst sbs t in
  match t' with
  | Sgn (s, [dom; cod]) when Path.equal s Common.Types.Prim.fun_sym ->
      (* Return user-visible (depolarized) types *)
      Ok (Types.depolarize_domain dom, Types.depolarize_codomain cod)
  | TMeta _ ->
      (* Unify with fresh function type *)
      let a = fresh_meta () in
      let b = fresh_meta () in
      (match unify t' (fun_sgn a b) sbs with
        Some _ -> Ok (a, b) | None -> Error (ExpectedFun t'))
  | _ -> Error (ExpectedFun t')

(** Extract forall binder and body, depolarizing the body *)
let expect_forall (sbs: subst) (t: typ)
    : (Ident.t * typ * typ, check_error) result =
  let t' = apply_subst sbs t in
  match t' with
  | Forall (x, k, body) -> Ok (x, k, Types.depolarize_codomain body)
  | _ -> Error (ExpectedForall t')

(** Check that a type is a data type (positive polarity) *)
let expect_data (ctx: tc_context) (sbs: subst) (t: typ)
    : (dec * typ list, check_error) result =
  let t' = apply_subst sbs t in
  match t' with
  | Sgn (name, args) ->
      let* dec = lookup_dec ctx name in
      if dec.polarity = Pos then Ok (dec, args)
      else Error (ExpectedData t')
  | _ -> Error (ExpectedData t')

(** Check that a type is a codata type (negative polarity) *)
let expect_codata (ctx: tc_context) (sbs: subst) (t: typ)
    : (dec * typ list, check_error) result =
  let t' = apply_subst sbs t in
  match t' with
  | Sgn (name, args) ->
      let* dec = lookup_dec ctx name in
      if dec.polarity = Neg then Ok (dec, args)
      else Error (ExpectedCodata t')
  | _ -> Error (ExpectedCodata t')

(* ========================================================================= *)
(* Xtor Instantiation                                                        *)
(* ========================================================================= *)

(** Instantiate an xtor by substituting type arguments for quantified vars
    and creating fresh metas for existentials.
    
    For construction: type_args should have same length as xtor.quantified.
    For pattern matching: pass empty type_args to freshen quantified vars. *)
let instantiate_xtor (xtor: xtor) (type_args: typ list)
    : (Ident.t * typ) list * typ list * typ =
  (* Build substitution for quantified vars *)
  let quant_subst =
    if type_args = [] && xtor.quantified <> [] then
      (* Pattern matching mode: freshen quantified vars as metas *)
      let _, subst = freshen_meta xtor.quantified in
      subst
    else
      List.fold_left2 (fun s (v, _) arg -> Ident.add v arg s)
        Ident.emptytbl xtor.quantified type_args
  in
  (* Freshen existentials *)
  let fresh_exist, exist_subst = freshen_meta xtor.existentials in
  (* Combine substitutions *)
  let combined = Ident.join quant_subst exist_subst in
  (* Apply to argument types and main *)
  let inst_args = List.map (apply_fresh_subst combined) xtor.argument_types in
  let inst_main = apply_fresh_subst combined xtor.main in
  (fresh_exist, inst_args, inst_main)

(** Instantiate an xtor for destructor calls, where type_args includes
    both quantified and existential type arguments.
    Returns (inst_args, inst_main) with all type params substituted. *)
let instantiate_dtor (xtor: xtor) (type_args: typ list)
    : typ list * typ =
  let n_quant = List.length xtor.quantified in
  let n_exist = List.length xtor.existentials in
  if List.length type_args <> n_quant + n_exist then
    failwith (Printf.sprintf "instantiate_dtor: expected %d type args, got %d"
      (n_quant + n_exist) (List.length type_args))
  else
    let quant_args = List.filteri (fun i _ -> i < n_quant) type_args in
    let exist_args = List.filteri (fun i _ -> i >= n_quant) type_args in
    let quant_subst = 
      List.fold_left2 (fun s (v, _) arg -> Ident.add v arg s)
        Ident.emptytbl xtor.quantified quant_args
    in
    let exist_subst =
      List.fold_left2 (fun s (v, _) arg -> Ident.add v arg s)
        quant_subst xtor.existentials exist_args
    in
    let inst_args = List.map (apply_fresh_subst exist_subst) xtor.argument_types in
    let inst_main = apply_fresh_subst exist_subst xtor.main in
    (inst_args, inst_main)

(** Instantiate an xtor for constructor calls, where type_args includes
    both quantified and existential type arguments.
    Returns (inst_args, inst_main) with all type params substituted. *)
let instantiate_ctor (xtor: xtor) (type_args: typ list)
    : typ list * typ =
  let n_quant = List.length xtor.quantified in
  let n_exist = List.length xtor.existentials in
  if List.length type_args <> n_quant + n_exist then
    failwith (Printf.sprintf "instantiate_ctor: expected %d type args, got %d"
      (n_quant + n_exist) (List.length type_args))
  else
    let quant_args = List.filteri (fun i _ -> i < n_quant) type_args in
    let exist_args = List.filteri (fun i _ -> i >= n_quant) type_args in
    let quant_subst = 
      List.fold_left2 (fun s (v, _) arg -> Ident.add v arg s)
        Ident.emptytbl xtor.quantified quant_args
    in
    let exist_subst =
      List.fold_left2 (fun s (v, _) arg -> Ident.add v arg s)
        quant_subst xtor.existentials exist_args
    in
    let inst_args = List.map (apply_fresh_subst exist_subst) xtor.argument_types in
    let inst_main = apply_fresh_subst exist_subst xtor.main in
    (inst_args, inst_main)

(* ========================================================================= *)
(* Bidirectional Type Inference                                              *)
(* ========================================================================= *)

(** Infer the type of a term, returning (typed_term, type, substitution) *)
let rec infer (ctx: tc_context) (sbs: subst) (tm: term)
    : (typed_term * typ * subst, check_error) result =
  match tm with
  | Int n -> Ok (TypedInt n, Ext Int, sbs)

  | Add (t, u) ->
      let* (t', _, sbs) = check ctx sbs t (Ext Int) in
      let* (u', _, sbs) = check ctx sbs u (Ext Int) in
      Ok (TypedAdd (t', u'), Ext Int, sbs)

  | Sub (t, u) ->
      let* (t', _, sbs) = check ctx sbs t (Ext Int) in
      let* (u', _, sbs) = check ctx sbs u (Ext Int) in
      Ok (TypedSub (t', u'), Ext Int, sbs)

  | Ifz (cond, then_branch, else_branch) ->
      let* (cond', _, sbs) = check ctx sbs cond (Ext Int) in
      let* (then', then_ty, sbs) = infer ctx sbs then_branch in
      let* (else', _, sbs) = check ctx sbs else_branch then_ty in
      Ok (TypedIfz (cond', then', else', then_ty), then_ty, sbs)

  | Var x ->
      let* ty = lookup_var ctx x in
      Ok (TypedVar (x, ty), ty, sbs)

  | Sym p ->
      let* def = lookup_def ctx p in
      (* Build polymorphic type: ∀a1..an. t1 -> ... -> tm -> ret *)
      let base_ty =
        List.fold_right (fun (_, arg_ty) acc ->
          Types.mk_fun ctx.tyctx arg_ty acc
        ) def.term_params def.return_type
      in
      let ty =
        List.fold_right (fun (v, k) acc ->
          Types.mk_forall ctx.tyctx v k acc
        ) def.type_params base_ty
      in
      Ok (TypedSym (p, ty), ty, sbs)

  | App (f, arg) ->
      let* (f', f_ty, sbs) = infer ctx sbs f in
      let* (dom, cod) = expect_fun sbs f_ty in
      let* (arg', _, sbs) = check ctx sbs arg dom in
      Ok (TypedApp (f', arg', cod), cod, sbs)

  | Ins (t, ty_arg) ->
      let* (t', t_ty, sbs) = infer ctx sbs t in
      let* (x, k, body) = expect_forall sbs t_ty in
      (* Kind check the type argument *)
      let* () =
        match check_kind ctx.tyctx ty_arg k with
          Ok () -> Ok ()
        | Error e -> Error (KindError e)
      in
      let result_ty =
        apply_fresh_subst (Ident.add x ty_arg Ident.emptytbl) body
      in
      Ok (TypedIns (t', ty_arg, k, result_ty), result_ty, sbs)

  | Lam (x, ann, body) ->
      let arg_ty =
        match ann with Some t -> t | None -> fresh_meta () in
      let ctx' = extend_var ctx x arg_ty in
      let* (body', body_ty, sbs) = infer ctx' sbs body in
      let fun_ty = Types.mk_fun ctx.tyctx arg_ty body_ty in
      Ok (TypedLam (x, arg_ty, body', fun_ty), fun_ty, sbs)

  | All ((x, k), body) ->
      let ctx' = extend_tyvar ctx x k in
      let* (body', body_ty, sbs) = infer ctx' sbs body in
      let all_ty = Types.mk_forall ctx.tyctx x k body_ty in
      Ok (TypedAll ((x, k), body', all_ty), all_ty, sbs)

  | Let (x, rhs, body) ->
      let* (rhs', rhs_ty, sbs) = infer ctx sbs rhs in
      let ctx' = extend_var ctx x rhs_ty in
      let* (body', body_ty, sbs) = infer ctx' sbs body in
      Ok (TypedLet (x, rhs', body', body_ty), body_ty, sbs)

  | Match (scrut, branches) ->
      let* (scrut', scrut_ty, sbs) = infer ctx sbs scrut in
      let* (dec, type_args) = expect_data ctx sbs scrut_ty in
      let result_ty = fresh_meta () in
      let* (typed_branches, sbs) =
        infer_match_branches ctx sbs dec type_args branches result_ty
      in
      (* GADT-aware exhaustiveness check using common/types.ml *)
      let covered = List.map (fun (xtor_name, _, _, _) -> xtor_name) branches in
      let tyctx = { ctx.tyctx with subst = sbs } in
      let missing = check_exhaustive tyctx dec type_args covered in
      let* () =
        if missing = [] then Ok ()
        else Error (NonExhaustive { dec = dec.name; missing })
      in
      Ok (TypedMatch (scrut', typed_branches, result_ty), result_ty, sbs)

  | New (ann, branches) ->
      let result_ty = match ann with Some t -> t | None -> fresh_meta () in
      let* (dec, type_args) = expect_codata ctx sbs result_ty in
      let* (typed_branches, sbs) =
        infer_new_branches ctx sbs dec type_args branches
      in
      (* Check exhaustiveness *)
      let covered = List.map (fun (xtor_name, _, _, _) ->
        xtor_name
      ) branches in
      let missing = List.filter_map (fun (x: xtor) ->
        if List.exists (Path.equal x.name) covered
        then None else Some x.name
      ) dec.xtors in
      let* () =
        if missing = [] then Ok ()
        else Error (NonExhaustive { dec = dec.name; missing })
      in
      Ok (TypedNew (typed_branches, result_ty), result_ty, sbs)

  | Ctor (dec_name, xtor_name, type_args, term_args) ->
      let* dec = lookup_dec ctx dec_name in
      (match find_xtor dec xtor_name with
      | None -> Error (UnboundXtor (dec_name, xtor_name))
      | Some xtor ->
          (* For constructor calls, type_args includes both quantified AND existential args *)
          let expected_ty_args = List.length xtor.quantified + List.length xtor.existentials in
          if List.length type_args <> expected_ty_args then
            Error (TypeArgArityMismatch
              { xtor = xtor_name
              ; expected = expected_ty_args
              ; got = List.length type_args })
          else if List.length term_args <> List.length xtor.argument_types then
            Error (XtorArityMismatch
              { xtor = xtor_name
              ; expected = List.length xtor.argument_types
              ; got = List.length term_args })
          else
            let inst_args, inst_main = instantiate_ctor xtor type_args in
            let* (typed_args, sbs) = check_args ctx sbs inst_args term_args in
            Ok (TypedCtor (dec_name, xtor_name, type_args, typed_args, inst_main), inst_main, sbs))

  | Dtor (dec_name, xtor_name, type_args, term_args) ->
      let* dec = lookup_dec ctx dec_name in
      (match find_xtor dec xtor_name with
      | None -> Error (UnboundXtor (dec_name, xtor_name))
      | Some xtor ->
          (* For destructor calls, type_args includes both quantified AND existential args *)
          let expected_ty_args = List.length xtor.quantified + List.length xtor.existentials in
          if List.length type_args <> expected_ty_args then
            Error (TypeArgArityMismatch
              { xtor = xtor_name
              ; expected = expected_ty_args
              ; got = List.length type_args })
          else
            (* For destructors:
               Surface: dtor: {qi's}{ei's} main -> argN -> ... -> arg0
               Domain:  argument_types = [arg0; ...; argN], main = "this" type
               AST:     Dtor(_, _, [qi's; ei's], [this; tN; ...; t1]) : arg0
               
               So term_args = [this; tN; ...; t1]
               Expected types = [main; argN; ...; arg1] = main :: (reverse (tail argument_types))
               Result type = arg0 = head of argument_types *)
            let inst_args, inst_main = instantiate_dtor xtor type_args in
            let (result_ty, regular_args) = match inst_args with
              | [] -> (inst_main, [])  (* No arguments - result is main *)
              | arg0 :: rest -> (arg0, List.rev rest)
            in
            let expected_term_types = inst_main :: regular_args in
            if List.length term_args <> List.length expected_term_types then
              Error (XtorArityMismatch
                { xtor = xtor_name
                ; expected = List.length expected_term_types
                ; got = List.length term_args })
            else
              let* (typed_args, sbs) = check_args ctx sbs expected_term_types term_args in
              Ok (TypedDtor (dec_name, xtor_name, type_args, typed_args, result_ty), result_ty, sbs))

(** Check a term against an expected type *)
and check (ctx: tc_context) (sbs: subst) (tm: term) (expected: typ)
    : (typed_term * typ * subst, check_error) result =
  match tm with
  | Lam (x, None, body) ->
      (* Check lambda against function type *)
      let* (dom, cod) = expect_fun sbs expected in
      let ctx' = extend_var ctx x dom in
      let* (body', _, sbs) = check ctx' sbs body cod in
      let fun_ty = Types.mk_fun ctx.tyctx dom cod in
      Ok (TypedLam (x, dom, body', fun_ty), fun_ty, sbs)

  | Match (scrut, branches) ->
      let* (scrut', scrut_ty, sbs) = infer ctx sbs scrut in
      let* (dec, type_args) = expect_data ctx sbs scrut_ty in
      let* (typed_branches, sbs) =
        infer_match_branches ctx sbs dec type_args branches expected
      in
      (* GADT-aware exhaustiveness check using common/types.ml *)
      let covered = List.map (fun (xtor_name, _, _, _) -> xtor_name) branches in
      let tyctx = { ctx.tyctx with subst = sbs } in
      let missing = check_exhaustive tyctx dec type_args covered in
      let* () =
        if missing = [] then Ok ()
        else Error (NonExhaustive { dec = dec.name; missing })
      in
      Ok (TypedMatch (scrut', typed_branches, expected), expected, sbs)

  | New (None, branches) ->
      let* (dec, type_args) = expect_codata ctx sbs expected in
      let* (typed_branches, sbs) =
        infer_new_branches ctx sbs dec type_args branches
      in
      let covered = List.map (fun (xtor_name, _, _, _) -> xtor_name) branches in
      let missing = List.filter_map (fun (x: xtor) ->
        if List.exists (Path.equal x.name) covered then None else Some x.name
      ) dec.xtors in
      let* () =
        if missing = [] then Ok ()
        else Error (NonExhaustive { dec = dec.name; missing })
      in
      Ok (TypedNew (typed_branches, expected), expected, sbs)

  | _ ->
      (* Fall back to inference and unification *)
      let* (tm', actual, sbs) = infer ctx sbs tm in
      let* sbs = unify_or_error expected actual sbs in
      Ok (tm', expected, sbs)

(** Check arguments against expected types *)
and check_args (ctx: tc_context) (sbs: subst) (expected: typ list) (args: term list)
    : (typed_term list * subst, check_error) result =
  let rec go sbs acc expected args =
    match expected, args with
    | [], [] -> Ok (List.rev acc, sbs)
    | exp :: exps, arg :: args ->
        let* (arg', _, sbs) = check ctx sbs arg exp in
        go sbs (arg' :: acc) exps args
    | _ -> failwith "check_args: arity mismatch"
  in
  go sbs [] expected args

(** Type check match branches (data elimination) *)
and infer_match_branches (ctx: tc_context) (sbs: subst) (dec: dec)
    (type_args: typ list) (branches: branch list) (result_ty: typ)
    : (typed_clause list * subst, check_error) result =
  let rec go sbs acc = function
    | [] -> Ok (List.rev acc, sbs)
    | (xtor_name, ty_vars, tm_vars, body) :: rest ->
        (match find_xtor dec xtor_name with
        | None -> Error (UnboundXtor (dec.name, xtor_name))
        | Some xtor ->
            (* Check arity: ty_vars bind ALL type params (quantified + existential) *)
            let expected_ty_vars = List.length xtor.quantified + List.length xtor.existentials in
            if List.length ty_vars <> expected_ty_vars then
              Error (TypeArgArityMismatch
                { xtor = xtor_name
                ; expected = expected_ty_vars
                ; got = List.length ty_vars })
            else if List.length tm_vars <> List.length xtor.argument_types then
              Error (XtorArityMismatch
                { xtor = xtor_name
                ; expected = List.length xtor.argument_types
                ; got = List.length tm_vars })
            else
              (* For pattern matching, we freshen all type params rather than
                 substituting with known types. Pass [] to trigger freshening. *)
              let fresh_exist, inst_args, inst_main = instantiate_xtor xtor [] in

              (* Unify the xtor's main type with the scrutinee type.
                 This determines what the quantified vars should be.
                 For GADT: lit's main is expr(int), which must match scrutinee expr(int).
                 For poly: ifthenelse's main is expr(?a), unified with expr(int) → ?a=int. *)
              let* sbs = unify_or_error inst_main (Sgn (dec.name, type_args)) sbs in
              (* Apply substitution to get instantiated argument types *)
              let inst_args' = List.map (apply_subst sbs) inst_args in
              
              (* Build type bindings for pattern type vars:
                 - Quantified vars: bind to the original declaration params 
                   (which get unified with scrutinee type args)
                 - Existential vars: bind to fresh metas *)
              let n_quant = List.length xtor.quantified in
              let quant_tyvars = List.filteri (fun i _ -> i < n_quant) ty_vars in
              let exist_tyvars = List.filteri (fun i _ -> i >= n_quant) ty_vars in
              
              (* Quantified type vars get their kinds from the xtor *)
              let quant_bindings = List.map2 (fun v (_, k) -> (v, k)) 
                quant_tyvars xtor.quantified in
              (* Existential type vars also get kinds, but their types are fresh metas *)
              let exist_bindings = List.map2 (fun v (_, k) -> (v, k))
                exist_tyvars xtor.existentials in
              
              let ctx' = extend_tyvars ctx (quant_bindings @ exist_bindings) in
              
              (* Add substitutions mapping pattern exist vars to fresh metas *)
              let sbs = List.fold_left2 (fun s pattern_var (fresh_var, _) ->
                Ident.add pattern_var (TVar fresh_var) s
              ) sbs exist_tyvars fresh_exist in
              
              let ctx' = extend_vars ctx'
                (List.combine tm_vars inst_args')
              in
              let* (body', _, sbs) = check ctx' sbs body result_ty in
              let clause = (xtor_name, ty_vars, tm_vars, body') in
              go sbs (clause :: acc) rest)
  in
  go sbs [] branches

(** Type check new/comatch branches (codata introduction) *)
and infer_new_branches (ctx: tc_context) (sbs: subst) (dec: dec)
    (type_args: typ list) (branches: branch list)
    : (typed_clause list * subst, check_error) result =
  let rec go sbs acc = function
    | [] -> Ok (List.rev acc, sbs)
    | (xtor_name, ty_vars, tm_vars, body) :: rest ->
        (match find_xtor dec xtor_name with
        | None -> Error (UnboundXtor (dec.name, xtor_name))
        | Some xtor ->
            (* For codata introduction (new/comatch):
               ty_vars bind BOTH quantified AND existential type params.
               
               For example, with foldable(d) and fold: {d}{r} foldable(d) -> algebra(d)(r) -> r,
               a new branch like { fold{e}{t}(alg) => ... } binds e to d (quantified)
               and t to r (existential). *)
            let total_arity = List.length xtor.quantified + List.length xtor.existentials in
            if ty_vars <> [] && List.length ty_vars <> total_arity then
              Error (TypeArgArityMismatch
                { xtor = xtor_name
                ; expected = total_arity
                ; got = List.length ty_vars })
            else
              (* Instantiate xtor with fresh metas for quantified vars *)
              let fresh_exist, inst_args, inst_main = instantiate_xtor xtor [] in
              (* Unify main type with the codata type being constructed.
                 This determines what the quantified vars should be.
                 For foldable: fold's main is foldable(?d), unified with foldable(e) → ?d=e *)
              let* sbs = unify_or_error inst_main (Sgn (dec.name, type_args)) sbs in
              let inst_args' = List.map (apply_subst sbs) inst_args in
              
              (* For codata destructors:
                 Surface: dtor: {qi's} main -> argN -> ... -> arg0
                 argument_types = [arg0; arg1; ...; argN]
                 - arg0 is the codomain (result type)
                 - [arg1; ...; argN] are extra parameters the branch binds *)
              let (result_ty, param_types) = match inst_args' with
                | [] -> (apply_subst sbs inst_main, [])  (* No arguments *)
                | arg0 :: rest -> (arg0, rest)
              in
              if List.length tm_vars <> List.length param_types then
                Error (XtorArityMismatch
                  { xtor = xtor_name
                  ; expected = List.length param_types
                  ; got = List.length tm_vars })
              else
                (* If ty_vars are provided, bind them to quantified + existential params *)
                let all_type_params = xtor.quantified @ xtor.existentials in
                let ctx' = if ty_vars <> [] then
                  extend_tyvars ctx
                    (List.map2 (fun v (_, k) -> (v, k)) ty_vars all_type_params)
                else 
                  (* Also bind the fresh existentials in context *)
                  extend_tyvars ctx fresh_exist
                in
                let ctx' = extend_vars ctx' (List.combine tm_vars param_types) in
                let* (body', _, sbs) = check ctx' sbs body result_ty in
                let clause = (xtor_name, ty_vars, tm_vars, body') in
                go sbs (clause :: acc) rest)
  in
  go sbs [] branches

(* ========================================================================= *)
(* Top-Level Checking                                                        *)
(* ========================================================================= *)

(** Infer type of a term *)
let infer_term (ctx: tc_context) (tm: term) : (typed_term * typ, check_error) result =
  let* (tm', ty, _) = infer ctx Ident.emptytbl tm in
  Ok (tm', ty)

(** Type check a definition *)
let check_definition (ctx: tc_context) (def: term_def)
    : (typed_term_def, check_error) result =
  (* Add type parameters to context *)
  let ctx = extend_tyvars ctx def.type_params in
  (* Add term parameters to context *)
  let ctx = extend_vars ctx def.term_params in
  (* Check body against declared return type *)
  let* (body', _, sbs) =
    check ctx Ident.emptytbl def.body def.return_type in
  (* Apply final substitution to resolve all meta-variables in types *)
  let body' = subst_type_in_typed_term sbs body' in
  Ok
    { name = def.name
    ; type_params = def.type_params
    ; term_params = def.term_params
    ; return_type = def.return_type
    ; body = body'
    }