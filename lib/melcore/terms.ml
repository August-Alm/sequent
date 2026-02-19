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
  | TypedCtor of sym * sym * typed_term list * typ
  | TypedDtor of sym * sym * typed_term list * typ
  | TypedIfz of typed_term * typed_term * typed_term * typ

and typed_clause =
  sym * var list * var list * typed_term

let get_type (tm: typed_term) : typ =
  match tm with
    TypedInt _ -> Ext Int
  | TypedAdd (_, _) -> Ext Int
  | TypedVar (_, ty) -> ty
  | TypedSym (_, ty) -> ty
  | TypedApp (_, _, ty) -> ty
  | TypedIns (_, _, _, ty) -> ty
  | TypedLam (_, _, _, ty) -> ty
  | TypedAll (_, _, ty) -> ty
  | TypedLet (_, _, _, ty) -> ty
  | TypedMatch (_, _, ty) -> ty
  | TypedNew (_, ty) -> ty
  | TypedCtor (_, _, _, ty) -> ty
  | TypedDtor (_, _, _, ty) -> ty
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
  | TypedCtor (d, c, args, ty) ->
      TypedCtor (d, c, List.map go args, go_typ ty)
  | TypedDtor (d, c, args, ty) ->
      TypedDtor (d, c, List.map go args, go_typ ty)
  | TypedIfz (cond, then_br, else_br, ty) ->
      TypedIfz (go cond, go then_br, go else_br, go_typ ty)

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
  | Fun (dom, cod) ->
      (* Return user-visible (depolarized) types *)
      Ok (Types.depolarize_domain dom, Types.depolarize_codomain cod)
  | TMeta _ ->
      (* Unify with fresh function type *)
      let a = fresh_meta () in
      let b = fresh_meta () in
      (match unify t' (Fun (a, b)) sbs with
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
    and creating fresh metas for existentials *)
let instantiate_xtor (xtor: xtor) (type_args: typ list)
    : (Ident.t * typ) list * typ list * typ =
  (* Build substitution for quantified vars *)
  let quant_subst =
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
          (* Check type argument arity *)
          if List.length type_args <> List.length xtor.quantified then
            Error (TypeArgArityMismatch
              { xtor = xtor_name
              ; expected = List.length xtor.quantified
              ; got = List.length type_args })
          else if List.length term_args <> List.length xtor.argument_types then
            Error (XtorArityMismatch
              { xtor = xtor_name
              ; expected = List.length xtor.argument_types
              ; got = List.length term_args })
          else
            let _, inst_args, inst_main = instantiate_xtor xtor type_args in
            let* (typed_args, sbs) = check_args ctx sbs inst_args term_args in
            Ok (TypedCtor (dec_name, xtor_name, typed_args, inst_main), inst_main, sbs))

  | Dtor (dec_name, xtor_name, type_args, term_args) ->
      let* dec = lookup_dec ctx dec_name in
      (match find_xtor dec xtor_name with
      | None -> Error (UnboundXtor (dec_name, xtor_name))
      | Some xtor ->
          if List.length type_args <> List.length xtor.quantified then
            Error (TypeArgArityMismatch
              { xtor = xtor_name
              ; expected = List.length xtor.quantified
              ; got = List.length type_args })
          else if List.length term_args <> List.length xtor.argument_types then
            Error (XtorArityMismatch
              { xtor = xtor_name
              ; expected = List.length xtor.argument_types
              ; got = List.length term_args })
          else
            let _, inst_args, inst_main = instantiate_xtor xtor type_args in
            let* (typed_args, sbs) = check_args ctx sbs inst_args term_args in
            (* For codata destructors, the result is the "main" type (self type) *)
            Ok (TypedDtor (dec_name, xtor_name, typed_args, inst_main), inst_main, sbs))

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
      let covered = List.map (fun (xtor_name, _, _, _) -> xtor_name) branches in
      let missing = List.filter_map (fun (x: xtor) ->
        if List.exists (Path.equal x.name) covered then None else Some x.name
      ) dec.xtors in
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
            (* Check arity *)
            if List.length ty_vars <> List.length xtor.existentials then
              Error (TypeArgArityMismatch
                { xtor = xtor_name
                ; expected = List.length xtor.existentials
                ; got = List.length ty_vars })
            else if List.length tm_vars <> List.length xtor.argument_types then
              Error (XtorArityMismatch
                { xtor = xtor_name
                ; expected = List.length xtor.argument_types
                ; got = List.length tm_vars })
            else
              (* Instantiate with scrutinee type args *)
              let fresh_exist, inst_args, _ = instantiate_xtor xtor type_args in
              (* Rename existentials to user-provided names *)
              let exist_rename =
                List.fold_left2 (fun s (old_v, _) new_v ->
                  Ident.add old_v (TVar new_v) s
                ) Ident.emptytbl fresh_exist ty_vars
              in
              let inst_args' = List.map (apply_fresh_subst exist_rename) inst_args in
              (* Extend context with existentials and term vars *)
              let ctx' = extend_tyvars ctx
                (List.map2 (fun v (_, k) -> (v, k)) ty_vars xtor.existentials)
              in
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
            if List.length ty_vars <> List.length xtor.existentials then
              Error (TypeArgArityMismatch
                { xtor = xtor_name
                ; expected = List.length xtor.existentials
                ; got = List.length ty_vars })
            else if List.length tm_vars <> List.length xtor.argument_types then
              Error (XtorArityMismatch
                { xtor = xtor_name
                ; expected = List.length xtor.argument_types
                ; got = List.length tm_vars })
            else
              let fresh_exist, inst_args, inst_main =
                instantiate_xtor xtor type_args in
              let exist_rename =
                List.fold_left2 (fun s (old_v, _) new_v ->
                  Ident.add old_v (TVar new_v) s
                ) Ident.emptytbl fresh_exist ty_vars
              in
              let inst_args' =
                List.map (apply_fresh_subst exist_rename) inst_args in
              let inst_main' = apply_fresh_subst exist_rename inst_main in
              let ctx' = extend_tyvars ctx
                (List.map2 (fun v (_, k) -> (v, k)) ty_vars xtor.existentials)
              in
              let ctx' = extend_vars ctx'
                (List.combine tm_vars inst_args')
              in
              (* For codata, the body should produce the result type (inst_main') *)
              let* (body', _, sbs) = check ctx' sbs body inst_main' in
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
  let* (body', _, _) =
    check ctx Ident.emptytbl def.body def.return_type in
  Ok
    { name = def.name
    ; type_params = def.type_params
    ; term_params = def.term_params
    ; return_type = def.return_type
    ; body = body'
    }