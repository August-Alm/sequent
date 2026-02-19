(**
  module: Melcore.Terms
  description: Abstract syntax for the Melcore language.
*)

open Common.Identifiers
open Types.MelcoreBase
open Types.MelcoreTypes

type var = Ident.t

type term =
  (* n *)
    Int of int
  (* t + u *)
  | Add of term * term
  (* x *)
  | Var of var
  (* name *)
  | Sym of Path.t
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
  (* ctor{ai's}(ti's); type and term arguments *)
  | Ctor of xtor * (term list)
  (* dtor{ai's}(ti's); type and term arguments *)
  | Dtor of xtor * (term list)
  (* ifz t then u else v *)
  | Ifz of term * term * term

and branch =
  (* xtor(ti's) => t; type and term arguments, and return *)
  xtor * (var list) * term

(* Typed terms: AST with type annotations *)
type typed_term =
    TypedInt of int
  | TypedAdd of typed_term * typed_term
  | TypedVar of var * typ
  | TypedSym of Path.t * typ
  | TypedApp of typed_term * typed_term * typ
  | TypedIns of typed_term * typ * kind * typ
  | TypedLam of var * typ * typed_term * typ
  | TypedAll of (var * kind) * typed_term * typ
  | TypedLet of var * typed_term * typed_term * typ
  | TypedMatch of typed_term * typed_clause list * typ
  | TypedNew of typed_clause list * typ
  | TypedCtor of xtor * typed_term list * typ
  | TypedDtor of xtor * typed_term list * typ
  | TypedIfz of typed_term * typed_term * typed_term * typ

and typed_clause =
  xtor * var list * var list * typed_term

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
  | TypedCtor (_, _, ty) -> ty
  | TypedDtor (_, _, ty) -> ty
  | TypedIfz (_, _, _, ty) -> ty

(** Substitute type variables (Unbound) in all type annotations of a typed term.
    Used for type-level beta reduction: (Λa. body){ty_arg} -> body[ty_arg/a] *)
let rec subst_type_in_typed_term
    (ms: (Ident.t * typ) list) (tm: typed_term) : typed_term =
  let go = subst_type_in_typed_term ms in
  let go_typ = subst_unbound ms in
  let go_xtor (x: xtor) : xtor =
    {x with arguments = List.map go_typ x.arguments; main = go_typ x.main}
  in
  let go_clause (xtor, ty_vars, tm_vars, body) =
    (go_xtor xtor, ty_vars, tm_vars, go body)
  in
  match tm with
    TypedInt n -> TypedInt n
  | TypedAdd (t1, t2) -> TypedAdd (go t1, go t2)
  | TypedVar (x, ty) -> TypedVar (x, go_typ ty)
  | TypedSym (path, ty) -> TypedSym (path, go_typ ty)
  | TypedApp (f, arg, ty) ->
      TypedApp (go f, go arg, go_typ ty)
  | TypedIns (t, ty_arg, k, ty) -> TypedIns (go t, go_typ ty_arg, k, go_typ ty)
  | TypedLam (x, a, body, ty) -> TypedLam (x, go_typ a, go body, go_typ ty)
  | TypedAll ((x, k), body, ty) ->
      (* Filter out substitutions shadowed by this binder *)
      let ms' = List.filter (fun (id, _) -> not (Ident.equal id x)) ms in
      TypedAll ((x, k), subst_type_in_typed_term ms' body, go_typ ty)
  | TypedLet (x, t1, t2, ty) -> TypedLet (x, go t1, go t2, go_typ ty)
  | TypedMatch (scrut, branches, ty) ->
      TypedMatch (go scrut, List.map go_clause branches, go_typ ty)
  | TypedNew (branches, ty) ->
      TypedNew (List.map go_clause branches, go_typ ty)
  | TypedCtor (xtor, args, ty) ->
      TypedCtor (go_xtor xtor, List.map go args, go_typ ty)
  | TypedDtor (xtor, args, ty) ->
      TypedDtor (go_xtor xtor, List.map go args, go_typ ty)
  | TypedIfz (cond, then_br, else_br, ty) ->
      TypedIfz (go cond, go then_br, go else_br, go_typ ty)

type term_def =
  { name: Path.t
  ; type_args: (var * kind) list
  ; term_args: (var * typ) list
  ; return_type: typ
  ; body: term
  }

type typed_term_def =
  { name: Path.t
  ; type_args: (var * kind) list
  ; term_args: (var * typ) list
  ; return_type: typ
  ; body: typed_term
  }

type definitions = term_def Path.tbl

type typed_definitions = typed_term_def Path.tbl

type context =
  { kinds: kind Ident.tbl
  ; types: typ Ident.tbl
  }

type check_error =
    UnboundVariable of var
  | UnboundSymbol of Path.t
  | TypeMismatch of {expected: typ; actual: typ}
  | ExpectedData of typ  (* Type was expected to be a data type *)
  | ExpectedCode of typ  (* Type was expected to be a codata type *)
  | SignatureMismatch of sgn_typ * sgn_typ  (* Expected, actual *)
  | XtorNotInSignature of xtor * sgn_typ
  | NonExhaustive of xtor list  (* Missing branches for these reachable xtors *)
  | ArityMismatch of {xtor: xtor; expected: int; actual: int}
  | UnificationFailed of typ * typ

let lookup (ctx: context) (v: var) : (typ, check_error) result =
  match Ident.find_opt v ctx.types with
    Some ct -> Ok ct
  | None -> Error (UnboundVariable v)

let extend (ctx: context) (v: var) (ct: typ) : context =
  { ctx with types = Ident.add v ct ctx.types }

let extend_many (ctx: context) (bindings: (var * typ) list) : context =
  List.fold_left (fun ctx (v, ct) -> extend ctx v ct) ctx bindings

let extend_kind (ctx: context) (v: var) (k: kind) : context =
  { ctx with kinds = Ident.add v k ctx.kinds }

let extend_kinds (ctx: context) (bindings: (var * kind) list) : context =
  List.fold_left (fun ctx (v, k) -> extend_kind ctx v k) ctx bindings

let ( let* ) = Result.bind

type check_result = (typed_term * typ, check_error) result

(** Fresh type variable for inference *)
let fresh_var (name: string) : typ =
  Var (ref (Unbound (Ident.mk name)))

let fresh () : typ = Var (ref (Unbound (Ident.fresh ())))

(** Unify two types, returning error on failure *)
let unify_or_error (kctx: kind Ident.tbl) (t1: typ) (t2: typ) (env: solving_env) 
    : (solving_env, check_error) result =
  match unify kctx t1 t2 env with
    Some env' -> Ok env'
  | None -> Error (UnificationFailed (t1, t2))

(** Extract the signature from a data type in WHNF *)
let expect_data (kctx: kind Ident.tbl) (env: solving_env) (t: typ) 
    : (sgn_typ, check_error) result =
  match whnf kctx env.subs t with
    Data sgn -> Ok sgn
  | t' -> Error (ExpectedData t')

(** Extract the signature from a codata type in WHNF *)
let expect_code (kctx: kind Ident.tbl) (env: solving_env) (t: typ) 
    : (sgn_typ, check_error) result =
  match whnf kctx env.subs t with
    Code sgn -> Ok sgn
  | t' -> Error (ExpectedCode t')

(** Extract function domain and codomain *)
let expect_fun (kctx: kind Ident.tbl) (env: solving_env) (t: typ) 
    : (typ * typ, check_error) result =
  match whnf kctx env.subs t with
    Fun (a, b) -> Ok (a, b)
  | t' -> 
      (* Try unifying with fresh function type *)
      let a = fresh () in
      let b = fresh () in
      match unify kctx t' (Fun (a, b)) env with
        Some _ -> Ok (a, b)
      | None -> Error (TypeMismatch
          { expected = Types.Fun (fresh (), fresh ())
          ; actual = t'
          })

(** Extract forall binder and body *)
let expect_all (kctx: kind Ident.tbl) (env: solving_env) (t: typ) 
    : ((Ident.t * kind) * typ, check_error) result =
  match whnf kctx env.subs t with
    All (binder, body) -> Ok (binder, body)
  | t' -> Error (TypeMismatch
      { expected = Types.All ((Ident.mk "?", Star), fresh ())
      ; actual = t'
      })

(** Find an xtor in a signature by name *)
let find_xtor (x: Types.xtor) (sgn: Types.sgn_typ) : (Types.xtor, check_error) result =
  match List.find_opt (fun (x': Types.xtor) -> 
      Path.equal x.name x'.name
    ) sgn.xtors
  with
    Some x' -> Ok x'
  | None -> Error (XtorNotInSignature (x, sgn))

(** Instantiate xtor's existentials with fresh variables *)
let instantiate_xtor_existentials (x: xtor) : (Ident.t * typ) list * xtor =
  let fresh_existentials = List.map (fun (id, _) ->
    (id, fresh_var (Ident.name id))
  ) x.existentials in
  let x' = { x with
    arguments = List.map (subst_rigid fresh_existentials) x.arguments
  ; main = subst_rigid fresh_existentials x.main
  } in
  (fresh_existentials, x')

(** Bidirectional type inference.
    Returns (typed_term, typ) on success. *)
let rec infer (defs: definitions) (ctx: context) (env: solving_env) (tm: term) 
    : (typed_term * typ * solving_env, check_error) result =
  match tm with
    Int n -> Ok (TypedInt n, Ext Int, env)
  
  | Add (t, u) ->
      let* (t', _, env) = check defs ctx env t (Ext Int) in
      let* (u', _, env) = check defs ctx env u (Ext Int) in
      Ok (TypedAdd (t', u'), Ext Int, env)
  
  | Ifz (cond, then_branch, else_branch) ->
      let* (cond', _, env) = check defs ctx env cond (Ext Int) in
      let* (then', then_ty, env) = infer defs ctx env then_branch in
      let* (else', _, env) = check defs ctx env else_branch then_ty in
      Ok (TypedIfz (cond', then', else', then_ty), then_ty, env)
  
  | Var x ->
      let* ty = lookup ctx x in
      Ok (TypedVar (x, ty), ty, env)
  
  | Sym p ->
      (match Path.find_opt p defs with
      | Some def ->
          (* Build the polymorphic type from definition *)
          let ty = List.fold_right (fun (v, k) acc -> 
            Types.All ((v, k), acc)
          ) def.type_args (
            List.fold_right (fun (_, arg_ty) acc ->
              Types.Fun (arg_ty, acc)
            ) def.term_args def.return_type
          ) in
          Ok (TypedSym (p, ty), ty, env)
      | None -> Error (UnboundSymbol p))
  
  | App (f, arg) ->
      let* (f', f_ty, env) = infer defs ctx env f in
      let* (dom, cod) = expect_fun ctx.kinds env f_ty in
      let* (arg', _, env) = check defs ctx env arg dom in
      Ok (TypedApp (f', arg', cod), cod, env)
  
  | Ins (t, ty_arg) ->
      let* (t', t_ty, env) = infer defs ctx env t in
      let* ((x, k), body) = expect_all ctx.kinds env t_ty in
      (* Kind check the type argument *)
      let* () =
        match check_kind ctx.kinds ty_arg k with
          Ok () -> Ok ()
        | Error _ -> Error (TypeMismatch {expected = Rigid x; actual = ty_arg})
      in
      let result_ty = subst_rigid [(x, ty_arg)] body in
      Ok (TypedIns (t', ty_arg, k, result_ty), result_ty, env)
  
  | Lam (x, ann, body) ->
      let arg_ty = match ann with Some t -> t | None -> fresh () in
      let ctx' = extend ctx x arg_ty in
      let* (body', body_ty, env) = infer defs ctx' env body in
      let fun_ty = Types.Fun (arg_ty, body_ty) in
      Ok (TypedLam (x, arg_ty, body', fun_ty), fun_ty, env)
  
  | All ((x, k), body) ->
      let ctx' = extend_kind ctx x k in
      let* (body', body_ty, env) = infer defs ctx' env body in
      let all_ty = Types.All ((x, k), body_ty) in
      Ok (TypedAll ((x, k), body', all_ty), all_ty, env)
  
  | Let (x, rhs, body) ->
      let* (rhs', rhs_ty, env) = infer defs ctx env rhs in
      let ctx' = extend ctx x rhs_ty in
      let* (body', body_ty, env) = infer defs ctx' env body in
      Ok (TypedLet (x, rhs', body', body_ty), body_ty, env)
  
  | Match (scrut, branches) ->
      let* (scrut', scrut_ty, env) = infer defs ctx env scrut in
      let* sgn = expect_data ctx.kinds env scrut_ty in
      let result_ty = fresh () in
      let* (typed_branches, env) =
        infer_branches defs ctx env sgn branches result_ty
      in
      (* Check exhaustiveness *)
      let covered = List.map (fun ((x: Types.xtor), _, _) ->
        x.name
      ) branches in
      let missing = List.filter (fun (x: Types.xtor) -> 
        not (List.exists (Path.equal x.name) covered)
      ) sgn.xtors in
      let* () = if missing = [] then Ok () 
                else Error (NonExhaustive missing) in
      Ok (TypedMatch (scrut', typed_branches, result_ty), result_ty, env)
  
  | New (ann, branches) ->
      let result_ty = match ann with Some t -> t | None -> fresh () in
      let* sgn = expect_code ctx.kinds env result_ty in
      let* (typed_branches, env) = 
        infer_cobranches defs ctx env sgn branches result_ty in
      (* Check exhaustiveness *)
      let covered = List.map (fun ((x: Types.xtor), _, _) ->
        x.name
      ) branches in
      let missing = List.filter (fun (x: Types.xtor) -> 
        not (List.exists (Path.equal x.name) covered)
      ) sgn.xtors in
      let* () = if missing = [] then Ok () 
                else Error (NonExhaustive missing) in
      Ok (TypedNew (typed_branches, result_ty), result_ty, env)
  
  | Ctor (x, args) ->
      (* The xtor carries its signature info. x.main is the result type.
        x.arguments are the expected argument types.
        Partial application: if fewer args provided, result is a function. *)
      let (_exist_bindings, x_inst) = instantiate_xtor_existentials x in
      (* exist_bindings are existentials - packed, not exposed to caller *)
      let expected_arity = List.length x_inst.arguments in
      let actual_arity = List.length args in
      let* () =
        if actual_arity <= expected_arity then Ok ()
        else Error (ArityMismatch
          { xtor = x; expected = expected_arity; actual = actual_arity }) in
      (* Split arguments into provided and remaining *)
      let rec split_at n lst =
        if n <= 0 then ([], lst)
        else match lst with
            [] -> ([], [])
          | h :: t -> let (taken, rest) = split_at (n - 1) t in (h :: taken, rest)
      in
      let (provided_tys, remaining_tys) = split_at actual_arity x_inst.arguments in
      (* Check each provided argument against expected type *)
      let* (typed_args, _, env) = 
        infer_ctor_args defs ctx env provided_tys args in
      (* Build result type: if partial, wrap remaining args as function type *)
      let base_ty = whnf ctx.kinds env.subs x_inst.main in
      let result_ty = List.fold_right (fun arg_ty acc ->
        Types.Fun (arg_ty, acc)
      ) remaining_tys base_ty in
      Ok (TypedCtor (x, typed_args, result_ty), result_ty, env)
  
  | Dtor (x, args) ->
      (* For codata destruction: x is a destructor, last argument type is codomain.
        Partial application is supported. *)
      let (_exist_bindings, x_inst) = instantiate_xtor_existentials x in
      let all_args = x_inst.arguments in
      (* For codata, last argument is the codomain/result type *)
      let (regular_args, final_result) = match List.rev all_args with
          cod :: rev_rest -> (List.rev rev_rest, cod)
        | [] -> ([], x_inst.main)  (* No arguments - unusual *)
      in
      let expected_arity = List.length regular_args in
      let actual_arity = List.length args in
      let* () =
        if actual_arity <= expected_arity then Ok ()
        else Error (ArityMismatch
          { xtor = x
          ; expected = expected_arity
          ; actual = actual_arity
          })
      in
      (* Split into provided and remaining *)
      let rec split_at n lst =
        if n <= 0 then ([], lst)
        else match lst with
            [] -> ([], [])
          | h :: t -> let (taken, rest) = split_at (n - 1) t in (h :: taken, rest)
      in
      let (provided_tys, remaining_tys) = split_at actual_arity regular_args in
      let* (typed_args, _, env) = 
        infer_ctor_args defs ctx env provided_tys args in
      (* Build result type: remaining args + final result *)
      let result_ty = List.fold_right (fun arg_ty acc ->
        Types.Fun (arg_ty, acc)
      ) remaining_tys final_result in
      Ok (TypedDtor (x, typed_args, result_ty), result_ty, env)

(** Check a term against an expected type *)
and check
    (defs: definitions) (ctx: context) (env: solving_env)
    (tm: term) (expected: typ)
    : (typed_term * typ * solving_env, check_error) result =
  match tm with
    Lam (x, None, body) ->
      (* Check lambda against function type *)
      let* (dom, cod) = expect_fun ctx.kinds env expected in
      let ctx' = extend ctx x dom in
      let* (body', _, env) = check defs ctx' env body cod in
      let fun_ty = Types.Fun (dom, cod) in
      Ok (TypedLam (x, dom, body', fun_ty), fun_ty, env)
  
  | Match (scrut, branches) ->
      let* (scrut', scrut_ty, env) = infer defs ctx env scrut in
      let* sgn = expect_data ctx.kinds env scrut_ty in
      let* (typed_branches, env) = 
        infer_branches defs ctx env sgn branches expected
      in
      let covered = List.map (fun ((x: Types.xtor), _, _) ->
        x.name
      ) branches in
      let missing = List.filter (fun (x: Types.xtor) -> 
        not (List.exists (Path.equal x.name) covered)
      ) sgn.xtors in
      let* () = if missing = [] then Ok () 
                else Error (NonExhaustive missing) in
      Ok (TypedMatch (scrut', typed_branches, expected), expected, env)
  
  | New (None, branches) ->
      let* sgn = expect_code ctx.kinds env expected in
      let* (typed_branches, env) = 
        infer_cobranches defs ctx env sgn branches expected in
      let covered = List.map (fun ((x: Types.xtor), _, _) ->
        x.name
      ) branches in
      let missing = List.filter (fun (x: Types.xtor) -> 
        not (List.exists (Path.equal x.name) covered)
      ) sgn.xtors in
      let* () = if missing = [] then Ok () 
                else Error (NonExhaustive missing) in
      Ok (TypedNew (typed_branches, expected), expected, env)
  
  | _ ->
      (* Fall back to inference and unification *)
      let* (tm', actual, env) = infer defs ctx env tm in
      let* env = unify_or_error ctx.kinds expected actual env in
      Ok (tm', expected, env)

(** Type check branches of a match (data elimination) *)
and infer_branches (defs: definitions) (ctx: context) (env: solving_env) 
    (sgn: sgn_typ) (branches: branch list) (result_ty: typ)
    : (typed_clause list * solving_env, check_error) result =
  let rec go env acc = function
      [] -> Ok (List.rev acc, env)
    | (x, vars, body) :: rest ->
        let* x' = find_xtor x sgn in
        (* Instantiate existentials with fresh vars *)
        let (exist_bindings, x_inst) = instantiate_xtor_existentials x' in
        let exist_vars = List.map fst exist_bindings in
        (* Check arity of term variables *)
        let expected_arity = List.length x_inst.arguments in
        let actual_arity = List.length vars in
        let* () =
          if expected_arity = actual_arity then Ok ()
          else Error (ArityMismatch
            { xtor = x
            ; expected = expected_arity
            ; actual = actual_arity
          })
        in
        (* Bind term variables to argument types *)
        let bindings = List.combine vars x_inst.arguments in
        let ctx' = extend_many ctx bindings in
        (* Extend kind context with existentials *)
        let ctx' = extend_kinds ctx' x'.existentials in
        (* Check body against result type *)
        let* (body', _, env) = check defs ctx' env body result_ty in
        let clause = (x, exist_vars, vars, body') in
        go env (clause :: acc) rest
  in
  go env [] branches

(** Type check branches of a new (codata introduction) *)
and infer_cobranches (defs: definitions) (ctx: context) (env: solving_env) 
    (sgn: sgn_typ) (branches: branch list) (self_ty: typ)
    : (typed_clause list * solving_env, check_error) result =
  let rec go env acc = function
      [] -> Ok (List.rev acc, env)
    | (x, vars, body) :: rest ->
        let* x' = find_xtor x sgn in
        (* For codata, last argument is the codomain *)
        let (exist_bindings, x_inst) = instantiate_xtor_existentials x' in
        let exist_vars = List.map fst exist_bindings in
        let all_args = x_inst.arguments in
        let (regular_args, codomain) = match List.rev all_args with
            cod :: rev_rest -> (List.rev rev_rest, cod)
          | [] -> ([], self_ty)  (* No arguments means identity *)
        in
        let expected_arity = List.length regular_args in
        let actual_arity = List.length vars in
        let* () =
          if expected_arity = actual_arity then Ok ()
          else Error (ArityMismatch
            { xtor = x
            ; expected = expected_arity
            ; actual = actual_arity
            })
        in
        let bindings = List.combine vars regular_args in
        let ctx' = extend_many ctx bindings in
        let ctx' = extend_kinds ctx' x'.existentials in
        let* (body', _, env) = check defs ctx' env body codomain in
        let clause = (x, exist_vars, vars, body') in
        go env (clause :: acc) rest
  in
  go env [] branches

(** Infer types for constructor arguments *)
and infer_ctor_args (defs: definitions) (ctx: context) (env: solving_env)
    (expected_tys: typ list) (args: term list)
    : (typed_term list * typ list * solving_env, check_error) result =
  let rec go env typed_acc ty_acc expected args =
    match expected, args with
      [], [] -> Ok (List.rev typed_acc, List.rev ty_acc, env)
    | exp_ty :: exp_rest, arg :: arg_rest ->
        let* (arg', _, env) = check defs ctx env arg exp_ty in
        go env (arg' :: typed_acc) (exp_ty :: ty_acc) exp_rest arg_rest
    | _ -> failwith "infer_ctor_args: arity mismatch"  (* Should be caught earlier *)
  in
  go env [] [] expected_tys args

(** Top-level inference that hides the solving_env *)
let infer_term (defs: definitions) (ctx: context) (tm: term) 
    : (typed_term * typ, check_error) result =
  let* (tm', ty, _) = infer defs ctx empty_env tm in
  Ok (tm', ty)

(** Type check a definition *)
let check_definition
    (defs: definitions) (def: term_def) : (typed_term_def, check_error) result =
  let ctx = {kinds = Ident.emptytbl; types = Ident.emptytbl} in
  (* Add type parameters to kind context *)
  let ctx = extend_kinds ctx def.type_args in
  (* Add term parameters to type context *)
  let ctx = extend_many ctx def.term_args in
  (* Check body against declared return type *)
  let* (body', _, _) = check defs ctx empty_env def.body def.return_type in
  Ok
    { name = def.name
    ; type_args = def.type_args
    ; term_args = def.term_args
    ; return_type = def.return_type
    ; body = body'
    }