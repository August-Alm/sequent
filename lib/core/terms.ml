(**
  module: Core.Terms
  description: Abstract syntax and type checking for the core language.
*)

open Common.Identifiers
open Common.Types

let ( let* ) = Result.bind

type var = Ident.t

type command =
  (* ⟨producer | consumer⟩ at type *)
  | Cut of typ * term * term
  (* Call a defined function with type and term args *)
  | Call of Path.t * typ list * term list
  | Add of term * term * term
  | Ifz of term * command * command
  | End

and term =
    Variable of var
  | Lit of int
  (* Constructors build data (Lhs/producer) *)
  | Ctor of sgn_typ * xtor * term list
  (* Destructors build codata (Rhs/consumer) *)
  | Dtor of sgn_typ * xtor * term list
  (* Match consumes data (Rhs/consumer) *)
  | Match of sgn_typ * branch list
  (* Comatch produces codata (Lhs/producer) *)
  | Comatch of sgn_typ * branch list
  (* μL binds Rhs var, forms Lhs *)
  | MuLhs of typ * var * command
  (* μR binds Lhs var, forms Rhs *)
  | MuRhs of typ * var * command

and branch = xtor * var list * command

type definition =
  { path: Path.t
  ; type_params: (var * kind) list
  ; term_params: (var * chiral_typ) list
  ; body: command
  }

(* ========================================================================= *)
(* Type Checking Errors                                                      *)
(* ========================================================================= *)

type check_error =
    UnboundVariable of var
  | UnboundDefinition of Path.t
  | UnificationFailed of typ * typ
  | ChiralityMismatch of
    { expected_chirality: [`Lhs | `Rhs]
    ; actual: chiral_typ
    }
  | ExpectedSignature of typ
  | SignatureMismatch of sgn_typ * sgn_typ
  | XtorNotInSignature of xtor * sgn_typ
  | XtorArityMismatch of
      { xtor: xtor
      ; expected: int
      ; got: int
      }
  | XtorArgTypeMismatch of 
      { xtor: xtor
      ; index: int
      ; expected: chiral_typ
      ; got: chiral_typ
      }
  | NonExhaustiveMatch of 
      { sgn: sgn_typ
      ; missing: xtor list
      }
  | CallTypeArityMismatch of 
      { defn: Path.t
      ; expected: int
      ; got: int
      }
  | CallTermArityMismatch of 
      { defn: Path.t
      ; expected: int
      ; got: int
      }
  | CallArgTypeMismatch of
      { defn: Path.t
      ; index: int
      ; expected: chiral_typ
      ; got: chiral_typ
      }
  | AddTypeMismatch of 
      { arg1: chiral_typ
      ; arg2: chiral_typ
      ; result: chiral_typ
      }
  | IfzConditionNotInt of chiral_typ
  | IfzBranchMismatch of 
      { then_typ: typ option
      ; else_typ: typ option
      }

type 'a check_result = ('a, check_error) result

(* ========================================================================= *)
(* Type Checking Context and Helpers                                         *)
(* ========================================================================= *)

(** Kind context: maps type variables to their kinds *)
type kctx = kind Ident.tbl

(** Term context: maps term variables to their chiral types *)
type ctx = chiral_typ Ident.tbl

(** Definition context: maps paths to top-level definitions *)
type dctx = definition Path.tbl

(** Lookup a definition by path *)
let lookup_def (dctx: dctx) (p: Path.t) : definition check_result =
  match Path.find_opt p dctx with
  | Some d -> Ok d
  | None -> Error (UnboundDefinition p)

(** Instantiate a type by substituting type parameters with arguments *)
let instantiate_typ (params: (var * kind) list) (args: typ list) (t: typ) : typ =
  let subst = List.map2 (fun (v, _) arg -> (v, arg)) params args in
  subst_rigid subst t

(** Instantiate a chiral type *)
let instantiate_chiral (params: (var * kind) list) (args: typ list) (ct: chiral_typ) : chiral_typ =
  chiral_map (instantiate_typ params args) ct

(** Extract the underlying typ from a chiral_typ *)
let unchiral (ct: chiral_typ) : typ =
  match ct with Lhs t | Rhs t -> t

(** Lookup a variable in context *)
let lookup (ctx: ctx) (v: var) : chiral_typ check_result =
  match Ident.find_opt v ctx with
    Some ct -> Ok ct | None -> Error (UnboundVariable v)

(** Extend context with a binding *)
let extend (ctx: ctx) (v: var) (ct: chiral_typ) : ctx =
  Ident.add v ct ctx

(** Check that a chiral type is Lhs and extract the type *)
let expect_lhs (ct: chiral_typ) : (typ, check_error) result =
  match ct with
    Lhs t -> Ok t
  | Rhs _ -> Error (ChiralityMismatch {expected_chirality = `Lhs; actual = ct})

(** Check that a chiral type is Rhs and extract the type *)
let expect_rhs (ct: chiral_typ) : (typ, check_error) result =
  match ct with
    Rhs t -> Ok t
  | Lhs _ -> Error (ChiralityMismatch {expected_chirality = `Rhs; actual = ct})

(** Expect a type to be a signature (after WHNF normalization) *)
let expect_sgn (kctx: kctx) (env: solving_env) (t: typ) : (sgn_typ, check_error) result =
  match whnf kctx env.subs t with
    Sgn sg -> Ok sg 
  | t' -> Error (ExpectedSignature t')

(* ========================================================================= *)
(* Xtor Argument Checking with Unification                                   *)
(* ========================================================================= *)

(** Bind variables from an xtor's arguments into context *)
let bind_xtor_args (ctx: ctx) (xtor: xtor) (vars: var list) : ctx =
  List.fold_left2 
    (fun ctx var chiral_ty -> extend ctx var chiral_ty)
    ctx vars xtor.arguments

(** Check that actual arguments match xtor's declared chiralities with unification *)
let check_xtor_args 
    (kctx: kctx) (ctx: ctx) (env: solving_env) 
    (xtor: xtor) (args: term list) 
    (infer: kctx -> ctx -> solving_env -> term -> (chiral_typ * solving_env) check_result) 
    : (solving_env, check_error) result =
  if List.length args <> List.length xtor.arguments then
    Error (XtorArityMismatch 
      {xtor; expected = List.length xtor.arguments; got = List.length args})
  else
    let rec check_args idx env args expected =
      match args, expected with
        [], [] -> Ok env
      | arg :: args', exp_chiral :: exps' ->
          let* (got_chiral, env') = infer kctx ctx env arg in
          (* Unify the underlying types *)
          let expected_typ = unchiral exp_chiral in
          let actual_typ = unchiral got_chiral in
          (match unify kctx expected_typ actual_typ env' with
            None -> Error (UnificationFailed (expected_typ, actual_typ))
          | Some env'' ->
              (* Also check chirality matches *)
              (match exp_chiral, got_chiral with
                Lhs _, Lhs _ | Rhs _, Rhs _ -> check_args (idx + 1) env'' args' exps'
              | _ -> Error (XtorArgTypeMismatch 
                  {xtor; index = idx; expected = exp_chiral; got = got_chiral})))
      | _ -> assert false (* Length mismatch already checked *)
    in
    check_args 0 env args xtor.arguments

(* ========================================================================= *)
(* Branch Checking                                                           *)
(* ========================================================================= *)

(** Check a single branch: bind vars with xtor's chiralities, check command *)
let check_branch 
    (kctx: kctx) (ctx: ctx) (env: solving_env) 
    (sgn: sgn_typ) (xtor: xtor) (vars: var list) (cmd: command)
    (check_cmd: kctx -> ctx -> solving_env -> command -> unit check_result) 
    : unit check_result =
  (* Verify xtor belongs to signature *)
  if not (List.exists (fun x -> Path.equal x.name xtor.name) sgn.xtors) then
    Error (XtorNotInSignature (xtor, sgn))
  (* Verify arity matches *)
  else if List.length vars <> List.length xtor.arguments then
    Error (XtorArityMismatch 
      {xtor; expected = List.length xtor.arguments; got = List.length vars})
  else
    let ctx' = bind_xtor_args ctx xtor vars in
    check_cmd kctx ctx' env cmd

(** Check all branches and verify exhaustiveness *)
let check_branches 
    (kctx: kctx) (ctx: ctx) (env: solving_env) 
    (sgn: sgn_typ) (branches: branch list)
    (check_cmd: kctx -> ctx -> solving_env -> command -> unit check_result) 
    : unit check_result =
  (* Check each branch *)
  let* () = 
    List.fold_left 
      (fun acc (xtor, vars, cmd) ->
        let* () = acc in
        check_branch kctx ctx env sgn xtor vars cmd check_cmd)
      (Ok ()) branches
  in
  (* Check exhaustiveness *)
  let covered = List.map (fun (xtor, _, _) -> xtor.name) branches in
  let missing = List.filter (fun x -> 
    not (List.exists (Path.equal x.name) covered)
  ) sgn.xtors in
  if missing = [] then Ok ()
  else Error (NonExhaustiveMatch {sgn; missing})

(* ========================================================================= *)
(* Type Inference with Unification                                           *)
(* ========================================================================= *)

(** Check call arguments against instantiated parameter types *)
let check_call_args
    (kctx: kctx) (ctx: ctx) (env: solving_env)
    (defn_path: Path.t) (params: (var * chiral_typ) list) (args: term list)
    (infer: kctx -> ctx -> solving_env -> term -> (chiral_typ * solving_env) check_result)
    : (solving_env, check_error) result =
  if List.length args <> List.length params then
    Error (CallTermArityMismatch 
      { defn = defn_path
      ; expected = List.length params
      ; got = List.length args
      })
  else
    let rec check_args idx env args params =
      match args, params with
      | [], [] -> Ok env
      | arg :: args', (_, exp_chiral) :: params' ->
          let* (got_chiral, env') = infer kctx ctx env arg in
          let expected_typ = unchiral exp_chiral in
          let actual_typ = unchiral got_chiral in
          (match unify kctx expected_typ actual_typ env' with
            None -> Error (UnificationFailed (expected_typ, actual_typ))
          | Some env'' ->
              (match exp_chiral, got_chiral with
                Lhs _, Lhs _ | Rhs _, Rhs _ ->
                  check_args (idx + 1) env'' args' params'
              | _ -> Error (CallArgTypeMismatch
                  { defn = defn_path; index = idx
                  ; expected = exp_chiral; got = got_chiral
                  })))
      | _ -> assert false
    in
    check_args 0 env args params

(** Infer the chiral type of a term, threading solving_env *)
let rec infer_typ (dctx: dctx) (kctx: kctx) (ctx: ctx) (env: solving_env) 
    : term -> (chiral_typ * solving_env) check_result =
  function
    Variable x ->
      let* ct = lookup ctx x in
      Ok (ct, env)
  | Lit _ -> 
      Ok (Lhs (Ext Int), env)
  | Ctor (_sgn, xtor, args) ->
      (* Check arguments match xtor's declared chiralities *)
      let* env' = check_xtor_args kctx ctx env xtor args (infer_typ dctx) in
      (* Ctor produces Lhs of the xtor's main type *)
      Ok (Lhs xtor.main, env')
  | Dtor (_sgn, xtor, args) ->
      (* Check arguments match xtor's declared chiralities *)
      let* env' = check_xtor_args kctx ctx env xtor args (infer_typ dctx) in
      (* Dtor produces Rhs of the xtor's main type *)
      Ok (Rhs xtor.main, env')
  | Match (sgn, branches) ->
      (* Check all branches, verify exhaustiveness *)
      let* () = check_branches kctx ctx env sgn branches (check_command dctx) in
      (* Match produces Rhs (consumer) of the signature type *)
      Ok (Rhs (Sgn sgn), env)
  | Comatch (sgn, branches) ->
      (* Check all branches, verify exhaustiveness *)
      let* () = check_branches kctx ctx env sgn branches (check_command dctx) in
      (* Comatch produces Lhs (producer) of the signature type *)
      Ok (Lhs (Sgn sgn), env)
  | MuLhs (ty, x, cmd) ->
      (* μL binds x : Rhs ty, produces Lhs ty *)
      let ctx' = extend ctx x (Rhs ty) in
      let* () = check_command dctx kctx ctx' env cmd in
      Ok (Lhs ty, env)
  | MuRhs (ty, k, cmd) ->
      (* μR binds k : Lhs ty, produces Rhs ty *)
      let ctx' = extend ctx k (Lhs ty) in
      let* () = check_command dctx kctx ctx' env cmd in
      Ok (Rhs ty, env)

(** Check a command under contexts and solving environment *)
and check_command (dctx: dctx) (kctx: kctx) (ctx: ctx) (env: solving_env) 
    : command -> unit check_result =
  function
    Cut (ret_ty, t1, t2) ->
      let* (t1_ct, env') = infer_typ dctx kctx ctx env t1 in
      let* (t2_ct, env'') = infer_typ dctx kctx ctx env' t2 in
      let* t1_ty = expect_lhs t1_ct in
      let* t2_ty = expect_rhs t2_ct in
      (* Unify both with the declared cut type *)
      (match unify kctx t1_ty ret_ty env'',
             unify kctx t2_ty ret_ty env''
      with
        None, _ -> Error (UnificationFailed (t1_ty, ret_ty))
      | _, None -> Error (UnificationFailed (t2_ty, ret_ty))
      | Some _, Some _ -> Ok ())
  | Call (path, type_args, term_args) ->
      (* Look up the definition *)
      let* defn = lookup_def dctx path in
      (* Check type argument arity *)
      if List.length type_args <> List.length defn.type_params then
        Error (CallTypeArityMismatch 
          { defn = path
          ; expected = List.length defn.type_params
          ; got = List.length type_args
          })
      else
        (* Instantiate term parameter types with type arguments *)
        let inst_params = List.map (fun (v, ct) ->
          (v, instantiate_chiral defn.type_params type_args ct)
        ) defn.term_params in
        (* Check term arguments against instantiated parameter types *)
        let* _env' = check_call_args kctx ctx env path inst_params term_args (infer_typ dctx) in
        Ok ()
  | Add (t1, t2, t3) ->
      let* (t1_ct, env') = infer_typ dctx kctx ctx env t1 in
      let* (t2_ct, env'') = infer_typ dctx kctx ctx env' t2 in
      let* (t3_ct, env''') = infer_typ dctx kctx ctx env'' t3 in
      let int_lhs = Lhs (Ext Int) in
      let int_rhs = Rhs (Ext Int) in
      (match unify kctx (unchiral t1_ct) (Ext Int) env''',
             unify kctx (unchiral t2_ct) (Ext Int) env'''
      with
        None, _ -> Error (AddTypeMismatch {arg1 = t1_ct; arg2 = t2_ct; result = t3_ct})
      | _, None -> Error (AddTypeMismatch {arg1 = t1_ct; arg2 = t2_ct; result = t3_ct})
      | Some _, Some _ ->
          (* Check chiralities: t1, t2 should be Lhs Int, t3 should be Rhs Int *)
          if t1_ct = int_lhs && t2_ct = int_lhs && t3_ct = int_rhs then Ok ()
          else Error (AddTypeMismatch {arg1 = t1_ct; arg2 = t2_ct; result = t3_ct}))
  | Ifz (t, cmd1, cmd2) ->
      let* (t_ct, env') = infer_typ dctx kctx ctx env t in
      (match unify kctx (unchiral t_ct) (Ext Int) env' with
        None -> Error (IfzConditionNotInt t_ct)
      | Some _ ->
          (* Check chirality: condition should be Lhs Int *)
          let* _ = expect_lhs t_ct in
          let* _ = check_command dctx kctx ctx env' cmd1 in
          check_command dctx kctx ctx env' cmd2)
  | End -> 
      Ok ()
