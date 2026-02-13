(**
  module: Canon.Terms
  description: Canonicalized commands for the sequent calculus.
*)

(* ========================================================================= *)
(* Commands
   
   Typing judgment: Γ ⊢ cmd  where Γ : var → chiral_typ
   
   Types are ambidextrous: the same signature can be read as data or codata.
   - Data reading: Let (constructor), Switch (pattern match)
   - Codata reading: New (copattern), Invoke (destructor)
   
   Context is non-linear: variables are never consumed, freely duplicated.
   Type instantiation is already reflected in sgn_typ/xtor.
*)

open Common.Identifiers
open Common.Types
type var = Ident.t

type command =
    (* let v = m(x1, ...); s
       
       m ∈ T    Γ(xi) = Ai (args of m)    Γ, v : lhs T ⊢ s
       ---------------------------------------------------- [LET]
       Γ ⊢ let v = m(x1, ...); s
       
       Constructs a producer of T using constructor m. *)
    Let of var * xtor * var list * command

    (* switch v {m1(y1, ...) ⇒ s1, ...}
       
       Γ(v) = lhs T    for each m ∈ T: Γ, yi : Ai ⊢ si
       ------------------------------------------------ [SWITCH]
       Γ ⊢ switch v {m1(y1, ...) ⇒ s1, ...}
       
       Pattern matches on producer v of signature T. *)
  | Switch of sgn_typ * var * branch list

    (* new v = {m1(y1, ...) ⇒ s1, ...}; s
       
       for each m ∈ T: Γ, yi : Ai ⊢ si    Γ, v : rhs T ⊢ s
       ---------------------------------------------------- [NEW]
       Γ ⊢ new v = {m1(y1, ...) ⇒ s1, ...}; s
       
       Creates a consumer of T via copattern matching. *)
  | New of sgn_typ * var * branch list * command

    (* invoke v m(x1, ...)
       
       Γ(v) = rhs T    m ∈ T    Γ(xi) = Ai
       ------------------------------------ [INVOKE]
       Γ ⊢ invoke v m(x1, ...)
       
       Invokes destructor m on consumer v. *)
  | Invoke of var * xtor * var list

    (* ⟨v | k⟩
       
       Γ(v) = lhs τ    Γ(k) = rhs τ
       ----------------------------- [AXIOM]
       Γ ⊢ ⟨v | k⟩
       
       Cut: pass producer v to consumer k at type τ. *)
  | Axiom of typ * var * var

    (* Primitives for integers *)
  | Lit of int * var * command       (* lit n { v ⇒ s } *)
  | Add of var * var * var * command (* add(x, y) { v ⇒ s } *)
  | Ifz of var * command * command   (* ifz(v) { sThen; sElse } *)

    (* Terminals *)
  | Ret of typ * var  (* ret τ v *)
  | End

and branch = xtor * var list * command

(* ========================================================================= *)
(* Type Checking for Commands *)
(* ========================================================================= *)

module VarMap = Ident

type context = chiral_typ VarMap.tbl

type check_error =
  | UnboundVariable of var
  | TypeMismatch of { expected: chiral_typ; actual: chiral_typ }
  | ChiralityMismatch of { expected_chirality: [`Lhs | `Rhs]; actual: chiral_typ }
  | ExpectedSignature of typ  (* Type was expected to be a signature *)
  | SignatureMismatch of sgn_typ * sgn_typ  (* Expected, actual *)
  | XtorNotInSignature of xtor * sgn_typ
  | NonExhaustive of xtor list  (* Missing branches for these reachable xtors *)
  | ArityMismatch of { xtor: xtor; expected: int; actual: int }
  | UnificationFailed of typ * typ

type 'a check_result = ('a, check_error) result

let lookup (ctx: context) (v: var) : chiral_typ check_result =
  match VarMap.find_opt v ctx with
  | Some ct -> Ok ct
  | None -> Error (UnboundVariable v)

let extend (ctx: context) (v: var) (ct: chiral_typ) : context =
  VarMap.add v ct ctx

let extend_many (ctx: context) (bindings: (var * chiral_typ) list) : context =
  List.fold_left (fun ctx (v, ct) -> extend ctx v ct) ctx bindings

(** Extract the underlying typ from a chiral_typ *)
let unchiral (ct: chiral_typ) : typ =
  match ct with Lhs t | Rhs t -> t

(** Check that a chiral type is Lhs and extract the type *)
let expect_lhs (ct: chiral_typ) : typ check_result =
  match ct with
    Lhs t -> Ok t
  | Rhs _ -> Error (ChiralityMismatch {
      expected_chirality = `Lhs; actual = ct })

(** Check that a chiral type is Rhs and extract the type *)
let expect_rhs (ct: chiral_typ) : typ check_result =
  match ct with
    Rhs t -> Ok t
  | Lhs _ -> Error (ChiralityMismatch {
      expected_chirality = `Rhs; actual = ct })

(** Expect a type to be a signature (possibly after whnf).
    After reduction, only Sgn or stuck types are possible. *)
let expect_sgn (kctx: kind Ident.tbl) (env: solving_env) (t: typ)
    : sgn_typ check_result =
  match whnf kctx env.subs t with
    Sgn sg -> Ok sg | t' -> Error (ExpectedSignature t')

(** Check that xtor arguments match the context types *)
let check_xtor_args
    (kctx: kind Ident.tbl) (ctx: context) (env: solving_env)
    (x: xtor) (args: var list) 
    : solving_env check_result =
  if List.length x.arguments <> List.length args then
    Error (ArityMismatch
      { xtor = x
      ; expected = List.length x.arguments
      ; actual = List.length args
      })
  else
    let rec check_args env xargs vars =
      match xargs, vars with
        [], [] -> Ok env
      | xarg :: xrest, v :: vrest ->
          let* actual_ct = lookup ctx v in
          (* Unify the expected type with the actual type *)
          let expected_typ = unchiral xarg in
          let actual_typ = unchiral actual_ct in
          (match unify kctx expected_typ actual_typ env with
            None -> Error (UnificationFailed (expected_typ, actual_typ))
          | Some env' -> 
              (* Also check chirality matches *)
              match xarg, actual_ct with
                Lhs _, Lhs _ | Rhs _, Rhs _ -> check_args env' xrest vrest
              | _ -> Error (TypeMismatch {
                expected = xarg; actual = actual_ct }))
      | _ -> failwith "impossible: length mismatch after check"
    in
    check_args env x.arguments args

(** Bind xtor arguments in context for a branch *)
let bind_xtor_args (ctx: context) (x: xtor) (vars: var list) : context =
  let bindings = List.combine vars x.arguments in
  extend_many ctx bindings

(** Check a command under a context and solving environment *)
let rec check_command
    (kctx: kind Ident.tbl) (ctx: context) (env: solving_env)
    (cmd: command) 
    : unit check_result =
  match cmd with
    Let (v, x, args, body) ->
      (* Check xtor arguments against context *)
      let* env' = check_xtor_args kctx ctx env x args in
      (* v gets type Lhs of the instantiated result type from the xtor *)
      let v_typ = Lhs x.main in
      check_command kctx (extend ctx v v_typ) env' body

  | Switch (sg, v, branches) ->
      (* v must be Lhs of the signature *)
      let* v_ct = lookup ctx v in
      let* v_typ = expect_lhs v_ct in
      (* Get the instantiated signature type (already GADT-filtered) *)
      let* actual_sg = expect_sgn kctx env v_typ in
      (* Unify with declared signature - this verifies same xtors *)
      (match unify_sgn kctx sg actual_sg env with
        None -> Error (SignatureMismatch (sg, actual_sg))
      | Some env' ->
          (* Check exhaustiveness against branches *)
          let branch_names = List.map (fun ((x: xtor), _, _) -> 
            x.name) branches in
          let missing_xtors = List.filter (fun (x: xtor) -> 
            not (List.exists (Path.equal x.name) branch_names)
          ) actual_sg.xtors in
          if missing_xtors <> [] then
            Error (NonExhaustive missing_xtors)
          else
            check_branches_simple kctx ctx env' actual_sg.xtors branches)

  | New (sg, v, branches, body) ->
      (* sg is the instantiated signature - xtors already GADT-filtered *)
      let branch_names = List.map (fun ((x: xtor), _, _) -> 
        x.name
      ) branches in
      let missing_xtors = List.filter (fun (x: xtor) -> 
        not (List.exists (Path.equal x.name) branch_names)
      ) sg.xtors in
      if missing_xtors <> [] then
        Error (NonExhaustive missing_xtors)
      else
        let* () = check_branches_simple kctx ctx env sg.xtors branches in
        let v_typ = Rhs (Sgn sg) in
        check_command kctx (extend ctx v v_typ) env body

  | Invoke (v, x, args) ->
      (* v must be Rhs of a signature containing x *)
      let* v_ct = lookup ctx v in
      let* v_typ = expect_rhs v_ct in
      let* sg = expect_sgn kctx env v_typ in
      if not (List.exists (fun (x': xtor) ->
        Path.equal x'.name x.name) sg.xtors
      ) then
        Error (XtorNotInSignature (x, sg))
      else
        check_xtor_args kctx ctx env x args
        |> Result.map (fun _ -> ())

  | Axiom (ty, v, k) ->
      (* v must be Lhs ty, k must be Rhs ty *)
      let* v_ct = lookup ctx v in
      let* k_ct = lookup ctx k in
      let* v_typ = expect_lhs v_ct in
      let* k_typ = expect_rhs k_ct in
      (match unify kctx v_typ ty env, unify kctx k_typ ty env with
        None, _ -> Error (UnificationFailed (v_typ, ty))
      | _, None -> Error (UnificationFailed (k_typ, ty))
      | Some _, Some _ -> Ok ())

  | Lit (_, v, body) ->
      let v_typ = Lhs (Ext Int) in
      check_command kctx (extend ctx v v_typ) env body

  | Add (x, y, v, body) ->
      let* x_ct = lookup ctx x in
      let* y_ct = lookup ctx y in
      let int_lhs = Lhs (Ext Int) in
      (match unify kctx (unchiral x_ct) (Ext Int) env, 
             unify kctx (unchiral y_ct) (Ext Int) env
      with
        None, _ -> Error (TypeMismatch {
          expected = int_lhs; actual = x_ct })
      | _, None -> Error (TypeMismatch {
          expected = int_lhs; actual = y_ct })
      | Some _, Some _ ->
          check_command kctx (extend ctx v int_lhs) env body)

  | Ifz (v, then_cmd, else_cmd) ->
      let* v_ct = lookup ctx v in
      (match unify kctx (unchiral v_ct) (Ext Int) env with
        None -> Error (TypeMismatch {
          expected = Lhs (Ext Int); actual = v_ct })
      | Some _ ->
          let* () = check_command kctx ctx env then_cmd in
          check_command kctx ctx env else_cmd)

  | Ret (ty, v) ->
      let* v_ct = lookup ctx v in
      let* v_typ = expect_lhs v_ct in
      (match unify kctx v_typ ty env with
        None -> Error (UnificationFailed (v_typ, ty))
      | Some _ -> Ok ())

  | End -> Ok ()

(** Check branches against xtors (same env for all branches) *)
and check_branches_simple
    (kctx: kind Ident.tbl) (ctx: context) (env: solving_env)
    (xtors: xtor list) (branches: branch list)
    : unit check_result =
  let check_one (x: xtor) =
    match List.find_opt (fun ((x': xtor), _, _) ->
        Path.equal x'.name x.name
      ) branches
    with
      None -> 
        (* This should not happen if exhaustiveness check passed *)
        failwith "impossible: missing branch after exhaustiveness check!"
    | Some (_, vars, cmd) ->
        if List.length vars <> List.length x.arguments then
          Error (ArityMismatch
            { xtor = x
            ; expected = List.length x.arguments
            ; actual = List.length vars
            })
        else
          let ctx' = bind_xtor_args ctx x vars in
          check_command kctx ctx' env cmd
  in
  let results = List.map check_one xtors in
  match List.find_opt Result.is_error results with
    Some (Error e) -> Error e
  | _ -> Ok ()