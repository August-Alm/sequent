(**
  module: Focused.Terms
  description: Focused/canonicalized commands for the core sequent calculus.
*)

open Common.Identifiers
open Types.FocusedBase
open Types.FocusedTypes

let ( let* ) o f = Utility.( let* ) o f

type var = Ident.t
type sym = Path.t

(* ========================================================================= *)
(* Commands                                                                  *)
(* ========================================================================= *)
   
(*
   Typing judgment: Γ ⊢ cmd  where Γ : var → chiral_typ
   
   Types are ambidextrous: the same signature can be read as data or codata.
   - Data reading: Let (constructor), Switch (pattern match)
   - Codata reading: New (copattern), Invoke (destructor)
   
   Context is non-linear: variables are never consumed, freely duplicated.
   Type instantiation is already reflected in sgn_typ/xtor.
*)

type command =
    (* let v = m(x1, ...); s
       
      m ∈ T    Γ(xi) = Ai (args of m)    Γ, v : prd T ⊢ s
      ---------------------------------------------------- [LET]
      Γ ⊢ let v = m(x1, ...); s
      
      Constructs a producer of T using constructor m. *)
    (* v, instantiated dec, m, xi's, s *)
    Let of var * dec * sym * (var list) * command

    (* switch v {m1(y1, ...) ⇒ s1, ...}
       
      Γ(v) = prd T    for each m ∈ T: Γ, yi : Ai ⊢ si
      ------------------------------------------------ [SWITCH]
      Γ ⊢ switch v {m1(y1, ...) ⇒ s1, ...}
      
      Pattern matches on producer v of signature T. *)
    (* v, instantiated dec, branches *)
  | Switch of var * dec * branch list

    (* new v = {m1(y1, ...) ⇒ s1, ...}; s
       
      for each m ∈ T: Γ, yi : Ai ⊢ si    Γ, v : cns T ⊢ s
      ---------------------------------------------------- [NEW]
      Γ ⊢ new v = {m1(y1, ...) ⇒ s1, ...}; s
      
      Creates a consumer of T via copattern matching. *)
    (* v, instantiated dec, branches, s *)
  | New of var * dec * branch list * command

    (* invoke v m(x1, ...)
       
      Γ(v) = cns T    m ∈ T    Γ(xi) = Ai
      ------------------------------------ [INVOKE]
      Γ ⊢ invoke v m(x1, ...)
      
      Invokes destructor m on consumer v. *)
    (* v, instantiated dec, m, xi's *)
  | Invoke of var * dec * sym * (var list)

    (* ⟨v | k⟩
       
      Γ(v) = prd τ    Γ(k) = cns τ
      ----------------------------- [AXIOM]
      Γ ⊢ ⟨v | k⟩
      
      Cut: pass producer v to consumer k at primitive type τ. *)
  | Axiom of Common.Types.ext_type * var * var

    (* Primitives for integers *)
  | Lit of int * var * command       (* lit n { v ⇒ s } *)
  | Add of var * var * var * command (* add(x, y) { v ⇒ s } *)
  | Sub of var * var * var * command (* sub(x, y) { v ⇒ s } *)
  | NewInt of var * var * command * command  (* new k = { v ⇒ s1 }; s2 - Int consumer binding, k : Cns Int *)
  | Ifz of var * command * command   (* ifz(v) { sThen; sElse } *)

    (* Terminals *)
  | Ret of typ * var  (* ret τ v *)
  | End

and branch = sym * (var list) * (var list) * command

(* ========================================================================= *)
(* Type Checking Errors                                                      *)
(* ========================================================================= *)

type check_error =
    UnboundVariable of var
  | UnboundDeclaration of Path.t
  | UnboundXtor of Path.t * Path.t
  | UnificationFailed of typ * typ
  | ChiralityMismatch of { expected_chirality: [`Prd | `Cns]; actual: chiral_typ }
  | XtorArityMismatch of { xtor: Path.t; expected: int; got: int }
  | TypeVarArityMismatch of { xtor: Path.t; expected: int; got: int }
  | NonExhaustiveMatch of { dec_name: Path.t; missing: Path.t list }
  | ArityMismatch of { expected: int; got: int }
  | ExpectedSignature of typ

type 'a check_result = ('a, check_error) result

(* ========================================================================= *)
(* Type Checking Context and Helpers                                         *)
(* ========================================================================= *)

type context =
  { types: Types.FocusedTypes.context
  ; term_vars: chiral_typ Ident.tbl
  }

(** Lookup a declaration (data/codata type) by path *)
let lookup_dec (ctx: context) (p: Path.t) : (dec, check_error) result =
  match Path.find_opt p ctx.types.decs with
    Some d -> Ok d | None -> Error (UnboundDeclaration p)

(** Find an xtor in a declaration *)
let find_xtor (dec: dec) (xtor_name: Path.t) : xtor option =
  List.find_opt (fun (x: xtor) -> Path.equal x.name xtor_name) dec.xtors

(** Lookup a variable in context *)
let lookup_var (ctx: context) (v: var) : chiral_typ check_result =
  match Ident.find_opt v ctx.term_vars with
    Some ct -> Ok ct
  | None -> Error (UnboundVariable v)

(** Extend context with a term variable binding *)
let extend (ctx: context) (v: var) (ct: chiral_typ) : context =
  { ctx with term_vars = Ident.add v ct ctx.term_vars }

(** Extend context with a type variable binding *)
let extend_tyvar (ctx: context) (v: var) (k: typ) : context =
  { ctx with types = { ctx.types with typ_vars = Ident.add v k ctx.types.typ_vars } }

(** Check that a chiral type is Prd and extract the type *)
let expect_prd (ct: chiral_typ) : (typ, check_error) result =
  match ct with
    Prd t -> Ok t
  | Cns _ -> Error (ChiralityMismatch { expected_chirality = `Prd; actual = ct })

(** Check that a chiral type is Cns and extract the type *)
let expect_cns (ct: chiral_typ) : (typ, check_error) result =
  match ct with
    Cns t -> Ok t
  | Prd _ -> Error (ChiralityMismatch { expected_chirality = `Cns; actual = ct })

(** Expect a type to be a signature *)
let expect_sgn (t: typ) (subs: subst) : (Path.t * typ list, check_error) result =
  match apply_subst subs t with
    Sgn (name, args) -> Ok (name, args)
  | t' -> Error (ExpectedSignature t')

(* ========================================================================= *)
(* Xtor Instantiation                                                        *)
(* ========================================================================= *)

(** Freshen an xtor's existential types with fresh metavariables.
    For instantiated declarations, quantified is empty so we only freshen existentials. *)
let freshen_xtor_existentials (xtor: xtor)
    : (chiral_typ list * typ) =
  (* Freshen existential variables only - quantified is empty for instantiated dec *)
  let _, exist_subst = freshen_meta xtor.existentials in
  let inst_args =
    List.map (chiral_map (apply_fresh_subst exist_subst))
      xtor.argument_types in
  let inst_main = apply_fresh_subst exist_subst xtor.main in
  (inst_args, inst_main)

(** Bind term variables with xtor argument types *)
let bind_xtor_term_args (ctx: context) (arg_types: chiral_typ list) (vars: var list)
    : context =
  List.fold_left2 (fun ctx var ct -> extend ctx var ct) ctx vars arg_types

(* ========================================================================= *)
(* Branch Checking                                                           *)
(* ========================================================================= *)

(** Check a single branch.
    For instantiated declarations, xtor.quantified is empty. *)
let check_branch
    (ctx: context) (dec: dec)
    (xtor_name: Path.t) (type_vars: var list) (term_vars: var list) (cmd: command)
    (check_cmd: context -> subst -> command -> unit check_result)
    (subs: subst)
    : unit check_result =
  match find_xtor dec xtor_name with
    None -> Error (UnboundXtor (dec.name, xtor_name))
  | Some xtor ->
      (* Check type variable arity (existentials only, quantified is empty) *)
      let num_exist = List.length xtor.existentials in
      if List.length type_vars <> num_exist then
        Error (TypeVarArityMismatch {
          xtor = xtor_name; expected = num_exist; got = List.length type_vars })
      (* Check term variable arity *)
      else if List.length term_vars <> List.length xtor.argument_types then
        Error (XtorArityMismatch {
          xtor = xtor_name
        ; expected = List.length xtor.argument_types
        ; got = List.length term_vars })
      else
        (* Freshen existentials only - dec is already instantiated *)
        let inst_args, _ = freshen_xtor_existentials xtor in
        (* Substitute user-provided type variable names for existentials *)
        let exist_subst =
          List.fold_left2 (fun s (old_v, _) new_v ->
            Ident.add old_v (TVar new_v) s
          ) Ident.emptytbl xtor.existentials type_vars
        in
        let inst_args' =
          List.map (chiral_map (apply_fresh_subst exist_subst))
            inst_args
        in
        (* Extend context with existential type vars and term vars *)
        let ctx' =
          List.fold_left2 (fun c new_v (_, k) -> extend_tyvar c new_v k)
            ctx type_vars xtor.existentials
        in
        let ctx'' = bind_xtor_term_args ctx' inst_args' term_vars in
        check_cmd ctx'' subs cmd

(** Check all branches and verify exhaustiveness.
    For instantiated declarations, exhaustiveness is just checking all xtors are covered. *)
let check_branches
    (ctx: context) (dec: dec) (branches: branch list)
    (check_cmd: context -> subst -> command -> unit check_result)
    (subs: subst)
    : unit check_result =
  (* Check each branch *)
  let* () =
    List.fold_left (fun acc (xtor_name, type_vars, term_vars, cmd) ->
      let* _ = acc in
      check_branch ctx dec xtor_name
        type_vars term_vars cmd check_cmd subs
    ) (Ok ()) branches
  in
  (* Check exhaustiveness - all xtors in instantiated dec must be covered *)
  let covered = List.map (fun (xtor_name, _, _, _) -> xtor_name) branches in
  let missing = List.filter_map (fun (x: xtor) ->
    if List.exists (Path.equal x.name) covered then None
    else Some x.name
  ) dec.xtors in
  if missing = [] then Ok ()
  else Error (NonExhaustiveMatch { dec_name = dec.name; missing })

(* ========================================================================= *)
(* Command Type Checking                                                     *)
(* ========================================================================= *)

(** Check a command under a context, threading substitution *)
let rec check_command (ctx: context) (subs: subst) (cmd: command)
    : unit check_result =
  match cmd with
  (* let v = m(xi's); s -- dec is pre-instantiated *)
  | Let (v, dec, xtor_name, term_vars, body) ->
      (match find_xtor dec xtor_name with
        None -> Error (UnboundXtor (dec.name, xtor_name))
      | Some xtor ->
          (* Freshen existentials - quantified is empty for instantiated dec *)
          let inst_args, inst_main = freshen_xtor_existentials xtor in
          if List.length term_vars <> List.length inst_args then
            Error (XtorArityMismatch
              { xtor = xtor_name
              ; expected = List.length inst_args
              ; got = List.length term_vars
              })
          else
            (* Check that term_vars have the expected types in context *)
            let* subs' =
              check_xtor_args ctx xtor_name inst_args term_vars subs in
            let v_typ = Prd inst_main in
            check_command (extend ctx v v_typ) subs' body)

  (* switch v {...} -- dec is pre-instantiated *)
  | Switch (v, dec, branches) ->
      let* v_ct = lookup_var ctx v in
      let* v_ty = expect_prd v_ct in
      (* The expected type is the instantiated signature *)
      let expected_ty = Sgn (dec.name, dec.type_args) in
      (* Unify v's type with the expected signature *)
      (match unify v_ty expected_ty subs with
        None -> Error (UnificationFailed (v_ty, expected_ty))
      | Some subs' ->
          check_branches ctx dec branches check_command subs')

  (* new v = {...}; s -- dec is pre-instantiated *)
  | New (v, dec, branches, body) ->
      let* _ =
        check_branches ctx dec branches check_command subs
      in
      let v_typ = Cns (Sgn (dec.name, dec.type_args)) in
      check_command (extend ctx v v_typ) subs body

  (* invoke v m(xi's) -- dec is pre-instantiated *)
  | Invoke (v, dec, xtor_name, term_vars) ->
      (match find_xtor dec xtor_name with
        None -> Error (UnboundXtor (dec.name, xtor_name))
      | Some xtor ->
          let* v_ct = lookup_var ctx v in
          let* v_ty = expect_cns v_ct in
          let expected_ty = Sgn (dec.name, dec.type_args) in
          (match unify v_ty expected_ty subs with
            None -> Error (UnificationFailed (v_ty, expected_ty))
          | Some subs' ->
              (* Freshen existentials - quantified is empty for instantiated dec *)
              let inst_args, _ = freshen_xtor_existentials xtor in
              check_xtor_args ctx xtor_name inst_args term_vars subs'
              |> Result.map (fun _ -> ())))

  (* ⟨v | k⟩ at ty *)
  | Axiom (ty, v, k) ->
      let* v_ct = lookup_var ctx v in
      let* k_ct = lookup_var ctx k in
      let* v_ty = expect_prd v_ct in
      let* k_ty = expect_cns k_ct in
      (match unify v_ty (Ext ty) subs with
        None -> Error (UnificationFailed (v_ty, Ext ty))
      | Some subs' ->
          (match unify k_ty (Ext ty) subs' with
            None -> Error (UnificationFailed (k_ty, Ext ty))
          | Some _ -> Ok ()))

  (* lit n { v => s } *)
  | Lit (_, v, body) ->
      let v_typ = Prd (Ext Int) in
      check_command (extend ctx v v_typ) subs body

  (* add(x, y) { v => s } *)
  | Add (x, y, v, body) ->
      let* x_ct = lookup_var ctx x in
      let* y_ct = lookup_var ctx y in
      let* x_ty = expect_prd x_ct in
      let* y_ty = expect_prd y_ct in
      let int_ty = Ext Int in
      (match unify x_ty int_ty subs with
        None -> Error (UnificationFailed (x_ty, int_ty))
      | Some subs' ->
          (match unify y_ty int_ty subs' with
            None -> Error (UnificationFailed (y_ty, int_ty))
          | Some subs'' ->
              let v_typ = Prd int_ty in
              check_command (extend ctx v v_typ) subs'' body))

  (* sub(x, y) { v => s } *)
  | Sub (x, y, v, body) ->
      let* x_ct = lookup_var ctx x in
      let* y_ct = lookup_var ctx y in
      let* x_ty = expect_prd x_ct in
      let* y_ty = expect_prd y_ct in
      let int_ty = Ext Int in
      (match unify x_ty int_ty subs with
        None -> Error (UnificationFailed (x_ty, int_ty))
      | Some subs' ->
          (match unify y_ty int_ty subs' with
            None -> Error (UnificationFailed (y_ty, int_ty))
          | Some subs'' ->
              let v_typ = Prd int_ty in
              check_command (extend ctx v v_typ) subs'' body))

  (* new k = { v => s1 }; s2 - Int consumer binding, k : Cns Int *)
  | NewInt (k, v, branch_body, cont) ->
      let int_ty = Ext Int in
      (* Check branch with v : Prd Int *)
      let* _ = check_command (extend ctx v (Prd int_ty)) subs branch_body in
      (* Check continuation with k : Cns Int *)
      check_command (extend ctx k (Cns int_ty)) subs cont

  (* ifz(v) { then; else } *)
  | Ifz (v, then_cmd, else_cmd) ->
      let* v_ct = lookup_var ctx v in
      let* v_ty = expect_prd v_ct in
      let int_ty = Ext Int in
      (match unify v_ty int_ty subs with
        None -> Error (UnificationFailed (v_ty, int_ty))
      | Some subs' ->
          let* _ = check_command ctx subs' then_cmd in
          check_command ctx subs' else_cmd)

  (* ret τ v
     Like simple.ml, Ret just checks that v is in scope with the right type. *)
  | Ret (ty, v) ->
      (* Following simple.ml's Collapsed checker: just check variable exists 
         and has the right type, don't check chirality.
         For negative types, x will be Cns; for positive, x will be Prd. *)
      let* v_ct = lookup_var ctx v in
      let v_ty = strip_chirality v_ct in
      (match unify v_ty ty subs with
        None -> Error (UnificationFailed (v_ty, ty))
      | Some _ -> Ok ())

  | End -> Ok ()

(** Helper: check that term variables have expected xtor argument types *)
and check_xtor_args (ctx: context) (xtor_name: Path.t)
    (expected: chiral_typ list) (vars: var list) (subs: subst)
    : subst check_result =
  if List.length vars <> List.length expected then
    Error (XtorArityMismatch {
      xtor = xtor_name
    ; expected = List.length expected
    ; got = List.length vars
    })
  else
    let rec check_args subs expected vars =
      match expected, vars with
        [], [] -> Ok subs
      | exp_ct :: exps', var :: vars' ->
          let* var_ct = lookup_var ctx var in
          let exp_ty = strip_chirality exp_ct in
          let var_ty = strip_chirality var_ct in
          (* DEBUG - use simple string conversion to avoid cycle *)
          let rec ty_str = function
            | TVar a -> "TVar " ^ Ident.name a
            | Sgn (p, tys) -> "Sgn(" ^ Path.name p ^ ", [" ^ String.concat ", " (List.map ty_str tys) ^ "])"
            | Ext Int -> "Ext Int"
            | _ -> "..."
          in
          Format.eprintf "check_xtor_args: var=%s, exp_ty=%s, var_ty=%s@."
            (Ident.name var) (ty_str exp_ty) (ty_str var_ty);
          (match unify exp_ty var_ty subs with
            None -> Error (UnificationFailed (exp_ty, var_ty))
          | Some subs' ->
              (* Also check chirality matches *)
              (match exp_ct, var_ct with
                Prd _, Prd _ | Cns _, Cns _ ->
                  check_args subs' exps' vars'
              | _ -> Error (ChiralityMismatch
                  { expected_chirality =
                      (match exp_ct with Prd _ -> `Prd | Cns _ -> `Cns)
                  ; actual = var_ct
                  })))
      | _ -> assert false
    in
    check_args subs expected vars