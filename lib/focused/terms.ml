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
      Γ ⊢ let v = m{Ti}(x1, ...); s
      
      Constructs a producer of T using constructor m. *)
    (* v, T_name, m, ti's, xi's, s *)
    Let of var * sym * sym * (typ list) * (var list) * command

    (* `Let` for the xtor of the built-in signature `Fun(t1, t2)`:
      let v = apply{t1, t2}(x, y); s *)
  | LetApply of var * typ * typ * var * var * command (* v, t1, t2, x, y, s *)
    (* `Let` for the xtor of the built-in signature `Forall(a, k, t)`:
      let v = instantiate{k, t}[ty_arg]; s 
      This provides a type argument ty_arg and creates a producer of Forall *)
  | LetInstantiate of var * var * typ * typ * command (* v, a, k, body_ty, s *)
    (* `Let` for the xtor of the built-in signature `Raise(t)`:
      let v = thunk{t}(x); s *)
  | LetThunk of var * typ * var * command (* v, t, x, s *)
    (* `Let` for the xtor of the built-in signature `Lower(t)`:
      let v = return{t}(x); s *)
  | LetReturn of var * typ * var * command (* v, t, x, s *)

    (* switch v {m1(y1, ...) ⇒ s1, ...}
       
      Γ(v) = prd T    for each m ∈ T: Γ, yi : Ai ⊢ si
      ------------------------------------------------ [SWITCH]
      Γ ⊢ switch v {m1(y1, ...) ⇒ s1, ...}
      
      Pattern matches on producer v of signature T. *)
    (* T_name, v, branches *)
  | Switch of sym * var * branch list

    (* switch v {apply{t1, t2}(x, y) ⇒ s} *)
  | SwitchFun of var * typ * typ * var * var * command (* v, t1, t2, x, y, s *)
    (* switch v {instantiate_k[a] ⇒ s} *)
  | SwitchForall of var * var * typ * command (* v, a, k, s *)
    (* switch v {thunk{t}(x) ⇒ s} *)
  | SwitchRaise of var * typ * var * command (* v, t, x, s *)
    (* switch v {return{t}(x) ⇒ s} *)
  | SwitchLower of var * typ * var * command (* v, t, x, s *)

    (* new v = {m1(y1, ...) ⇒ s1, ...}; s
       
      for each m ∈ T: Γ, yi : Ai ⊢ si    Γ, v : cns T ⊢ s
      ---------------------------------------------------- [NEW]
      Γ ⊢ new v = {m1(y1, ...) ⇒ s1, ...}; s
      
      Creates a consumer of T via copattern matching. *)
    (* T_name, v, branches, s *)
  | New of sym * var * branch list * command

    (* new v = {apply{t1, t2}(x, y) ⇒ s1}; s2 *)
  | NewFun of var * typ * typ * var * var * command * command (* v, t1, t2, x, y, s1, s2 *)
    (* new v = {instantiate_k_t[a] ⇒ s1}; s2 *)
  | NewForall of var * var * typ * command * command (* v, a, k, s1, s2 *)
    (* new v = {thunk{t}(x) ⇒ s1}; s2 *)
  | NewRaise of var * typ * var * command * command (* v, t, x, s1, s2 *)
    (* new v = {return{t}(x) ⇒ s1}; s2 *)
  | NewLower of var * typ * var * command * command (* v, t, x, s1, s2 *)

    (* invoke v m(x1, ...)
       
      Γ(v) = cns T    m ∈ T    Γ(xi) = Ai
      ------------------------------------ [INVOKE]
      Γ ⊢ invoke v m{ti}(x1, ...)
      
      Invokes destructor m on consumer v. *)
    (* v, T_name, m, ti's, xi's *)
  | Invoke of var * sym * sym * (typ list) * (var list)

    (* invoke v apply{t1, t2}(x, y) *)
  | InvokeApply of var * typ * typ * var * var (* v, t1, t2, x, y *)
    (* invoke v instantiate_k[ty_arg] *)
  | InvokeInstantiate of var * typ * typ (* v, ty_arg, k *)
    (* invoke v thunk{t}(x) *)
  | InvokeThunk of var * typ * var (* v, t, x *)
    (* invoke v return{t}(x) *)
  | InvokeReturn of var * typ * var (* v, t, x *)

    (* ⟨v | k⟩
       
      Γ(v) = prd τ    Γ(k) = cns τ
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

(** Instantiate an xtor's types with the declaration's type arguments *)
let instantiate_xtor (xtor: xtor) (type_args: typ list)
    : (Ident.t * typ) list * chiral_typ list * typ =
  (* Create substitution from declaration params to type args *)
  let quant_subst =
    List.fold_left2 (fun s (v, _) arg ->
      Ident.add v arg s
    ) Ident.emptytbl xtor.quantified type_args
  in
  (* Freshen existentials *)
  let fresh_exist, exist_subst = freshen_meta xtor.existentials in
  (* Combine substitutions *)
  let combined = Ident.join quant_subst exist_subst in
  (* Instantiate argument types and main type *)
  let inst_args =
    List.map (chiral_map (apply_fresh_subst combined))
      xtor.argument_types in
  let inst_main = apply_fresh_subst combined xtor.main in
  (fresh_exist, inst_args, inst_main)

(** Bind term variables with xtor argument types *)
let bind_xtor_term_args (ctx: context) (arg_types: chiral_typ list) (vars: var list)
    : context =
  List.fold_left2 (fun ctx var ct -> extend ctx var ct) ctx vars arg_types

(* ========================================================================= *)
(* Branch Checking                                                           *)
(* ========================================================================= *)

(** Check a single branch *)
let check_branch
    (ctx: context) (dec: dec) (scrutinee_args: typ list)
    (xtor_name: Path.t) (type_vars: var list) (term_vars: var list) (cmd: command)
    (check_cmd: context -> subst -> command -> unit check_result)
    (subs: subst)
    : unit check_result =
  match find_xtor dec xtor_name with
    None -> Error (UnboundXtor (dec.name, xtor_name))
  | Some xtor ->
      (* Check type variable arity *)
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
        let fresh_exist, inst_args, _ = instantiate_xtor xtor scrutinee_args in
        (* Substitute user-provided type variable names for existentials *)
        let exist_rename =
          List.fold_left2 (fun s (old_v, _) new_v ->
            Ident.add old_v (TVar new_v) s
          ) Ident.emptytbl fresh_exist type_vars
        in
        let inst_args' =
          List.map (chiral_map (apply_fresh_subst exist_rename))
            inst_args
        in
        (* Extend context with existential type vars *)
        let ctx' =
          List.fold_left2 (fun c new_v (_, k) -> extend_tyvar c new_v k)
            ctx type_vars xtor.existentials
        in
        let ctx'' = bind_xtor_term_args ctx' inst_args' term_vars in
        check_cmd ctx'' subs cmd

(** Check all branches for a Match/Switch *)
let check_switch_branches
    (ctx: context) (dec: dec) (scrutinee_args: typ list) (branches: branch list)
    (check_cmd: context -> subst -> command -> unit check_result)
    (subs: subst)
    : unit check_result =
  let* () =
    List.fold_left (fun acc (xtor_name, type_vars, term_vars, cmd) ->
      let* _ = acc in
      check_branch ctx dec scrutinee_args xtor_name
        type_vars term_vars cmd check_cmd subs
    ) (Ok ()) branches
  in
  (* Check exhaustiveness *)
  let covered = List.map (fun (xtor_name, _, _, _) -> xtor_name) branches in
  let missing = check_exhaustive ctx.types dec scrutinee_args covered in
  if missing = [] then Ok ()
  else Error (NonExhaustiveMatch { dec_name = dec.name; missing })

(** Check all branches for a New/Comatch *)
let check_new_branches
    (ctx: context) (dec: dec) (scrutinee_args: typ list) (branches: branch list)
    (check_cmd: context -> subst -> command -> unit check_result)
    (subs: subst)
    : unit check_result =
  (* Same as switch branches - branches bind arguments, check body *)
  check_switch_branches ctx dec scrutinee_args branches check_cmd subs

(* ========================================================================= *)
(* Command Type Checking                                                     *)
(* ========================================================================= *)

(** Check a command under a context, threading substitution *)
let rec check_command (ctx: context) (subs: subst) (cmd: command)
    : unit check_result =
  match cmd with
  (* let v = m{ti's}(xi's); s *)
  | Let (v, dec_name, xtor_name, type_args, term_vars, body) ->
      let* dec = lookup_dec ctx dec_name in
      (match find_xtor dec xtor_name with
        None -> Error (UnboundXtor (dec_name, xtor_name))
      | Some xtor ->
          if List.length type_args <> List.length dec.param_kinds then
            Error (ArityMismatch
              { expected = List.length dec.param_kinds
              ; got = List.length type_args
              })
          else
            let _, inst_args, inst_main =
              instantiate_xtor xtor type_args in
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

  (* let v = apply{t1, t2}(x, y); s *)
  | LetApply (v, t1, t2, x, y, body) ->
      let* x_ct = lookup_var ctx x in
      let* y_ct = lookup_var ctx y in
      let* x_ty = expect_prd x_ct in
      let* y_ty = expect_cns y_ct in
      (match unify x_ty t1 subs with
        None -> Error (UnificationFailed (x_ty, t1))
      | Some subs' ->
          (match unify y_ty t2 subs' with
            None -> Error (UnificationFailed (y_ty, t2))
          | Some subs'' ->
              let v_typ = Prd (Fun (t1, t2)) in
              check_command (extend ctx v v_typ) subs'' body))

  (* let v = instantiate{k, body_ty}[a]; s *)
  | LetInstantiate (v, a, k, body_ty, body) ->
      (* Creates producer of Forall(a, k, body_ty) *)
      let v_typ = Prd (Forall (a, k, body_ty)) in
      let ctx' = extend_tyvar ctx a k in
      check_command (extend ctx' v v_typ) subs body

  (* let v = thunk{t}(x); s *)
  | LetThunk (v, t, x, body) ->
      let* x_ct = lookup_var ctx x in
      let* x_ty = expect_cns x_ct in
      (match unify x_ty t subs with
        None -> Error (UnificationFailed (x_ty, t))
      | Some subs' ->
          let v_typ = Prd (Raise t) in
          check_command (extend ctx v v_typ) subs' body)

  (* let v = return{t}(x); s *)
  | LetReturn (v, t, x, body) ->
      let* x_ct = lookup_var ctx x in
      let* x_ty = expect_prd x_ct in
      (match unify x_ty t subs with
        None -> Error (UnificationFailed (x_ty, t))
      | Some subs' ->
          let v_typ = Prd (Lower t) in
          check_command (extend ctx v v_typ) subs' body)

  (* switch v {...} *)
  | Switch (dec_name, v, branches) ->
      let* dec = lookup_dec ctx dec_name in
      let* v_ct = lookup_var ctx v in
      let* v_ty = expect_prd v_ct in
      let* (sgn_name, sgn_args) = expect_sgn v_ty subs in
      if not (Path.equal sgn_name dec_name) then
        Error (UnificationFailed (v_ty, Sgn (dec_name, [])))
      else
        check_switch_branches ctx dec sgn_args
          branches check_command subs

  (* switch v {apply{t1, t2}(x, y) => s}
     Switch always expects v to be a producer. *)
  | SwitchFun (v, t1, t2, x, y, body) ->
      let* v_ct = lookup_var ctx v in
      let* v_ty = expect_prd v_ct in
      (match unify v_ty (Fun (t1, t2)) subs with
        None -> Error (UnificationFailed (v_ty, Fun (t1, t2)))
      | Some subs' ->
          let ctx' = extend (extend ctx x (Prd t1)) y (Cns t2) in
          check_command ctx' subs' body)

  (* switch v {instantiate_k[a] => s}
     Switch always expects v to be a producer. *)
  | SwitchForall (v, a, k, body) ->
      let* v_ct = lookup_var ctx v in
      let* v_ty = expect_prd v_ct in
      (* v should be Prd (Forall(_, k, _)) - we use fresh meta for body *)
      let body_meta = TMeta (Ident.fresh ()) in
      (match unify v_ty (Forall (a, k, body_meta)) subs with
        None -> Error (UnificationFailed (v_ty, Forall (a, k, body_meta)))
      | Some subs' ->
          let ctx' = extend_tyvar ctx a k in
          check_command ctx' subs' body)

  (* switch v {thunk{t}(x) => s} *)
  | SwitchRaise (v, t, x, body) ->
      let* v_ct = lookup_var ctx v in
      let* v_ty = expect_prd v_ct in
      (match unify v_ty (Raise t) subs with
        None -> Error (UnificationFailed (v_ty, Raise t))
      | Some subs' ->
          let ctx' = extend ctx x (Cns t) in
          check_command ctx' subs' body)

  (* switch v {return{t}(x) => s}
     Switch always expects v to be a producer. *)
  | SwitchLower (v, t, x, body) ->
      let* v_ct = lookup_var ctx v in
      let* v_ty = expect_prd v_ct in
      (match unify v_ty (Lower t) subs with
        None -> Error (UnificationFailed (v_ty, Lower t))
      | Some subs' ->
          let ctx' = extend ctx x (Prd t) in
          check_command ctx' subs' body)

  (* new v = {...}; s *)
  | New (dec_name, v, branches, body) ->
      let* dec = lookup_dec ctx dec_name in
      (* Create fresh metas for type parameters - inferred from usage *)
      let fresh_vars = freshen_kinds dec.param_kinds in
      let type_args = List.map (fun (v, _) -> TMeta v) fresh_vars in
      let* _ =
        check_new_branches ctx dec type_args branches check_command subs
      in
      let v_typ = Cns (Sgn (dec_name, type_args)) in
      check_command (extend ctx v v_typ) subs body

  (* new v = {apply{t1, t2}(x, y) => s1}; s2 *)
  | NewFun (v, t1, t2, x, y, branch_body, continuation) ->
      (* Check the branch body with x: Prd t1, y: Cns t2 *)
      let ctx_branch = extend (extend ctx x (Prd t1)) y (Cns t2) in
      let* _ = check_command ctx_branch subs branch_body in
      (* Check continuation with v: Cns (Fun(t1, t2)) *)
      let v_typ = Cns (Fun (t1, t2)) in
      check_command (extend ctx v v_typ) subs continuation

  (* new v = {instantiate{k}[a] => s1}; s2 *)
  | NewForall (v, a, k, branch_body, continuation) ->
      (* Check the branch body with type var a: k in scope *)
      let ctx_branch = extend_tyvar ctx a k in
      let* _ = check_command ctx_branch subs branch_body in
      (* The body type is inferred from usage - use fresh meta *)
      let body_meta = TMeta (Ident.fresh ()) in
      let v_typ = Cns (Forall (a, k, body_meta)) in
      check_command (extend ctx v v_typ) subs continuation

  (* new v = {thunk{t}(x) => s1}; s2 *)
  | NewRaise (v, t, x, branch_body, continuation) ->
      (* Check the branch body with x: Cns t *)
      let ctx_branch = extend ctx x (Cns t) in
      let* _ = check_command ctx_branch subs branch_body in
      (* Check continuation with v: Cns (Raise t) *)
      let v_typ = Cns (Raise t) in
      check_command (extend ctx v v_typ) subs continuation

  (* new v = {return{t}(x) => s1}; s2 *)
  | NewLower (v, t, x, branch_body, continuation) ->
      (* Check the branch body with x: Prd t *)
      let ctx_branch = extend ctx x (Prd t) in
      let* _ = check_command ctx_branch subs branch_body in
      (* Check continuation with v: Cns (Lower t) *)
      let v_typ = Cns (Lower t) in
      check_command (extend ctx v v_typ) subs continuation

  (* invoke v m{ti's}(xi's) *)
  | Invoke (v, dec_name, xtor_name, type_args, term_vars) ->
      let* dec = lookup_dec ctx dec_name in
      (match find_xtor dec xtor_name with
        None -> Error (UnboundXtor (dec_name, xtor_name))
      | Some xtor ->
          let* v_ct = lookup_var ctx v in
          let* v_ty = expect_cns v_ct in
          let* (sgn_name, sgn_args) = expect_sgn v_ty subs in
          if not (Path.equal sgn_name dec_name) then
            Error (UnificationFailed (v_ty, Sgn (dec_name, [])))
          else
            let _, inst_args, _ = instantiate_xtor xtor sgn_args in
            (* Substitute explicit type_args for existentials *)
            if List.length type_args <> List.length xtor.existentials then
              Error (TypeVarArityMismatch {
                xtor = xtor_name
              ; expected = List.length xtor.existentials
              ; got = List.length type_args
              })
            else
              let exist_subst =
                List.fold_left2 (fun s (v, _) arg ->
                  Ident.add v arg s
                ) Ident.emptytbl xtor.existentials type_args
              in
              let inst_args' =
                List.map (chiral_map (apply_fresh_subst exist_subst))
                  inst_args
              in
              check_xtor_args ctx xtor_name inst_args' term_vars subs
              |> Result.map (fun _ -> ()))

  (* invoke v apply{t1, t2}(x, y) *)
  | InvokeApply (v, t1, t2, x, y) ->
      let* v_ct = lookup_var ctx v in
      let* v_ty = expect_cns v_ct in
      (match unify v_ty (Fun (t1, t2)) subs with
        None -> Error (UnificationFailed (v_ty, Fun (t1, t2)))
      | Some subs' ->
          let* x_ct = lookup_var ctx x in
          let* y_ct = lookup_var ctx y in
          let* x_ty = expect_prd x_ct in
          let* y_ty = expect_cns y_ct in
          (match unify x_ty t1 subs' with
            None -> Error (UnificationFailed (x_ty, t1))
          | Some subs'' ->
              (match unify y_ty t2 subs'' with
                None -> Error (UnificationFailed (y_ty, t2))
              | Some _ -> Ok ())))

  (* invoke v instantiate_k[ty_arg] *)
  | InvokeInstantiate (v, _ty_arg, k) ->
      let* v_ct = lookup_var ctx v in
      let* v_ty = expect_cns v_ct in
      (* v should be Cns (Forall(a, k, body)) for some a, body *)
      let a = Ident.fresh () in
      let body_meta = TMeta (Ident.fresh ()) in
      (match unify v_ty (Forall (a, k, body_meta)) subs with
        None -> Error (UnificationFailed (v_ty, Forall (a, k, body_meta)))
      | Some _ -> Ok ())

  (* invoke v thunk{t}(x) *)
  | InvokeThunk (v, t, x) ->
      let* v_ct = lookup_var ctx v in
      let* v_ty = expect_cns v_ct in
      (match unify v_ty (Raise t) subs with
        None -> Error (UnificationFailed (v_ty, Raise t))
      | Some subs' ->
          let* x_ct = lookup_var ctx x in
          let* x_ty = expect_cns x_ct in
          (match unify x_ty t subs' with
            None -> Error (UnificationFailed (x_ty, t))
          | Some _ -> Ok ()))

  (* invoke v return{t}(x) *)
  | InvokeReturn (v, t, x) ->
      let* v_ct = lookup_var ctx v in
      let* v_ty = expect_cns v_ct in
      (match unify v_ty (Lower t) subs with
        None -> Error (UnificationFailed (v_ty, Lower t))
      | Some subs' ->
          let* x_ct = lookup_var ctx x in
          let* x_ty = expect_prd x_ct in
          (match unify x_ty t subs' with
            None -> Error (UnificationFailed (x_ty, t))
          | Some _ -> Ok ()))

  (* ⟨v | k⟩ at ty *)
  | Axiom (ty, v, k) ->
      let* v_ct = lookup_var ctx v in
      let* k_ct = lookup_var ctx k in
      let* v_ty = expect_prd v_ct in
      let* k_ty = expect_cns k_ct in
      (match unify v_ty ty subs with
        None -> Error (UnificationFailed (v_ty, ty))
      | Some subs' ->
          (match unify k_ty ty subs' with
            None -> Error (UnificationFailed (k_ty, ty))
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
      let* v_ct = lookup_var ctx v in
      let* v_ty = expect_prd v_ct in
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