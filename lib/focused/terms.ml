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

    (* jump s  

      Θ(l) = Γ
      ---------- [JUMP]
      Γ ⊢ jump l 
    
    Jump: Go to top-level definition/label *)
  | Jump of sym * (var list)

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
  | UnboundDefinition of Path.t
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

type definition =
  { path: sym
  ; term_params: (var * chiral_typ) list
  ; body: command
  }

type context =
  { types: Types.FocusedTypes.context
  ; defs: definition Path.tbl
  ; term_vars: chiral_typ Ident.tbl
  }

(** Create an initial context from type declarations and term definitions *)
let make_tc_context (type_defs: dec Path.tbl) (defs: definition Path.tbl) : context =
  let tyctx = List.fold_left (fun ctx ((p, dec): (Path.t * dec)) ->
    { ctx with decs = Path.add p dec ctx.decs }
  ) empty_context (Path.to_list type_defs) in
  { types = tyctx; term_vars = Ident.emptytbl; defs = defs }

(** Lookup a declaration (data/codata type) by path *)
let lookup_dec (ctx: context) (p: Path.t) : (dec, check_error) result =
  match Path.find_opt p ctx.types.decs with
    Some d -> Ok d | None -> Error (UnboundDeclaration p)

(** Lookup a definition (top-level label) by path *)
let lookup_def (ctx: context) (p: Path.t) : (definition, check_error) result =
  match Path.find_opt p ctx.defs with
    Some d -> Ok d | None -> Error (UnboundDefinition p)

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

(** Freshen an xtor's type parameters for pattern matching.
    Both quantified and existential parameters become existentially bound when matching.
    Returns: (fresh_metas, inst_args, inst_main) where fresh_metas maps original params to fresh TMetas *)
let freshen_xtor_type_params (xtor: xtor)
    : (Ident.t list * chiral_typ list * typ) =
  (* For pattern matching, both quantified and existentials are freshened *)
  let all_params = xtor.quantified @ xtor.existentials in
  let fresh_metas_with_kinds, subst = freshen_meta all_params in
  let fresh_metas = List.map fst fresh_metas_with_kinds in
  let inst_args =
    List.map (chiral_map (apply_fresh_subst subst))
      xtor.argument_types in
  let inst_main = apply_fresh_subst subst xtor.main in
  (fresh_metas, inst_args, inst_main)

(** Bind term variables with xtor argument types *)
let bind_xtor_term_args (ctx: context) (arg_types: chiral_typ list) (vars: var list)
    : context =
  List.fold_left2 (fun ctx var ct -> extend ctx var ct) ctx vars arg_types

(** Apply a type substitution to all variable types in a context.
    Used for GADT refinement so that variables from outer scope get their TVars
    converted to TMetas that can be unified with the refined types. *)
let refine_context (subst: typ Ident.tbl) (ctx: context) : context =
  let refine_chiral ct = chiral_map (apply_fresh_subst subst) ct in
  { ctx with term_vars = Ident.map_tbl refine_chiral ctx.term_vars }

(* ========================================================================= *)
(* Branch Checking                                                           *)
(* ========================================================================= *)

(** Check a single branch with GADT refinement.
    For data: quantified is existentially bound (matching introduces them).
    For codata: quantified is also existentially bound (matching on codata introduces them).
    So type_vars should match the total of quantified + existentials.
    
    GADT Refinement: When dec.type_args contains TVars, we unify the xtor's result
    type with the scrutinee type to learn constraints (e.g., n = 'zero). *)
let check_branch
    (ctx: context) (dec: dec)
    (xtor_name: Path.t) (type_vars: var list) (term_vars: var list) (cmd: command)
    (check_cmd: context -> subst -> command -> unit check_result)
    (subs: subst)
    : unit check_result =
  match find_xtor dec xtor_name with
    None -> Error (UnboundXtor (dec.name, xtor_name))
  | Some xtor ->
      (* For both data and codata, pattern matching binds both quantified and existentials.
         For data ctors: quantified are the universals, but matching introduces them existentially.
         For codata dtors: quantified AND existentials are introduced by matching. *)
      let all_type_params = xtor.quantified @ xtor.existentials in
      let num_type_vars = List.length all_type_params in
      if List.length type_vars <> num_type_vars then
        Error (TypeVarArityMismatch {
          xtor = xtor_name; expected = num_type_vars; got = List.length type_vars })
      (* Check term variable arity *)
      else if List.length term_vars <> List.length xtor.argument_types then
        Error (XtorArityMismatch {
          xtor = xtor_name
        ; expected = List.length xtor.argument_types
        ; got = List.length term_vars })
      else
        (* GADT Refinement: For types in dec.type_args that are TMetas or TVars,
           we'll include them in scrutinee_ty for unification with xtor.main.
           TMetas can be directly refined; TVars need fresh metas. *)
        let (tvar_to_meta, scrutinee_meta_args) =
          List.fold_right (fun ty (mapping, args) ->
            (* Don't apply subs here - we want the actual types from unified_dec,
               not the resolved values. The unified_dec already has TMetas. *)
            match ty with
              TMeta _ -> mapping, ty :: args
            | TVar v ->
                (* TVar - create fresh meta *)
                let m = Ident.mk (Ident.name v) in
                ((v, m) :: mapping, TMeta m :: args)
            | other -> (mapping, other :: args)
          ) dec.type_args ([], [])
        in
        let scrutinee_ty = Sgn (dec.name, scrutinee_meta_args) in
        
        (* Unify xtor's result type with scrutinee type to learn GADT constraints.
           IMPORTANT: Use empty substitution, not incoming subs. The incoming subs
           may have TMeta -> TVar mappings that would prevent GADT refinement.
           We merge the GADT refinements with subs afterward. *)
        let branch_subs = match unify xtor.main scrutinee_ty Ident.emptytbl with
            Some gadt_subs ->
              (* Merge: GADT refinements override incoming subs for TMetas we care about *)
              List.fold_left (fun acc (k, v) ->
                Ident.add k v acc
              ) subs (Ident.to_list gadt_subs)
          | None -> 
              subs  (* If unification fails, continue with original subs *)
        in
        
        (* Convert TVars in context to TMetas so apply_subst can resolve them.
           Only needed if we created new TMetas for TVars in dec.type_args.
           If dec.type_args already had TMetas, the context should too - no refinement needed. *)
        let refined_ctx = if tvar_to_meta = [] then ctx else begin
          let tvar_subst = List.fold_left (fun s (orig_var, meta_var) ->
            Ident.add orig_var (TMeta meta_var) s
          ) Ident.emptytbl tvar_to_meta in
          refine_context tvar_subst ctx
        end in
        
        (* For pattern matching:
           - quantified: need to freshen (not yet freshened by instantiate_dec)
           - existentials: already fresh from instantiate_dec (for GADT xtors)
           We must use the SAME metas that GADT unification used for existentials. *)
        let fresh_quant_metas, quant_subst = freshen_meta xtor.quantified in
        let fresh_quant_ids = List.map fst fresh_quant_metas in
        let existing_exist_ids = List.map fst xtor.existentials in
        let all_fresh_metas = fresh_quant_ids @ existing_exist_ids in
        
        (* Apply substitution only to quantified parts of argument types *)
        let inst_args = List.map (chiral_map (apply_fresh_subst quant_subst)) xtor.argument_types in
        
        (* Instead of substituting user names into inst_args, we keep the fresh metas
           and add user_var -> fresh_meta mappings to the substitution.
           This way, when the body uses TVar m, it resolves to TMeta n#1127.
           Skip adding mapping if user_var IS the meta (from eta-expansion). *)
        let branch_subs_with_tyvars =
          List.fold_left2 (fun s meta user_var ->
            if Ident.equal meta user_var then s  (* Already a meta, no mapping needed *)
            else Ident.add user_var (TMeta meta) s
          ) branch_subs all_fresh_metas type_vars
        in
        
        (* Extend context with type vars (for kind checking) *)
        let ctx' =
          List.fold_left2 (fun c new_v (_, k) -> extend_tyvar c new_v k)
            refined_ctx type_vars all_type_params
        in
        let ctx'' = bind_xtor_term_args ctx' inst_args term_vars in
        check_cmd ctx'' branch_subs_with_tyvars cmd

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
    Let (v, dec, xtor_name, term_vars, body) ->
      (match find_xtor dec xtor_name with
        None -> Error (UnboundXtor (dec.name, xtor_name))
      | Some xtor ->
          (* Freshen type params for construction *)
          let _, inst_args, inst_main = freshen_xtor_type_params xtor in
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
      (* Apply subs to get the actual scrutinee type *)
      let resolved_v_ty = apply_subst subs v_ty in
      (* Extract actual type args from resolved scrutinee type for GADT refinement *)
      let actual_type_args = match resolved_v_ty with
          Sgn (_, args) -> args
        | _ -> dec.type_args  (* Fallback to dec.type_args if not a Sgn *)
      in
      (* Create unified dec with actual type args for branch checking *)
      let unified_dec = { dec with type_args = actual_type_args } in
      (* The expected type is the instantiated signature *)
      let expected_ty = Sgn (dec.name, dec.type_args) in
      (* Unify v's type with the expected signature *)
      (match unify v_ty expected_ty subs with
        None -> Error (UnificationFailed (v_ty, expected_ty))
      | Some subs' ->
          check_branches ctx unified_dec branches check_command subs')

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
          (match expect_cns v_ct with
            Error e -> Error e
          | Ok v_ty ->
              let expected_ty = Sgn (dec.name, dec.type_args) in
              (match unify v_ty expected_ty subs with
                None -> Error (UnificationFailed (v_ty, expected_ty))
              | Some subs' ->
                  (* Freshen type params for invocation *)
                  let _, inst_args, _ = freshen_xtor_type_params xtor in
                  check_xtor_args ctx xtor_name inst_args term_vars subs'
                  |> Result.map (fun _ -> ()))))

  (* ⟨v | k⟩ at ty *)
  | Axiom (ty, v, k) ->
      let* v_ct = lookup_var ctx v in
      let* k_ct = lookup_var ctx k in
      let* v_ty = expect_prd v_ct in
      (match expect_cns k_ct with
        Error e -> Error e
      | Ok k_ty ->
      (match unify v_ty (Ext ty) subs with
        None -> Error (UnificationFailed (v_ty, Ext ty))
      | Some subs' ->
          (match unify k_ty (Ext ty) subs' with
            None -> Error (UnificationFailed (k_ty, Ext ty))
          | Some _ -> Ok ())))

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

  (* jump l(args) - jump to top-level definition with arguments *)
  | Jump (label, args) ->
      let* def = lookup_def ctx label in
      (* Check arity *)
      if List.length args <> List.length def.term_params then
        Error (ArityMismatch {
          expected = List.length def.term_params;
          got = List.length args
        })
      else
        (* Check each argument has the expected type *)
        let rec check_args subs params args =
          match params, args with
          | [], [] -> Ok ()
          | (_, exp_ct) :: params', arg :: args' ->
              let* arg_ct = lookup_var ctx arg in
              let exp_ty = strip_chirality exp_ct in
              let arg_ty = strip_chirality arg_ct in
              (match unify exp_ty arg_ty subs with
              | None -> Error (UnificationFailed (exp_ty, arg_ty))
              | Some subs' ->
                  (* Check chirality matches *)
                  (match exp_ct, arg_ct with
                    Prd _, Prd _ | Cns _, Cns _ ->
                      check_args subs' params' args'
                  | _ -> 
                      Error (ChiralityMismatch
                      { expected_chirality =
                          (match exp_ct with Prd _ -> `Prd | Cns _ -> `Cns)
                      ; actual = arg_ct
                      })))
          | _ -> assert false
        in
        check_args subs def.term_params args

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
    let rec check_args idx subs expected vars =
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
                  check_args (idx + 1) subs' exps' vars'
              | _ -> 
                  Error (ChiralityMismatch
                  { expected_chirality =
                      (match exp_ct with Prd _ -> `Prd | Cns _ -> `Cns)
                  ; actual = var_ct
                  })))
      | _ -> assert false
    in
    check_args 0 subs expected vars

let check_def (ctx: context) (def: definition) : definition check_result =
  let ctx' = List.fold_left (fun c (v, ct) -> extend c v ct) ctx def.term_params in
  let* _ = check_command ctx' Ident.emptytbl def.body in
  Ok def