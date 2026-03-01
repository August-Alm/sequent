(**
  module: Core.Terms
  description: Abstract syntax and type checking for the core language.
*)

open Common.Identifiers
open Types.CoreBase
open Types.CoreTypes

let ( let* ) = Result.bind

type var = Ident.t
type sym = Path.t

type command =
  (* ⟨producer | consumer⟩ at type *)
  | Cut of typ * term * term
  (* Call a defined function with type and term args *)
  | Call of sym * typ list * term list
  | Add of term * term * term
  | Sub of term * term * term
  | Ifz of term * command * command
  (* Explicit return - terminal command that returns a value *)
  | Ret of typ * term
  | End

and term =
    Var of var
  | Lit of int
  (* Constructors build data (are producers) *)
  (* Parameters are instantiated declaration, ctor symbol, and terms *)
  | Ctor of dec * sym * (term list)
  (* Destructors consume codata (are consumers) *)
  (* Parameters: instantiated declaration, dtor symbol, existential type args, term args *)
  | Dtor of dec * sym * (typ list) * (term list)
  (* Match consumes data (consumer) *)
  (* First argument is instantiated declaration *)
  | Match of dec * (branch list)
  (* Comatch produces codata (producer) *)
  | Comatch of dec * (branch list)
  (* μP binds consumer var, forms producer *)
  | MuPrd of typ * var * command
  (* μC binds producer var, forms consumer *)
  | MuCns of typ * var * command
  (* We treat the Forall(a, k, t) as a codata type:
      NewForall ~ comatch { instantiate[a](cont) => cmd }
    The instantiate destructor works as an xtor with
    an existentially bound type parameter `a` of kind `k`.
    The continuation `cont` is bound and receives the body result. *)
  | NewForall of var * typ * typ * var * command
  | InstantiateDtor of typ

(* xtor{t0, .., tn}(x0, .., xm) => cmd *)
and branch = sym * (var list) * (var list) * command

(* A top-level definition *)
type definition =
  { path: sym
  ; type_params: (var * typ) list
  ; term_params: (var * chiral_typ) list
  ; body: command
  }

(* Context during type-checking *)
type context =
  { types: Types.CoreTypes.context
  ; defs: definition Path.tbl
  ; term_vars: chiral_typ Ident.tbl
  }

(* ========================================================================= *)
(* Type Checking Errors                                                      *)
(* ========================================================================= *)

type check_error =
    UnboundVariable of var
  | UnboundDefinition of Path.t
  | UnboundDeclaration of Path.t
  | UnboundXtor of Path.t * Path.t
  | UnificationFailed of typ * typ
  | ChiralityMismatch of { expected_chirality: [`Prd | `Cns]; actual: chiral_typ }
  | XtorArityMismatch of { xtor: Path.t; expected: int; got: int }
  | XtorArgTypeMismatch of { xtor: Path.t; index: int; expected: chiral_typ; got: chiral_typ }
  | TypeVarArityMismatch of { xtor: Path.t; expected: int; got: int }
  | NonExhaustiveMatch of { dec_name: Path.t; missing: Path.t list }
  | CallTypeArityMismatch of { defn: Path.t; expected: int; got: int }
  | CallTermArityMismatch of { defn: Path.t; expected: int; got: int }
  | CallArgTypeMismatch of { defn: Path.t; index: int; expected: chiral_typ; got: chiral_typ }
  | AddTypeMismatch of { arg1: chiral_typ; arg2: chiral_typ; result: chiral_typ }
  | IfzConditionNotInt of chiral_typ

type 'a check_result = ('a, check_error) result

(* ========================================================================= *)
(* Type Checking Context and Helpers                                         *)
(* ========================================================================= *)

(* Create an initial context from type declarations and term definitions *)
let make_tc_context (type_defs: dec Path.tbl) (defs: definition Path.tbl) : context =
  let tyctx = List.fold_left (fun ctx ((p, dec): (Path.t * dec)) ->
    { ctx with decs = Path.add p dec ctx.decs }
  ) empty_context (Path.to_list type_defs) in
  { types = tyctx; term_vars = Ident.emptytbl; defs = defs }

(** Lookup a definition by path *)
let lookup_def (ctx: context) (p: Path.t) : definition check_result =
  match Path.find_opt p ctx.defs with
    Some d -> Ok d | None -> Error (UnboundDefinition p)

(** Lookup a declaration (data/codata type) by path *)
let lookup_dec (ctx: context) (p: Path.t) : (dec, check_error) result =
  match Path.find_opt p ctx.types.decs with
    Some d -> Ok d | None -> Error (UnboundDeclaration p)

(** Find an xtor in a declaration *)
let find_xtor (dec: dec) (xtor_name: Path.t) : xtor option =
  List.find_opt (fun (x: xtor) -> Path.equal x.name xtor_name) dec.xtors

(** Instantiate a type by substituting type parameters with arguments *)
let instantiate_typ (params: (var * typ) list) (args: typ list) (t: typ) : typ =
  let subst =
    List.fold_left2 (fun s (v, _) arg -> Ident.add v arg s)
      Ident.emptytbl params args
  in apply_fresh_subst subst t

(** Instantiate a chiral type *)
let instantiate_chiral (params: (var * typ) list) (args: typ list) (ct: chiral_typ)
    : chiral_typ =
  chiral_map (instantiate_typ params args) ct

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

(* ========================================================================= *)
(* Xtor Argument Checking with Unification                                   *)
(* ========================================================================= *)

(** Bind variables from an xtor's arguments into context *)
let bind_xtor_term_args (ctx: context) (arg_types: chiral_typ list) (vars: var list)
    : context =
  List.fold_left2 (fun ctx var ct -> extend ctx var ct) ctx vars arg_types

(** Check that actual arguments match xtor's declared chiralities with unification *)
let rec simple_typ_str = function
  | TVar v -> Ident.name v
  | TMeta m -> "?" ^ Ident.name m
  | Sgn (p, args) -> Path.name p ^ "(" ^ String.concat ", " (List.map simple_typ_str args) ^ ")"
  | Forall (v, _, body) -> "∀" ^ Ident.name v ^ ". " ^ simple_typ_str body
  | Arrow (a, b) -> simple_typ_str a ^ " -> " ^ simple_typ_str b
  | _ -> "?"

let check_xtor_args
    (ctx: context)
    (xtor_name: Path.t) (expected: chiral_typ list) (args: term list)
    (infer: context -> term -> (chiral_typ * subst) check_result)
    (subs: subst)
    : (subst, check_error) result =
  if List.length args <> List.length expected then
    Error (XtorArityMismatch {
      xtor = xtor_name; expected = List.length expected; got = List.length args })
  else
    let rec check_args idx subs args expected =
      match args, expected with
        [], [] -> Ok subs
      | arg :: args', exp_ct :: exps' ->
          let* (got_ct, subs') = infer ctx arg in
          let exp_typ = strip_chirality exp_ct in
          let got_typ = strip_chirality got_ct in
          (match unify exp_typ got_typ subs' with
            None -> Error (UnificationFailed (exp_typ, got_typ))
          | Some subs'' ->
              (* Chirality must also match *)
              (match exp_ct, got_ct with
                Prd _, Prd _ | Cns _, Cns _ -> check_args (idx + 1) subs'' args' exps'
              | _ -> Error (XtorArgTypeMismatch {
                  xtor = xtor_name; index = idx; expected = exp_ct; got = got_ct })))
      | _ -> assert false
    in
    check_args 0 subs args expected

(* ========================================================================= *)
(* Branch Checking                                                           *)
(* ========================================================================= *)

(** Freshen an xtor's existential types with fresh metavariables.
    For instantiated declarations, quantified is empty so we only freshen existentials. *)
let freshen_xtor_existentials (xtor: xtor)
    : (chiral_typ list * typ) =
  (* Freshen existential variables only - quantified is empty for instantiated dec *)
  let _, exist_subst = freshen_meta xtor.existentials in
  let inst_args =
    List.map (chiral_map (apply_fresh_subst exist_subst))
      xtor.argument_types
  in
  let inst_main = apply_fresh_subst exist_subst xtor.main in
  (inst_args, inst_main)

(** Apply a type substitution to all types in a command.
    Used for GADT refinement to convert TVars to TMetas before checking. *)
let rec refine_cmd_types (subst: typ Ident.tbl) (cmd: command) : command =
  let refine_typ = apply_fresh_subst subst in
  let refine_term t = refine_term_types subst t in
  match cmd with
    Cut (ty, t1, t2) -> Cut (refine_typ ty, refine_term t1, refine_term t2)
  | Call (path, type_args, term_args) ->
      Call (path, List.map refine_typ type_args, List.map refine_term term_args)
  | Add (t1, t2, t3) -> Add (refine_term t1, refine_term t2, refine_term t3)
  | Sub (t1, t2, t3) -> Sub (refine_term t1, refine_term t2, refine_term t3)
  | Ifz (t, c1, c2) ->
      Ifz (refine_term t, refine_cmd_types subst c1, refine_cmd_types subst c2)
  | Ret (ty, t) -> Ret (refine_typ ty, refine_term t)
  | End -> End

and refine_term_types (subst: typ Ident.tbl) (term: term) : term =
  let refine_typ = apply_fresh_subst subst in
  let refine_chiral ct = chiral_map refine_typ ct in
  let refine_term t = refine_term_types subst t in
  let refine_dec (d: dec) : dec =
    { d with
      type_args = List.map refine_typ d.type_args
    ; xtors = List.map (fun (x: xtor) ->
        { x with
          argument_types = List.map refine_chiral x.argument_types
        ; main = refine_typ x.main
        }) d.xtors
    }
  in
  let refine_branch (xtor, tvs, tms, cmd) = (xtor, tvs, tms, refine_cmd_types subst cmd) in
  match term with
    Var v -> Var v
  | Lit n -> Lit n
  | Ctor (dec, xtor, args) -> Ctor (refine_dec dec, xtor, List.map refine_term args)
  | Dtor (dec, xtor, ty_args, args) ->
      Dtor (refine_dec dec, xtor, List.map refine_typ ty_args, List.map refine_term args)
  | Match (dec, branches) -> Match (refine_dec dec, List.map refine_branch branches)
  | Comatch (dec, branches) -> Comatch (refine_dec dec, List.map refine_branch branches)
  | MuPrd (ty, v, cmd) -> MuPrd (refine_typ ty, v, refine_cmd_types subst cmd)
  | MuCns (ty, v, cmd) -> MuCns (refine_typ ty, v, refine_cmd_types subst cmd)
  | NewForall (a, k, body_ty, cont, cmd) ->
      NewForall (a, refine_typ k, refine_typ body_ty, cont, refine_cmd_types subst cmd)
  | InstantiateDtor ty -> InstantiateDtor (refine_typ ty)

(** Apply a type substitution to all variable types in a context.
    Used for GADT refinement so that variables from outer scope get their TVars
    converted to TMetas that can be unified with the refined types. *)
let refine_context (subst: typ Ident.tbl) (ctx: context) : context =
  let refine_chiral ct = chiral_map (apply_fresh_subst subst) ct in
  { ctx with term_vars = Ident.map_tbl refine_chiral ctx.term_vars }

(** Check a single branch: bind vars with xtor's chiralities, check command.
    For instantiated declarations, xtor.quantified is empty. *)
let check_branch
    (ctx: context) (dec: dec)
    (xtor_name: Path.t) (type_vars: var list) (term_vars: var list) (cmd: command)
    (check_cmd: context -> subst -> command -> unit check_result)
    (subs: subst)
    : unit check_result =
  (* Find the xtor in the instantiated declaration *)
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
        Error (XtorArityMismatch
          { xtor = xtor_name
          ; expected = List.length xtor.argument_types
          ; got = List.length term_vars })
      else
        (* GADT refinement: create fresh metas from TVars in dec.type_args so they
           can be unified with the xtor's result type. *)
        let (fresh_metas, meta_type_args) =
          List.fold_right (fun ty (metas, args) ->
            match apply_subst subs ty with
              TVar v ->
                let m = Ident.mk (Ident.name v) in
                ((v, m) :: metas, TMeta m :: args)
            | other -> (metas, other :: args)
          ) dec.type_args ([], [])
        in
        
        (* Unify xtor's main type with the scrutinee type (using metas).
           The xtor.main in instantiated decs already has quantified vars resolved. *)
        let scrutinee_type = Sgn (dec.name, meta_type_args) in
        let branch_subs = match unify xtor.main scrutinee_type subs with
            Some s -> s
          | None -> subs  (* If unification fails, continue with original subs *)
        in
        
        (* For GADT refinement: convert TVars in the command to their corresponding metas.
           This is crucial: the command may contain types like vec(a, n) where n is a TVar.
           After unification, branch_subs has ?m = zero. But apply_subst doesn't substitute
           TVars, only TMetas. So we use apply_fresh_subst to convert vec(a, TVar n) →
           vec(a, TMeta ?m), which then unifies correctly via apply_subst. *)
        let tvar_to_meta = List.fold_left (fun s (orig_var, meta_var) ->
          Ident.add orig_var (TMeta meta_var) s
        ) Ident.emptytbl fresh_metas in
        let refined_cmd = refine_cmd_types tvar_to_meta cmd in
        (* Also refine the context: variables from outer scope have TVars that need to be
           converted to the same TMetas, so apply_subst can resolve GADT refinements *)
        let refined_ctx = refine_context tvar_to_meta ctx in
        
        (* Substitute user-provided type variable names for existentials.
           Don't freshen - the user's type vars are the "fresh" names for this branch. *)
        let exist_subst =
          List.fold_left2 (fun s (old_v, _) new_v ->
            Ident.add old_v (TVar new_v) s
          ) Ident.emptytbl xtor.existentials type_vars
        in
        let inst_args =
          List.map (chiral_map (apply_fresh_subst exist_subst)) xtor.argument_types
        in
        (* Extend context with existential type vars and term vars *)
        let ctx' =
          List.fold_left2 (fun c new_v (_, k) -> extend_tyvar c new_v k)
            refined_ctx type_vars xtor.existentials
        in
        let ctx'' = bind_xtor_term_args ctx' inst_args term_vars in
        check_cmd ctx'' branch_subs refined_cmd

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
      check_branch ctx dec xtor_name type_vars term_vars cmd check_cmd subs
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
(* Type Inference with Unification                                           *)
(* ========================================================================= *)

(** Check call arguments against instantiated parameter types *)
let check_call_args
    (ctx: context)
    (defn_path: Path.t) (params: (var * chiral_typ) list) (args: term list)
    (infer: context -> term -> (chiral_typ * subst) check_result)
    (subs: subst)
    : (subst, check_error) result =
  if List.length args <> List.length params then
    Error (CallTermArityMismatch
      { defn = defn_path
      ; expected = List.length params
      ; got = List.length args
      })
  else
    let rec check_args idx subs args params =
      match args, params with
        [], [] -> Ok subs
      | arg :: args', (_, exp_ct) :: params' ->
          let* (got_ct, subs') = infer ctx arg in
          let exp_typ = strip_chirality exp_ct in
          let got_typ = strip_chirality got_ct in
          (match unify exp_typ got_typ subs' with
            None -> Error (UnificationFailed (exp_typ, got_typ))
          | Some subs'' ->
              (match exp_ct, got_ct with
                Prd _, Prd _ | Cns _, Cns _ ->
                  check_args (idx + 1) subs'' args' params'
              | _ -> Error (CallArgTypeMismatch
                  { defn = defn_path; index = idx
                  ; expected = exp_ct; got = got_ct
                  })))
      | _ -> assert false
    in
    check_args 0 subs args params

(** Infer the chiral type of a term, threading substitution *)
let rec infer_typ (ctx: context) (subs: subst) (tm: term)
    : (chiral_typ * subst) check_result =
  match tm with
    Var x -> let* ct = lookup_var ctx x in Ok (ct, subs)
  | Lit _ -> Ok (Prd (Ext Int), subs)
  | Ctor (dec, xtor_name, term_args) ->
      (* dec is already instantiated - just find the xtor and use its types directly *)
      (match find_xtor dec xtor_name with
        None -> Error (UnboundXtor (dec.name, xtor_name))
      | Some xtor ->
          (* Freshen existentials for this usage *)
          let inst_args, inst_main = freshen_xtor_existentials xtor in
          (* Check term arguments *)
          let* subs' = check_xtor_args ctx xtor_name inst_args term_args
            (fun c tm -> infer_typ c subs tm) subs in
          (* Ctor produces Prd (producer) of the result type *)
          Ok (Prd inst_main, subs'))
  | Dtor (dec, xtor_name, exist_ty_args, term_args) ->
      (* dec is already instantiated - just find the xtor and use its types directly *)
      (match find_xtor dec xtor_name with
        None -> Error (UnboundXtor (dec.name, xtor_name))
      | Some xtor ->
          (* Apply existential type args to specialize the xtor *)
          let exist_subst = List.fold_left2 (fun s (v, _k) ty ->
            Ident.add v ty s
          ) Ident.emptytbl xtor.existentials exist_ty_args in
          let inst_args = List.map (chiral_map (apply_fresh_subst exist_subst)) xtor.argument_types in
          let inst_main = apply_fresh_subst exist_subst xtor.main in
          let* subs' = check_xtor_args ctx xtor_name inst_args term_args
            (fun c tm -> infer_typ c subs tm) subs in
          (* Dtor produces Cns (consumer) of the result type *)
          Ok (Cns inst_main, subs'))
  | Match (dec, branches) ->
      (* dec is already instantiated with param_kinds = [] *)
      let* _ = check_branches ctx dec branches check_command subs in
      (* Match produces Cns (consumer) of the data type *)
      Ok (Cns (Sgn (dec.name, dec.type_args)), subs)
  | Comatch (dec, branches) ->
      (* dec is already instantiated with param_kinds = [] *)
      let* _ = check_branches ctx dec branches check_command subs in
      (* Comatch produces Prd (producer) of the codata type *)
      Ok (Prd (Sgn (dec.name, dec.type_args)), subs)
  | MuPrd (ty, x, cmd) ->
      (* μP binds x : Cns ty, produces Prd ty *)
      let ctx' = extend ctx x (Cns ty) in
      let* _ = check_command ctx' subs cmd in
      Ok (Prd ty, subs)
  | MuCns (ty, k, cmd) ->
      (* μC binds k : Prd ty, produces Cns ty *)
      let ctx' = extend ctx k (Prd ty) in
      let* _ = check_command ctx' subs cmd in
      Ok (Cns ty, subs)
  | NewForall (a, k, body_ty, cont, cmd) ->
      (* NewForall ~ comatch { instantiate[a: k](cont) => cmd }
         Binds type var a : k and term var cont : Cns body_ty
         Produces Prd (Forall a k body_ty) *)
      let ctx' = extend_tyvar ctx a k in
      let ctx'' = extend ctx' cont (Cns body_ty) in
      let* _ = check_command ctx'' subs cmd in
      Ok (Prd (Forall (a, k, body_ty)), subs)
  | InstantiateDtor ty_arg ->
      (* instantiate destructor: given a type argument, consumes Forall
         We need a fresh meta for the quantified kind and body *)
      let a = Ident.fresh () in
      let k = TMeta (Ident.fresh ()) in
      let body = TMeta (Ident.fresh ()) in
      (* Substitute ty_arg for a in body *)
      let inst_body = apply_fresh_subst (Ident.add a ty_arg Ident.emptytbl) body in
      Ok (Cns (Forall (a, k, inst_body)), subs)

(** Check a command under context and substitution *)
and check_command (ctx: context) (subs: subst) (cmd: command) : unit check_result =
  match cmd with
    Cut (ret_ty, t1, t2) ->
      let* (t1_ct, subs') = infer_typ ctx subs t1 in
      let* (t2_ct, subs'') = infer_typ ctx subs' t2 in
      let* t1_ty = expect_prd t1_ct in
      let* t2_ty = expect_cns t2_ct in
      (* Unify producer and consumer with the declared cut type *)
      (match unify t1_ty ret_ty subs'' with
        None -> Error (UnificationFailed (t1_ty, ret_ty))
      | Some subs''' ->
          (match unify t2_ty ret_ty subs''' with
          | None -> Error (UnificationFailed (t2_ty, ret_ty))
          | Some _ -> Ok ()))
  | Call (path, type_args, term_args) ->
      let* defn = lookup_def ctx path in
      if List.length type_args <> List.length defn.type_params then
        Error (CallTypeArityMismatch
          { defn = path
          ; expected = List.length defn.type_params
          ; got = List.length type_args })
      else
        (* Instantiate term parameter types with type arguments *)
        let inst_params = List.map (fun (v, ct) ->
          (v, instantiate_chiral defn.type_params type_args ct)
        ) defn.term_params in
        let* _ = check_call_args ctx path inst_params term_args
          (fun c tm -> infer_typ c subs tm) subs in
        Ok ()
  | Add (t1, t2, t3) ->
      let* (t1_ct, subs') = infer_typ ctx subs t1 in
      let* (t2_ct, subs'') = infer_typ ctx subs' t2 in
      let* (t3_ct, subs''') = infer_typ ctx subs'' t3 in
      let int_prd = Prd (Ext Int) in
      let int_cns = Cns (Ext Int) in
      (match unify (strip_chirality t1_ct) (Ext Int) subs''' with
        None -> Error (AddTypeMismatch { arg1 = t1_ct; arg2 = t2_ct; result = t3_ct })
      | Some subs4 ->
          (match unify (strip_chirality t2_ct) (Ext Int) subs4 with
            None -> Error (AddTypeMismatch { arg1 = t1_ct; arg2 = t2_ct; result = t3_ct })
          | Some _ ->
              (* t1, t2 should be Prd Int, t3 should be Cns Int *)
              if t1_ct = int_prd && t2_ct = int_prd && t3_ct = int_cns then Ok ()
              else Error (AddTypeMismatch { arg1 = t1_ct; arg2 = t2_ct; result = t3_ct })))
  | Sub (t1, t2, t3) ->
      let* (t1_ct, subs') = infer_typ ctx subs t1 in
      let* (t2_ct, subs'') = infer_typ ctx subs' t2 in
      let* (t3_ct, subs''') = infer_typ ctx subs'' t3 in
      let int_prd = Prd (Ext Int) in
      let int_cns = Cns (Ext Int) in
      (match unify (strip_chirality t1_ct) (Ext Int) subs''' with
        None -> Error (AddTypeMismatch { arg1 = t1_ct; arg2 = t2_ct; result = t3_ct })
      | Some subs4 ->
          (match unify (strip_chirality t2_ct) (Ext Int) subs4 with
            None -> Error (AddTypeMismatch { arg1 = t1_ct; arg2 = t2_ct; result = t3_ct })
          | Some _ ->
              (* t1, t2 should be Prd Int, t3 should be Cns Int *)
              if t1_ct = int_prd && t2_ct = int_prd && t3_ct = int_cns then Ok ()
              else Error (AddTypeMismatch { arg1 = t1_ct; arg2 = t2_ct; result = t3_ct })))
  | Ifz (t, cmd1, cmd2) ->
      let* (t_ct, subs') = infer_typ ctx subs t in
      (match unify (strip_chirality t_ct) (Ext Int) subs' with
        None -> Error (IfzConditionNotInt t_ct)
      | Some subs'' ->
          let* _ = expect_prd t_ct in
          let* _ = check_command ctx subs'' cmd1 in
          check_command ctx subs'' cmd2)
  | Ret (_ty, t) ->
      (* Ret returns a producer value - just check it's a valid producer *)
      let* (t_ct, _subs') = infer_typ ctx subs t in
      let* _ = expect_prd t_ct in
      Ok ()
  | End ->
      Ok ()

let check_def (ctx: context) (def: definition) : definition check_result =
  let ctx' = List.fold_left (fun c (v, ct) -> extend c v ct) ctx def.term_params in
  let* _ = check_command ctx' Ident.emptytbl def.body in
  Ok def