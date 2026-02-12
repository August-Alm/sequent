(**
  module: Common.Types
  description: A type system common to sequent calculus-based intermediate languages.
*)

open Identifiers

type sym = Path.t

type kind =
    Star
  | Arrow of kind * kind

type ext_typ =
    Int
  
type typ =
    Ext of ext_typ (* Built-in, externally implemented types *)
  | Var of var_typ ref (* Free, local type variable *)
  | Rigid of Ident.t (* Rigid/skolem variable *)
  | Sym of sym * sgn_typ Lazy.t (* Reference to a signature *)
  | App of typ * (typ list) (* Instantiation *)
  | Sgn of sgn_typ (* An instantiated signature *)

and var_typ =
    Unbound of Ident.t
  | Link of typ

(* Signatures are not polarised as data or codata, but can
 function as both, depending on context *)
and sgn_typ =
  { name: sym
  ; parameters: (Ident.t * kind) list
  ; xtors: xtor list
  }

(* Unifying, unpolarized notion constructors and destructors *)
and xtor =
  { name: sym
  ; parent: sym
  ; parameters: (Ident.t * kind) list 
  ; existentials: (Ident.t * kind) list
  ; arguments: chiral_typ list
  (* `main` is result type if considered as constructor, the "this"
    type if considered as destructor *)
  ; main: typ
  }

(* Typing judgements in sequent calculi distinguish between
left (producer) terms and right (consumer) terms *)
and chiral_typ =
    Lhs of typ (* Producer *)
  | Rhs of typ (* Consumer *)

and equation =
  | Equal of typ * typ
  | And of equation * equation
  | Exists of var_typ * equation 
  | Implies of equation * equation
  | True

let chiral_map (f: typ -> typ) (ct: chiral_typ) : chiral_typ =
  match ct with
    Lhs t -> Lhs (f t)
  | Rhs t -> Rhs (f t)

(** Substitute rigid type variables with types in a type.
    Used for instantiating signature parameters. *)
let rec subst_rigid (mapping: (Ident.t * typ) list) (t: typ) : typ =
  match t with
  | Rigid id ->
      (match List.assoc_opt id mapping with
       | Some t' -> t'
       | None -> t)
  | Var ({contents = Link t'}) -> subst_rigid mapping t'
  | Var _ -> t
  | App (f, args) -> App (subst_rigid mapping f, List.map (subst_rigid mapping) args)
  | Sgn s -> Sgn (subst_rigid_sgn mapping s)
  | Ext _ | Sym (_, _) -> t

and subst_rigid_sgn (mapping: (Ident.t * typ) list) (s: sgn_typ) : sgn_typ =
  (* Don't substitute parameters that are shadowed by the signature's own params *)
  let shadowed = List.map fst s.parameters in
  let mapping' = List.filter (fun (id, _) -> not (List.mem id shadowed)) mapping in
  { s with
    xtors = List.map (subst_rigid_xtor mapping') s.xtors
  }

and subst_rigid_xtor (mapping: (Ident.t * typ) list) (x: xtor) : xtor =
  (* Don't substitute parameters shadowed by xtor's own params or existentials *)
  let shadowed = List.map fst x.parameters @ List.map fst x.existentials in
  let mapping' = List.filter (fun (id, _) -> not (List.mem id shadowed)) mapping in
  { x with
    arguments = List.map (chiral_map (subst_rigid mapping')) x.arguments
  ; main = subst_rigid mapping' x.main
  }

type solving_env =
  { subst: (var_typ ref * typ) list (* Current substitution - keyed by ref *)
  ; local_eqs: (typ * typ) list (* Local assumptions (from GADT matches) *)
  }

let empty_env : solving_env = { subst = []; local_eqs = [] }

(** Find a var ref in the substitution using physical equality *)
let rec find_subst (r: var_typ ref) (subst: (var_typ ref * typ) list) : typ option =
  match subst with
    [] -> None
  | (r', t) :: _ when r == r' -> Some t
  | _ :: rest -> find_subst r rest

(** Occurs check: does variable r occur in type t? *)
let rec occurs (r: var_typ ref) (t: typ) : bool =
  match t with
    Var r' when r == r' -> true
  | Var {contents = Link t'} -> occurs r t'
  | Var {contents = Unbound _} -> false
  | App (f, args) -> occurs r f || List.exists (occurs r) args
  | Sgn s -> occurs_sgn r s
  | Sym (_, lazy_sgn) -> occurs_sgn r (Lazy.force lazy_sgn)
  | Ext _ | Rigid _ -> false

and occurs_sgn (r: var_typ ref) (s: sgn_typ) : bool =
  List.exists (fun (x: xtor) -> 
    List.exists (occurs_chiral r) x.arguments || occurs r x.main
  ) s.xtors

and occurs_chiral (r: var_typ ref) (ct: chiral_typ) : bool =
  match ct with Lhs t | Rhs t -> occurs r t

(* ========================================================================= *)
(* Weak head normal form, instantiation, and unification
   
   These are mutually recursive because:
   - whnf calls instantiate to reduce App(Sym, args) -> Sgn
   - instantiate filters unreachable xtors using unify
   - unify calls whnf to normalize before comparing
   
   GADT filtering happens in instantiate: after substituting type parameters,
   we check each xtor's `main` type against the instantiated signature type.
   Xtors that can't unify are filtered out.
*)

(** Reduce a type to weak head normal form.
    - Follows variable links
    - Reduces App(Sym(...), args) to instantiated Sgn (with GADT filtering)
    - Applies the current substitution *)
let rec whnf (subst: (var_typ ref * typ) list) (t: typ) : typ =
  match t with
    Var {contents = Link t'} -> whnf subst t'
  | Var ({contents = Unbound _} as r) ->
      (match find_subst r subst with 
        Some t' -> whnf subst t'
      | None -> t)
  | App (f, args) ->
      (* First reduce the function *)
      let f' = whnf subst f in
      let args' = List.map (whnf subst) args in
      (match f' with
        Sym (_, lazy_sgn) ->
          (* Instantiate: App(Sym, args) -> Sgn with params replaced by args
             and unreachable xtors filtered out *)
          Sgn (instantiate lazy_sgn args')
      | App (f'', args'') ->
          (* Nested application - flatten and try again *)
          whnf subst (App (f'', args'' @ args'))
      | _ -> App (f', args'))
  | Ext _ | Rigid _ | Sym _ | Sgn _ -> t

(** Instantiate a signature with type arguments.
    Substitutes parameters and filters out GADT-unreachable xtors. *)
and instantiate (lazy_sgn: sgn_typ Lazy.t) (args: typ list) : sgn_typ =
  let sgn = Lazy.force lazy_sgn in
  let param_ids = List.map fst sgn.parameters in
  if List.length param_ids <> List.length args then
    failwith "instantiate: arity mismatch"
  else
    let mapping = List.combine param_ids args in
    let substituted = subst_rigid_sgn mapping sgn in
    (* The "self type" after instantiation *)
    let self_typ = Sgn substituted in
    (* Filter xtors: keep only those whose main can unify with self_typ *)
    let reachable_xtors = List.filter (fun (x: xtor) ->
      (* Fresh unification variables for existentials *)
      let fresh_existentials = List.map (fun (id, _kind) ->
        (id, Var (ref (Unbound id)))
      ) x.existentials in
      let main_with_fresh = subst_rigid fresh_existentials x.main in
      (* Try unification with empty env - we just want to know if it's possible *)
      match unify main_with_fresh self_typ empty_env with
      | Some _ -> true
      | None -> false
    ) substituted.xtors in
    { substituted with xtors = reachable_xtors }

(** Unify two lists of types pairwise *)
and unify_args (args1: typ list) (args2: typ list) (env: solving_env) 
    : solving_env option =
  match args1, args2 with
    [], [] -> Some env
  | t1 :: rest1, t2 :: rest2 ->
      Option.bind (unify t1 t2 env) (unify_args rest1 rest2)
  | _ -> None (* Length mismatch *)

(** Unify two types. Reduces both to whnf first, then compares structurally. *)
and unify (t1: typ) (t2: typ) (env: solving_env) : solving_env option =
  let t1 = whnf env.subst t1 in
  let t2 = whnf env.subst t2 in
  match t1, t2 with
  (* Identical externals *)
  | Ext e1, Ext e2 -> if e1 = e2 then Some env else None
  (* Same variable (by physical equality) *)
  | Var r1, Var r2 when r1 == r2 -> Some env
  (* Unbound variable: occurs check, then link *)
  | Var ({contents = Unbound _} as r), t 
  | t, Var ({contents = Unbound _} as r) ->
      if occurs r t then None else (r := Link t; Some env)
  (* Unapplied symbols: same name means same type constructor *)
  | Sym (s1, _), Sym (s2, _) -> 
      if Path.equal s1 s2 then Some env else None
  (* Instantiated signatures: unify structurally *)
  | Sgn sg1, Sgn sg2 -> unify_sgn sg1 sg2 env
  (* Rigid variables *)
  | Rigid a, Rigid b when Ident.equal a b -> Some env
  | Rigid a, t | t, Rigid a ->
      (* Check if local assumptions tell us rigid 'a equals t *)
      if List.exists (fun (t1', t2') -> 
        (t1' = Rigid a && t2' = t) || (t2' = Rigid a && t1' = t)
      ) env.local_eqs
      then Some env else None
  (* Stuck applications: unify head and args separately *)
  | App (f1, a1), App (f2, a2) ->
      Option.bind (unify f1 f2 env) (unify_args a1 a2)
  (* Everything else fails *)
  | _ -> None

(** Unify two signatures structurally.
    Both signatures should already have unreachable xtors filtered out. *)
and unify_sgn (sg1: sgn_typ) (sg2: sgn_typ) (env: solving_env) : solving_env option =
  (* Must have same name *)
  if not (Path.equal sg1.name sg2.name) then None
  (* Must have same xtors (after GADT filtering) *)
  else if List.length sg1.xtors <> List.length sg2.xtors then None
  else
    (* Unify corresponding xtors by name *)
    List.fold_left2 (fun env_opt (x1: xtor) (x2: xtor) ->
      Option.bind env_opt (fun env -> unify_xtor x1 x2 env)
    ) (Some env) sg1.xtors sg2.xtors

(** Unify two xtors structurally *)
and unify_xtor (x1: xtor) (x2: xtor) (env: solving_env) : solving_env option =
  if not (Path.equal x1.name x2.name) then None
  else if List.length x1.arguments <> List.length x2.arguments then None
  else
    (* Unify main types *)
    Option.bind (unify x1.main x2.main env) (fun env ->
      (* Unify arguments pairwise *)
      List.fold_left2 (fun env_opt a1 a2 ->
        Option.bind env_opt (fun env -> unify_chiral a1 a2 env)
      ) (Some env) x1.arguments x2.arguments)

(** Unify chiral types *)
and unify_chiral (ct1: chiral_typ) (ct2: chiral_typ) (env: solving_env) : solving_env option =
  match ct1, ct2 with
  | Lhs t1, Lhs t2 -> unify t1 t2 env
  | Rhs t1, Rhs t2 -> unify t1 t2 env
  | _ -> None  (* Chirality mismatch *)

(** Decompose an equation into a list of type equalities. *)
let rec decompose_eq (eq: equation) : (typ * typ) list =
  match eq with
    Equal (t1, t2) -> [(t1, t2)]
  | And (e1, e2) -> decompose_eq e1 @ decompose_eq e2
  | Implies (assum, body) -> decompose_eq assum @ decompose_eq body
  | Exists (_, e) -> decompose_eq e
  | True -> []

let rec solve (c: equation) (env: solving_env) : solving_env option =
  match c with
    True -> Some env
  | Equal (t1, t2) -> unify t1 t2 env
  | And (c1, c2) -> Option.bind (solve c1 env) (solve c2)
  | Exists (_, c) -> solve c env
  | Implies (assumption, body) ->
      solve body { env with local_eqs = decompose_eq assumption @ env.local_eqs }

(* ========================================================================= *)
(* Commands
   
   Typing judgment: Γ ⊢ cmd  where Γ : var → chiral_typ
   
   Types are ambidextrous: the same signature can be read as data or codata.
   - Data reading: Let (constructor), Switch (pattern match)
   - Codata reading: New (copattern), Invoke (destructor)
   
   Context is non-linear: variables are never consumed, freely duplicated.
   Type instantiation is already reflected in sgn_typ/xtor.
*)

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

let ( let* ) o f =
  match o with
  | Error e -> Error e
  | Ok x -> f x

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
  | Rhs _ -> Error (ChiralityMismatch { expected_chirality = `Lhs; actual = ct })

(** Check that a chiral type is Rhs and extract the type *)
let expect_rhs (ct: chiral_typ) : typ check_result =
  match ct with
    Rhs t -> Ok t
  | Lhs _ -> Error (ChiralityMismatch { expected_chirality = `Rhs; actual = ct })

(** Expect a type to be a signature (possibly after whnf) *)
let expect_sgn (env: solving_env) (t: typ) : sgn_typ check_result =
  match whnf env.subst t with
    Sgn sg -> Ok sg | t' -> Error (ExpectedSignature t')

(** Check that xtor arguments match the context types *)
let check_xtor_args (ctx: context) (env: solving_env) (x: xtor) (args: var list) 
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
          (match unify expected_typ actual_typ env with
            None -> Error (UnificationFailed (expected_typ, actual_typ))
          | Some env' -> 
              (* Also check chirality matches *)
              match xarg, actual_ct with
                Lhs _, Lhs _ | Rhs _, Rhs _ -> check_args env' xrest vrest
              | _ -> Error (TypeMismatch { expected = xarg; actual = actual_ct }))
      | _ -> failwith "impossible: length mismatch after check"
    in
    check_args env x.arguments args

(** Bind xtor arguments in context for a branch *)
let bind_xtor_args (ctx: context) (x: xtor) (vars: var list) : context =
  let bindings = List.combine vars x.arguments in
  extend_many ctx bindings

(** Check a command under a context and solving environment *)
let rec check_command (ctx: context) (env: solving_env) (cmd: command) 
    : unit check_result =
  match cmd with
    Let (v, x, args, body) ->
      (* Check xtor arguments against context *)
      let* env' = check_xtor_args ctx env x args in
      (* v gets type Lhs of the instantiated result type from the xtor *)
      let v_typ = Lhs x.main in
      check_command (extend ctx v v_typ) env' body

  | Switch (sg, v, branches) ->
      (* v must be Lhs of the signature *)
      let* v_ct = lookup ctx v in
      let* v_typ = expect_lhs v_ct in
      (* Get the instantiated signature type (already GADT-filtered) *)
      let* actual_sg = expect_sgn env v_typ in
      (* Unify with declared signature - this verifies same xtors *)
      (match unify_sgn sg actual_sg env with
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
            check_branches_simple ctx env' actual_sg.xtors branches)

  | New (sg, v, branches, body) ->
      (* sg is the instantiated signature - xtors already GADT-filtered *)
      let branch_names = List.map (fun ((x: xtor), _, _) -> x.name) branches in
      let missing_xtors = List.filter (fun (x: xtor) -> 
        not (List.exists (Path.equal x.name) branch_names)
      ) sg.xtors in
      if missing_xtors <> [] then
        Error (NonExhaustive missing_xtors)
      else
        let* () = check_branches_simple ctx env sg.xtors branches in
        let v_typ = Rhs (Sgn sg) in
        check_command (extend ctx v v_typ) env body

  | Invoke (v, x, args) ->
      (* v must be Rhs of a signature containing x *)
      let* v_ct = lookup ctx v in
      let* v_typ = expect_rhs v_ct in
      let* sg = expect_sgn env v_typ in
      if not (List.exists (fun (x': xtor) ->
        Path.equal x'.name x.name) sg.xtors
      ) then
        Error (XtorNotInSignature (x, sg))
      else
        check_xtor_args ctx env x args
        |> Result.map (fun _ -> ())

  | Axiom (ty, v, k) ->
      (* v must be Lhs ty, k must be Rhs ty *)
      let* v_ct = lookup ctx v in
      let* k_ct = lookup ctx k in
      let* v_typ = expect_lhs v_ct in
      let* k_typ = expect_rhs k_ct in
      (match unify v_typ ty env, unify k_typ ty env with
        None, _ -> Error (UnificationFailed (v_typ, ty))
      | _, None -> Error (UnificationFailed (k_typ, ty))
      | Some _, Some _ -> Ok ())

  | Lit (_, v, body) ->
      let v_typ = Lhs (Ext Int) in
      check_command (extend ctx v v_typ) env body

  | Add (x, y, v, body) ->
      let* x_ct = lookup ctx x in
      let* y_ct = lookup ctx y in
      let int_lhs = Lhs (Ext Int) in
      (match unify (unchiral x_ct) (Ext Int) env, 
             unify (unchiral y_ct) (Ext Int) env
      with
        None, _ -> Error (TypeMismatch { expected = int_lhs; actual = x_ct })
      | _, None -> Error (TypeMismatch { expected = int_lhs; actual = y_ct })
      | Some _, Some _ ->
          check_command (extend ctx v int_lhs) env body)

  | Ifz (v, then_cmd, else_cmd) ->
      let* v_ct = lookup ctx v in
      (match unify (unchiral v_ct) (Ext Int) env with
        None -> Error (TypeMismatch { expected = Lhs (Ext Int); actual = v_ct })
      | Some _ ->
          let* () = check_command ctx env then_cmd in
          check_command ctx env else_cmd)

  | Ret (ty, v) ->
      let* v_ct = lookup ctx v in
      let* v_typ = expect_lhs v_ct in
      (match unify v_typ ty env with
        None -> Error (UnificationFailed (v_typ, ty))
      | Some _ -> Ok ())

  | End -> Ok ()

(** Check branches against xtors (simple version - same env for all branches) *)
and check_branches_simple (ctx: context) (env: solving_env) (xtors: xtor list)
    (branches: branch list) : unit check_result =
  let check_one (x: xtor) =
    match List.find_opt (fun ((x': xtor), _, _) -> Path.equal x'.name x.name) branches with
      None -> Error (NonExhaustive [x])  (* Should not happen if exhaustiveness passed *)
    | Some (_, vars, cmd) ->
        if List.length vars <> List.length x.arguments then
          Error (ArityMismatch { xtor = x; expected = List.length x.arguments; actual = List.length vars })
        else
          let ctx' = bind_xtor_args ctx x vars in
          check_command ctx' env cmd
  in
  let results = List.map check_one xtors in
  match List.find_opt Result.is_error results with
    Some (Error e) -> Error e
  | _ -> Ok ()