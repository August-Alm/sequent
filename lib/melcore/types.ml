(**
  module: Melcore.Types
  description: Type system of the Melcore language.
*)

open Common.Identifiers

let ( let* ) o f = Utility.( let* ) o f

type sym = Path.t

type kind = Star | Arrow of kind * kind

type ext_typ =
    Int

type polarity = Pos | Neg
  
type typ =
    Ext of ext_typ (* Built-in, externally implemented types *)
  | Var of var_typ ref (* Type variable *)
  | Rigid of Ident.t (* Rigid/skolem variable *)
  | Sym of sym * polarity * sgn_typ Lazy.t (* Reference to a signature *)
  | App of typ * (typ list) (* Instantiation *)
  | Fun of typ * typ (* Function type *)
  | All of (Ident.t * kind) * typ (* Universally quantified type *)
  | Data of sgn_typ (* An instantiated data type *)
  | Code of sgn_typ (* An instantiated codata type *)

and var_typ =
    Unbound of Ident.t
  | Link of typ

(* Signatures are not polarised as data or codata, but can
 function as both, depending on context *)
and sgn_typ =
  { name: sym
  ; parameters: kind list  (* Just kinds, no names - GADT style *)
  ; xtors: xtor list
  }

(* Unifying, unpolarized notion constructors and destructors *)
and xtor =
  { name: sym
  ; parameters: (Ident.t * kind) list 
  ; existentials: (Ident.t * kind) list
  (* For a codata type, the last argument is the codomain! *)
  ; arguments: typ list
  (* `main` is result type if considered as constructor, the "this"
    type if considered as destructor *)
  ; main: typ
  }

and equation =
    Equal of typ * typ
  | And of equation * equation
  | Exists of var_typ * equation 
  | Implies of equation * equation
  | True

type kind_error =
    UnboundVariable of Ident.t
  | ExpectedHKT of typ * kind
  | KindMismatch of {expected: kind; actual: kind}
  | ExistentialEscape of {xtor: Path.t; existential: Ident.t}

type kind_check_result = (kind, kind_error) result

(** Check if an identifier is in a list, using Ident.equal *)
let contains_var (id: Ident.t) (ids: Ident.t list) : bool =
  List.exists (Ident.equal id) ids

(** Check if a rigid variable appears free in a type *)
let rec rigid_occurs (id: Ident.t) (t: typ) : bool =
  match t with
    Rigid id' -> Ident.equal id id'
  | Var {contents = Link t'} -> rigid_occurs id t'
  | Var {contents = Unbound _} -> false
  | App (f, args) ->
      rigid_occurs id f || List.exists (rigid_occurs id) args
  | Data sgn | Code sgn -> rigid_occurs_sgn id sgn
  | Sym _ | Ext _ | Fun _ | All _ -> false

and rigid_occurs_sgn (id: Ident.t) (s: sgn_typ) : bool =
  (* sgn.parameters are just kinds, no binders to shadow *)
  List.exists (rigid_occurs_xtor id) s.xtors

and rigid_occurs_xtor (id: Ident.t) (x: xtor) : bool =
  (* Don't check under binders that shadow the id *)
  let bound = List.map fst x.parameters @ List.map fst x.existentials in
  if contains_var id bound then false
  else
    List.exists (rigid_occurs id) x.arguments 
    || rigid_occurs id x.main

(** Bidirectional kind checking.
    infer_kind computes the kind of a type given a kind context.
    check_kind verifies a type has the expected kind.
    The context maps identifiers (both Rigid and Var binders) to their kinds. *)
let rec infer_kind (ctx: kind Ident.tbl) (t: typ) : kind_check_result =
  match t with
    Ext _ -> Ok Star
  | Var {contents = Unbound id} ->
      (match Ident.find_opt id ctx with
        Some k -> Ok k
      | None -> Error (UnboundVariable id))
  | Var {contents = Link t'} -> infer_kind ctx t'
  | Rigid id ->
      (match Ident.find_opt id ctx with
        Some k -> Ok k
      | None -> Error (UnboundVariable id))
  | Sym (_, _, lazy_sgn) ->
      (* The kind of a symbol is determined by its parameters *)
      let sgn = Lazy.force lazy_sgn in
      Ok (List.fold_right (fun k acc ->
        Arrow (k, acc)
      ) sgn.parameters Star)
  | App (f, args) ->
      let* f_kind = infer_kind ctx f in
      (* Apply each argument, consuming one arrow at a time *)
      let rec apply_args (fk: kind) (args: typ list) =
        match fk, args with
          k, [] -> Ok k
        | Arrow (param_kind, result_kind), arg :: rest ->
            let* arg_kind = infer_kind ctx arg in
            if arg_kind = param_kind then
              apply_args result_kind rest
            else
              Error (KindMismatch {expected = param_kind; actual = arg_kind})
        | k, _ :: _ -> Error (ExpectedHKT (f, k))
      in
      apply_args f_kind args
  | Fun (a, b) ->
      let* _ = check_kind ctx a Star in
      let* _ = check_kind ctx b Star in
      Ok Star
  | All ((x, k), body) ->
      let ctx' = Ident.add x k ctx in
      let* _ = check_kind ctx' body Star in
      Ok Star
  | Data sgn | Code sgn -> 
      (* Kind check the signature for well-formedness:
        1. Check that existentials don't escape into main
        2. Compute kind from parameters *)
      let check_xtor (x: xtor) : (unit, kind_error) result =
        let escaped = List.filter (fun (id, _) ->
          rigid_occurs id x.main
        ) x.existentials in
        match escaped with
        | [] -> Ok ()
        | (id, _) :: _ ->
          Error (ExistentialEscape {xtor = x.name; existential = id})
      in
      let rec check_all = function
        | [] -> 
            (* All xtors valid; compute kind from parameters *)
            Ok (List.fold_right (fun k acc ->
              Arrow (k, acc)
            ) sgn.parameters Star)
        | x :: rest -> 
            match check_xtor x with
            | Ok () -> check_all rest
            | Error e -> Error e
      in
      check_all sgn.xtors

(** Check that a type has the expected kind *)
and check_kind (ctx: kind Ident.tbl) (t: typ) (expected: kind)
    : (unit, kind_error) result =
  let* actual = infer_kind ctx t in
  if actual = expected then Ok ()
  else Error (KindMismatch {expected; actual})

(** Substitute rigid type variables with types in a type.
    Used for instantiating signature parameters. *)
let rec subst_rigid (ms: (Ident.t * typ) list) (t: typ) : typ =
  match t with
  | Rigid id ->
      (match List.find_opt (fun (id', _) -> Ident.equal id id') ms with
        Some (_, t') -> t' | None -> t)
  | Var ({contents = Link t'}) -> subst_rigid ms t'
  | Var _ -> t
  | App (f, args) -> App (subst_rigid ms f, List.map (subst_rigid ms) args)
  | Data sgn -> Data (subst_rigid_sgn ms sgn)
  | Code sgn -> Code (subst_rigid_sgn ms sgn)
  | Ext _ | Sym (_, _, _) | Fun (_, _) | All (_, _) -> t

and subst_rigid_sgn (ms: (Ident.t * typ) list) (s: sgn_typ) : sgn_typ =
  (* Substitute into xtors. No shadowing check needed here - the signature's
    parameters are exactly what we want to substitute. Shadowing is handled
    in subst_rigid_xtor for xtor-local bindings. *)
  {s with xtors = List.map (subst_rigid_xtor ms) s.xtors}

and subst_rigid_xtor (ms: (Ident.t * typ) list) (x: xtor) : xtor =
  (* Don't substitute identifiers rebound by xtor's own params or existentials *)
  let shadowed = List.map fst x.parameters @ List.map fst x.existentials in
  let ms' = List.filter (fun (id, _) -> not (contains_var id shadowed)) ms in
  { x with
    arguments = List.map (subst_rigid ms') x.arguments
  ; main = subst_rigid ms' x.main
  }

(** Substitute Var {contents = Unbound id} by identifier name.
    Used for builtin templates that use Var refs as placeholders. *)
let rec subst_unbound (ms: (Ident.t * typ) list) (t: typ) : typ =
  match t with
  | Var ({contents = Unbound id}) ->
      (match List.find_opt (fun (id', _) -> Ident.equal id id') ms with
        Some (_, t') -> t' | None -> t)
  | Var ({contents = Link t'}) -> subst_unbound ms t'
  | Rigid _ -> t
  | App (f, args) -> App (subst_unbound ms f, List.map (subst_unbound ms) args)
  | Data sgn -> Data (subst_unbound_sgn ms sgn)
  | Code sgn -> Code (subst_unbound_sgn ms sgn)
  | Ext _ | Sym (_, _, _) | Fun (_, _) | All (_, _) -> t

and subst_unbound_sgn (ms: (Ident.t * typ) list) (s: sgn_typ) : sgn_typ =
  {s with xtors = List.map (subst_unbound_xtor ms) s.xtors}

and subst_unbound_xtor (ms: (Ident.t * typ) list) (x: xtor) : xtor =
  let shadowed = List.map fst x.parameters @ List.map fst x.existentials in
  let ms' = List.filter (fun (id, _) -> not (contains_var id shadowed)) ms in
  { x with
    arguments = List.map (subst_unbound ms') x.arguments
  ; main = subst_unbound ms' x.main
  }

type solving_env =
  { subs: (var_typ ref * typ) list (* Current substitution - keyed by ref *)
  ; local_eqs: (typ * typ) list (* Local assumptions (from GADT matches) *)
  }

let empty_env: solving_env = {subs = []; local_eqs = []}

(** Find a var ref in the substitution using physical equality *)
let rec find_subst (r: var_typ ref) (subs: (var_typ ref * typ) list) =
  match subs with
    [] -> None
  | (r', t) :: _ when r == r' -> Some t
  | _ :: rest -> find_subst r rest

(* Set of signature paths for tracking visited signatures in occurs check *)
module PathSet = Set.Make(struct type t = Path.t let compare = Path.compare end)

(** Occurs check: does variable r occur in type t?
    Uses a visited set to prevent infinite recursion on recursive types. *)
let rec occurs_aux (visited: PathSet.t) (r: var_typ ref) (t: typ) : bool =
  match t with
    Var r' when r == r' -> true
  | Var {contents = Link t'} -> occurs_aux visited r t'
  | Var {contents = Unbound _} -> false
  | App (f, args) -> occurs_aux visited r f || List.exists (occurs_aux visited r) args
  | Data sgn | Code sgn ->
      if PathSet.mem sgn.name visited then false
      else occurs_sgn_aux (PathSet.add sgn.name visited) r sgn
  | Sym (name, _, lazy_sgn) ->
      if PathSet.mem name visited then false
      else occurs_sgn_aux (PathSet.add name visited) r (Lazy.force lazy_sgn)
  | Ext _ | Rigid _ | Fun _ | All _ -> false

and occurs_sgn_aux (visited: PathSet.t) (r: var_typ ref) (s: sgn_typ) : bool =
  List.exists (fun (x: xtor) -> 
    List.exists (occurs_aux visited r) x.arguments || occurs_aux visited r x.main
  ) s.xtors

let occurs (r: var_typ ref) (t: typ) : bool = occurs_aux PathSet.empty r t

(* ========================================================================= *)
(* Weak head normal form, instantiation, and unification                     *)
(* ========================================================================= *)
(*
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
    - Applies the current substitution
    kctx is the kind context for kind checking during instantiation. *)
let rec whnf (kctx: kind Ident.tbl) (subs: (var_typ ref * typ) list) (t: typ) =
  match t with
    Var {contents = Link t'} -> whnf kctx subs t'
  | Var ({contents = Unbound _} as r) ->
      (match find_subst r subs with 
        Some t' -> whnf kctx subs t'
      | None -> t)
  | App (f, args) ->
      (* First reduce the function *)
      let f' = whnf kctx subs f in
      let args' = List.map (whnf kctx subs) args in
      (match f' with
        Sym (_, pol, lazy_sgn) ->
          (* Instantiate: App(Sym, args) -> Sgn with params replaced by args
             and unreachable xtors filtered out *)
          (match pol with
            Pos -> Data (instantiate kctx lazy_sgn args')
          | Neg -> Code (instantiate kctx lazy_sgn args'))
      | App (f'', args'') ->
          (* Nested application - flatten and try again *)
          whnf kctx subs (App (f'', args'' @ args'))
      | _ -> App (f', args'))
  | Sym (_, pol, lazy_sgn) ->
      (* Nullary type symbol: instantiate with no arguments.
         This handles bare Sym without App wrapper. *)
      let sgn = Lazy.force lazy_sgn in
      if sgn.parameters = [] then
        (* Nullary: instantiate directly *)
        (match pol with
          Pos -> Data (instantiate kctx lazy_sgn [])
        | Neg -> Code (instantiate kctx lazy_sgn []))
      else
        (* Has parameters: leave as Sym, will be applied later *)
        t
  | Ext _ | Rigid _ | Data _ | Code _ | Fun _ | All _ -> t

(** Instantiate a signature with type arguments.
    Substitutes parameters, checks kinds, and filters out GADT-unreachable xtors. *)
and instantiate
    (kctx: kind Ident.tbl) (lazy_sgn: sgn_typ Lazy.t) (args: typ list)
    : sgn_typ =
  let sgn = Lazy.force lazy_sgn in
  let param_kinds = sgn.parameters in
  if List.length param_kinds <> List.length args then
    failwith "instantiate: arity mismatch"
  else begin
    (* Kind check: verify each arg has the expected kind *)
    List.iter2 (fun expected_kind arg ->
      match check_kind kctx arg expected_kind with
        Ok () -> ()
      | Error _ -> failwith "instantiate: kind mismatch"
    ) param_kinds args;
    (* For each xtor:
      1. Create fresh unification variables for its universal parameters
      2. Unify main with target type to derive substitution
      3. Apply substitution to arguments
      4. Filter out xtors that can't unify (GADT refinement)
      
      Note: xtor.parameters are universals (exposed by pattern matching) -> substituted with caller's args
            xtor.existentials are existentials (hidden) -> stay as Rigid *)
    let instantiate_xtor (x: xtor) : xtor option =
      (* Derive substitution by matching xtor.main against target type.
         For non-GADT types: xtor.main = App(Sym(parent), [vars...])
         We match positionally with caller's args to get substitution.
         This ensures substituted types contain caller's args (already kind-checked). *)
      match x.main with
      | App (Sym (p, _, _), main_args) when Path.equal p sgn.name ->
          if List.length main_args <> List.length args then
            None  (* Arity mismatch - xtor not reachable *)
          else begin
            (* Check if all args can unify (GADT filtering) *)
            let can_match = List.for_all2 can_unify_shallow_types main_args args in
            if not can_match then
              None  (* GADT refinement: xtor not reachable at this type *)
            else begin
              (* Build substitution: xtor's param vars -> caller's args *)
              let subst = List.fold_left2 (fun acc main_arg caller_arg ->
                match main_arg with
                | Var {contents = Unbound id} -> (id, caller_arg) :: acc
                | Var {contents = Link _} -> acc  (* Already linked *)
                | _ -> acc  (* Complex pattern - handled by can_unify check *)
              ) [] main_args args in
              let args_subst = List.map (subst_unbound subst) x.arguments in
              Some { x with 
                parameters = []  (* Universals cleared after instantiation *)
              ; arguments = args_subst
              ; main = x.main  (* Keep original - avoids infinite expansion *)
              }
            end
          end
      | Sym (p, _, _) when Path.equal p sgn.name ->
          (* Nullary main type - xtor produces/consumes bare parent type *)
          if args = [] then Some { x with parameters = [] }
          else None  (* Caller passed args but xtor expects none *)
      | Var {contents = Unbound id} ->
          (* main is just a var - matches any target (degenerate GADT case) *)
          let target = App (Sym (sgn.name, Pos, lazy sgn), args) in
          let subst = [(id, target)] in
          let args_subst = List.map (subst_unbound subst) x.arguments in
          Some { x with parameters = []; arguments = args_subst }
      | _ -> None  (* Doesn't match target type *)
    in
    let reachable_xtors = List.filter_map instantiate_xtor sgn.xtors in
    {sgn with parameters = []; xtors = reachable_xtors}
  end

(** Shallow unification check for GADT filtering.
    Checks if type `t` can unify with `App(Sym(target_name, _), target_args)`.
    Returns true if t can potentially equal the target type, without recursing 
    deeply into signature structure. This avoids infinite recursion when 
    signatures contain recursive references. *)
and can_unify_shallow
    (t: typ) (target_args: typ list) (target_name: Path.t) : bool =
  match t with
    Var {contents = Link t'} -> can_unify_shallow t' target_args target_name
  | Var {contents = Unbound _} -> true  (* Unbound can unify with anything *)
  | Data sgn | Code sgn -> 
      Path.equal sgn.name target_name && 
      sgn.parameters = []  (* Sgn with no params = already instantiated *)
  | Sym (p, _, _) ->
      (* Bare Sym (nullary type): matches if path equals and no target args *)
      Path.equal p target_name && target_args = []
  | App (Sym (p, _, _), args) ->
      Path.equal p target_name && 
      List.length args = List.length target_args &&
      List.for_all2 can_unify_shallow_types args target_args
  | App (f, args) ->
      (* Nested App - try to extract the head *)
      (match f with
        Sym (p, _, _) -> 
          Path.equal p target_name && 
          List.length args = List.length target_args &&
          List.for_all2 can_unify_shallow_types args target_args
      | _ -> false)
  | _ -> false

(** Check if two types can potentially unify (shallow) *)
and can_unify_shallow_types (t1: typ) (t2: typ) : bool =
  match t1, t2 with
    Var {contents = Link t1'}, _ -> can_unify_shallow_types t1' t2
  | _, Var {contents = Link t2'} -> can_unify_shallow_types t1 t2'
  | Var {contents = Unbound _}, _ -> true
  | _, Var {contents = Unbound _} -> true
  | Ext e1, Ext e2 -> e1 = e2
  | Rigid a, Rigid b -> Ident.equal a b
  | Sym (p1, _, _), Sym (p2, _, _) -> Path.equal p1 p2
  | Data sg1, Data sg2 -> Path.equal sg1.name sg2.name
  | Code sg1, Code sg2 -> Path.equal sg1.name sg2.name
  (* App can unify with Data/Code if the App's head is an unbound var or 
     the App would reduce to the same signature *)
  | App (Var {contents = Unbound _}, _), (Data _ | Code _) -> true
  | (Data _ | Code _), App (Var {contents = Unbound _}, _) -> true
  | App (Sym (p1, _, _), _), Data sg2 -> Path.equal p1 sg2.name
  | App (Sym (p1, _, _), _), Code sg2 -> Path.equal p1 sg2.name
  | Data sg1, App (Sym (p2, _, _), _) -> Path.equal sg1.name p2
  | Code sg1, App (Sym (p2, _, _), _) -> Path.equal sg1.name p2
  | App (f1, a1), App (f2, a2) ->
      can_unify_shallow_types f1 f2 && 
      List.length a1 = List.length a2 &&
      List.for_all2 can_unify_shallow_types a1 a2
  | _ -> false

(** Unify two lists of types pairwise *)
and unify_args
    (kctx: kind Ident.tbl) (args1: typ list) (args2: typ list) (env: solving_env) 
    : solving_env option =
  match args1, args2 with
    [], [] -> Some env
  | t1 :: rest1, t2 :: rest2 ->
      Option.bind (unify kctx t1 t2 env) (unify_args kctx rest1 rest2)
  | _ -> None (* Length mismatch *)

(** Unify two types. Reduces both to whnf first, then compares structurally. *)
and unify (kctx: kind Ident.tbl) (t1: typ) (t2: typ) (env: solving_env)
    : solving_env option =
  let t1 = whnf kctx env.subs t1 in
  let t2 = whnf kctx env.subs t2 in
  match t1, t2 with
  (* Identical externals *)
    Ext e1, Ext e2 -> if e1 = e2 then Some env else None
  (* Same variable (by physical equality) *)
  | Var r1, Var r2 when r1 == r2 -> Some env
  (* Unbound variable: occurs check, then link *)
  | Var ({contents = Unbound _} as r), t 
  | t, Var ({contents = Unbound _} as r) ->
      if occurs r t then None else (r := Link t; Some env)
  (* Unapplied symbols: same name means same type constructor *)
  | Sym (s1, _, _), Sym (s2, _, _) -> 
      if Path.equal s1 s2 then Some env else None
  (* Function types: unify domain and codomain *)
  | Fun (a1, b1), Fun (a2, b2) ->
      Option.bind (unify kctx a1 a2 env) (unify kctx b1 b2)
  (* Instantiated signatures: check name equality to avoid infinite recursion *)
  | Data sg1, Data sg2 -> 
      (* If same name and both have no parameters (already instantiated), they're equal *)
      if Path.equal sg1.name sg2.name && sg1.parameters = [] && sg2.parameters = []
      then Some env
      else unify_sgn kctx sg1 sg2 env
  | Code sg1, Code sg2 -> 
      if Path.equal sg1.name sg2.name && sg1.parameters = [] && sg2.parameters = []
      then Some env
      else unify_sgn kctx sg1 sg2 env
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
      Option.bind (unify kctx f1 f2 env) (unify_args kctx a1 a2)
  (* Universally quantified types: unify bodies *)
  | All ((x1, k1), body1), All ((x2, k2), body2) when k1 = k2 ->
      (* Alpha-rename x2 to x1 in body2 for comparison *)
      let body2' = subst_rigid [(x2, Rigid x1)] body2 in
      let kctx' = Ident.add x1 k1 kctx in
      unify kctx' body1 body2' env
  (* Everything else fails *)
  | _ -> None

(** Unify two signatures structurally.
    Both signatures should already have unreachable xtors filtered out. *)
and unify_sgn
    (kctx: kind Ident.tbl) (sg1: sgn_typ) (sg2: sgn_typ) (env: solving_env)
    : solving_env option =
  (* Must have same name *)
  if not (Path.equal sg1.name sg2.name) then None
  (* Must have same xtors (after GADT filtering) *)
  else if List.length sg1.xtors <> List.length sg2.xtors then None
  else
    (* Unify corresponding xtors by name *)
    List.fold_left2 (fun env_opt (x1: xtor) (x2: xtor) ->
      Option.bind env_opt (fun env -> unify_xtor kctx x1 x2 env)
    ) (Some env) sg1.xtors sg2.xtors

(** Unify two xtors structurally *)
and unify_xtor
    (kctx: kind Ident.tbl) (x1: xtor) (x2: xtor) (env: solving_env)
    : solving_env option =
  if not (Path.equal x1.name x2.name) then None
  else if List.length x1.arguments <> List.length x2.arguments then None
  else
    (* Don't unify main types - if xtors have same name from same signature,
       their main types are definitionally equal. Unifying them would cause
       infinite recursion since main contains the signature that contains xtors. *)
    (* Just unify arguments pairwise *)
    List.fold_left2 (fun env_opt a1 a2 ->
      Option.bind env_opt (unify kctx a1 a2)
    ) (Some env) x1.arguments x2.arguments

(* ========================================================================= *)
(* Equation solving *)
(* ========================================================================= *)

let rec solve
    (kctx: kind Ident.tbl) (c: equation) (env: solving_env)
    : solving_env option =
  match c with
    True -> Some env
  | Equal (t1, t2) -> unify kctx t1 t2 env
  | And (c1, c2) -> Option.bind (solve kctx c1 env) (solve kctx c2)
  | Exists (_, c) -> solve kctx c env
  | Implies (assumption, body) ->
      (* Verify assumption is solvable, then add to local equations for body *)
      let rec collect_eqs (eq: equation) : (typ * typ) list =
        match eq with
          Equal (t1, t2) -> [(t1, t2)]
        | And (e1, e2) -> collect_eqs e1 @ collect_eqs e2
        | Implies (_, e) -> collect_eqs e
        | Exists (_, e) -> collect_eqs e
        | True -> []
      in
      match solve kctx assumption env with
        None -> None
      | Some env' ->
          solve kctx body { env' with
            local_eqs = collect_eqs assumption @ env'.local_eqs
          }
