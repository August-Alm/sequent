(**
  module: Common.Types
  description: A type system common to sequent calculus-based intermediate languages.
*)

open Identifiers

let ( let* ) o f = Utility.( let* ) o f

type sym = Path.t

type kind = Star | Arrow of kind * kind

(* Newton's method for integer square root *)
let isqrt n =
  if n < 0 then invalid_arg "isqrt"
  else if n = 0 then 0
  else
    let rec go x =
      let x' = (x + n / x) / 2 in
      if x' >= x then x else go x'
    in
    go n

(* Cantor's diagonal *)
let cantor_pair x y = (x + y) * (x + y + 1) / 2 + y

let cantor_unpair p =
  let w = (isqrt (8 * p + 1) - 1) / 2 in
  let t = (w * w + w) / 2 in
  let y = p - t in
  let x = w - y in
  (x, y)

let rec encode =
  function
    Star -> 0
  | Arrow (k1, k2) -> cantor_pair (encode k1) (encode k2) + 3

let rec decode n =
  if n = 0 then Star
  else
    let (x, y) = cantor_unpair (n - 3) in
    Arrow (decode x, decode y)

let compare_kinds k1 k2 =
  let n1 = encode k1 in
  let n2 = encode k2 in
  compare n1 n2

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
  ; parameters: kind list  (* Just kinds, no names - GADT style *)
  ; xtors: xtor list
  }

(* Unifying, unpolarized notion constructors and destructors *)
and xtor =
  { name: sym
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
    Equal of typ * typ
  | And of equation * equation
  | Exists of var_typ * equation 
  | Implies of equation * equation
  | True

let chiral_map (f: typ -> typ) (ct: chiral_typ) : chiral_typ =
  match ct with
    Lhs t -> Lhs (f t)
  | Rhs t -> Rhs (f t)

type kind_error =
    UnboundVariable of Ident.t
  | ExpectedHKT of typ * kind
  | KindMismatch of { expected: kind; actual: kind }
  | ExistentialEscape of { xtor: Path.t; existential: Ident.t }

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
  | Sgn s -> rigid_occurs_sgn id s
  | Sym _ | Ext _ -> false

and rigid_occurs_sgn (id: Ident.t) (s: sgn_typ) : bool =
  (* sgn.parameters are just kinds, no binders to shadow *)
  List.exists (rigid_occurs_xtor id) s.xtors

and rigid_occurs_xtor (id: Ident.t) (x: xtor) : bool =
  (* Don't check under binders that shadow the id *)
  let bound = List.map fst x.parameters @ List.map fst x.existentials in
  if contains_var id bound then false
  else
    List.exists (fun ct ->
      match ct with Lhs t | Rhs t -> rigid_occurs id t
    ) x.arguments 
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
  | Sym (_, lazy_sgn) ->
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
              Error (KindMismatch { expected = param_kind; actual = arg_kind })
        | k, _ :: _ -> Error (ExpectedHKT (f, k))
      in
      apply_args f_kind args
  | Sgn s -> 
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
          Error (ExistentialEscape { xtor = x.name; existential = id })
      in
      let rec check_all = function
        | [] -> 
            (* All xtors valid; compute kind from parameters *)
            Ok (List.fold_right (fun k acc ->
              Arrow (k, acc)
            ) s.parameters Star)
        | x :: rest -> 
            match check_xtor x with
            | Ok () -> check_all rest
            | Error e -> Error e
      in
      check_all s.xtors

(** Check that a type has the expected kind *)
and check_kind (ctx: kind Ident.tbl) (t: typ) (expected: kind)
    : (unit, kind_error) result =
  let* actual = infer_kind ctx t in
  if actual = expected then Ok ()
  else Error (KindMismatch { expected; actual })

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
  | Sgn s -> Sgn (subst_rigid_sgn ms s)
  | Ext _ | Sym (_, _) -> t

and subst_rigid_sgn (ms: (Ident.t * typ) list) (s: sgn_typ) : sgn_typ =
  (* Substitute into xtors. No shadowing check needed here - the signature's
    parameters are exactly what we want to substitute. Shadowing is handled
    in subst_rigid_xtor for xtor-local bindings. *)
  { s with xtors = List.map (subst_rigid_xtor ms) s.xtors }

and subst_rigid_xtor (ms: (Ident.t * typ) list) (x: xtor) : xtor =
  (* Don't substitute identifiers bound by existentials (they are local to xtor).
     xtor.parameters are copies of signature parameters and SHOULD be substituted. *)
  let shadowed = List.map fst x.existentials in
  let ms' = List.filter (fun (id, _) -> not (contains_var id shadowed)) ms in
  { x with
    arguments = List.map (chiral_map (subst_rigid ms')) x.arguments
  ; main = subst_rigid ms' x.main
  ; parameters = []  (* Clear parameters after instantiation *)
  }

(** Substitute unbound unification variables by identifier name.
    Used for instantiating xtor template parameters (which use Var not Rigid). *)
let rec subst_unbound (ms: (Ident.t * typ) list) (t: typ) : typ =
  match t with
  | Var ({contents = Unbound id}) ->
      (match List.find_opt (fun (id', _) -> Ident.equal id id') ms with
        Some (_, t') -> t' | None -> t)
  | Var ({contents = Link t'}) -> subst_unbound ms t'
  | Rigid _ -> t
  | App (f, args) -> App (subst_unbound ms f, List.map (subst_unbound ms) args)
  | Sgn s -> Sgn (subst_unbound_sgn ms s)
  | Ext _ | Sym (_, _) -> t

and subst_unbound_sgn (ms: (Ident.t * typ) list) (s: sgn_typ) : sgn_typ =
  { s with xtors = List.map (subst_unbound_xtor ms) s.xtors }

and subst_unbound_xtor (ms: (Ident.t * typ) list) (x: xtor) : xtor =
  (* Don't substitute identifiers bound by existentials (they are local). *)
  let shadowed = List.map fst x.existentials in
  let ms' = List.filter (fun (id, _) -> not (contains_var id shadowed)) ms in
  { x with
    arguments = List.map (chiral_map (subst_unbound ms')) x.arguments
  ; main = subst_unbound ms' x.main
  ; parameters = []
  }

type solving_env =
  { subs: (var_typ ref * typ) list (* Current substitution - keyed by ref *)
  ; local_eqs: (typ * typ) list (* Local assumptions (from GADT matches) *)
  }

let empty_env : solving_env = { subs = []; local_eqs = [] }

(** Find a var ref in the substitution using physical equality *)
let rec find_subst (r: var_typ ref) (subs: (var_typ ref * typ) list) =
  match subs with
    [] -> None
  | (r', t) :: _ when r == r' -> Some t
  | _ :: rest -> find_subst r rest

(** Occurs check: does variable r occur in type t?
    Uses a visited set to handle recursive type definitions. *)
module PathSet = Set.Make(struct type t = Path.t let compare = Path.compare end)

let rec occurs_aux (visited: PathSet.t) (r: var_typ ref) (t: typ) : bool =
  match t with
    Var r' when r == r' -> true
  | Var {contents = Link t'} -> occurs_aux visited r t'
  | Var {contents = Unbound _} -> false
  | App (f, args) -> 
      occurs_aux visited r f || List.exists (occurs_aux visited r) args
  | Sgn s ->
      (* If we've already visited this signature, don't recurse into it *)
      if PathSet.mem s.name visited then false
      else occurs_sgn_aux (PathSet.add s.name visited) r s
  | Sym (name, lazy_sgn) ->
      (* If we've already visited this signature, don't recurse into it *)
      if PathSet.mem name visited then false
      else occurs_sgn_aux (PathSet.add name visited) r (Lazy.force lazy_sgn)
  | Ext _ | Rigid _ -> false

and occurs_sgn_aux (visited: PathSet.t) (r: var_typ ref) (s: sgn_typ) : bool =
  List.exists (fun (x: xtor) -> 
    List.exists (fun ct ->
      match ct with Lhs t | Rhs t -> occurs_aux visited r t
    ) x.arguments || occurs_aux visited r x.main
  ) s.xtors

let occurs r t = occurs_aux PathSet.empty r t

(* ========================================================================= *)
(* Weak head normal form, instantiation, and unification
(* ========================================================================= *)
   
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
        Sym (_, lazy_sgn) ->
          (* Instantiate: App(Sym, args) -> Sgn with params replaced by args
             and unreachable xtors filtered out *)
          Sgn (instantiate kctx lazy_sgn args')
      | App (f'', args'') ->
          (* Nested application - flatten and try again *)
          whnf kctx subs (App (f'', args'' @ args'))
      | _ -> App (f', args'))
  | Ext _ | Rigid _ | Sym _ | Sgn _ -> t

(** Instantiate a signature with type arguments.
    Substitutes parameters, checks kinds, and filters out GADT-unreachable xtors. *)
and instantiate (kctx: kind Ident.tbl) (lazy_sgn: sgn_typ Lazy.t) (args: typ list) : sgn_typ =
  let sgn = Lazy.force lazy_sgn in
  let param_kinds = sgn.parameters in
  if List.length param_kinds <> List.length args then
    failwith (Printf.sprintf "instantiate: arity mismatch (params=%d, args=%d)" 
      (List.length param_kinds) (List.length args))
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
       
       Note: xtor.parameters are universals (exposed by pattern matching) -> fresh Var refs
             xtor.existentials are existentials (hidden) -> stay as Rigid *)
    let target_typ = App (Sym (sgn.name, lazy_sgn), args) in
    let instantiate_xtor (x: xtor) : xtor option =
      (* Fresh unification variables for xtor's universal parameters only *)
      let fresh_vars = List.map (fun (id, _) -> ref (Unbound id)) x.parameters in
      let fresh_mapping = List.map2 (fun (id, _) r -> (id, Var r)) x.parameters fresh_vars in
      (* Substitute Unbound params with fresh Vars; existentials stay as Rigid *)
      let main_with_fresh = subst_unbound fresh_mapping x.main in
      (* Try to unify with target *)
      if can_unify_shallow main_with_fresh args sgn.name then begin
        (* Apply substitution to arguments *)
        let args_subst = List.map (chiral_map (subst_unbound fresh_mapping)) x.arguments in
        Some { x with 
          parameters = []  (* Universals cleared after instantiation *)
        (* existentials stay - they become Rigid skolems during pattern match *)
        ; arguments = args_subst
        ; main = target_typ
        }
      end else
        None
    in
    let reachable_xtors = List.filter_map instantiate_xtor sgn.xtors in
    { sgn with parameters = []; xtors = reachable_xtors }
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
  | Sgn sg -> 
      Path.equal sg.name target_name && 
      sg.parameters = []  (* Sgn with no params = already instantiated *)
  | App (Sym (p, _), args) ->
      Path.equal p target_name && 
      List.length args = List.length target_args &&
      List.for_all2 can_unify_shallow_types args target_args
  | App (f, args) ->
      (* Nested App - try to extract the head *)
      (match f with
        Sym (p, _) -> 
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
  | Sym (p1, _), Sym (p2, _) -> Path.equal p1 p2
  | Sgn sg1, Sgn sg2 -> Path.equal sg1.name sg2.name
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
  | Sym (s1, _), Sym (s2, _) -> 
      if Path.equal s1 s2 then Some env else None
  (* Instantiated signatures: unify structurally *)
  | Sgn sg1, Sgn sg2 -> unify_sgn kctx sg1 sg2 env
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
    (* Skip unifying main types - they are both App(Sym(sgn.name), args) which would
       trigger infinite recursion through whnf -> instantiate. The signatures 
       already have the same name (checked in unify_sgn), so main types are equal. *)
    (* Unify arguments pairwise *)
    List.fold_left2 (fun env_opt a1 a2 ->
        Option.bind env_opt (fun env -> unify_chiral kctx a1 a2 env)
      ) (Some env) x1.arguments x2.arguments

(** Unify chiral types *)
and unify_chiral
    (kctx: kind Ident.tbl) (ct1: chiral_typ) (ct2: chiral_typ) (env: solving_env)
    : solving_env option =
  match ct1, ct2 with
    Lhs t1, Lhs t2 -> unify kctx t1 t2 env
  | Rhs t1, Rhs t2 -> unify kctx t1 t2 env
  | _ -> None  (* Chirality mismatch *)

(* ========================================================================= *)
(* Equation solving *)
(* ========================================================================= *)

let rec solve (kctx: kind Ident.tbl) (c: equation) (env: solving_env) : solving_env option =
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
          solve kctx body { env' with local_eqs = collect_eqs assumption @ env'.local_eqs }
