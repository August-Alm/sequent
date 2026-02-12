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
    Ext of ext_typ
  | Var of var_typ ref (* Free, local type variable *)
  | Rigid of Ident.t (* Rigid/skolem variable *)
  | Sym of sym (* Reference to a signature *)
  | App of typ * (typ list)
  | Sgn of sgn_typ (* A signature *)

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

type solving_env =
  { subst: (var_typ ref * typ) list (* Current substitution - keyed by ref *)
  ; local_eqs: (typ * typ) list (* Local assumptions (from GADT matches) *)
  }

(** Find a var ref in the substitution using physical equality *)
let rec find_subst (r: var_typ ref) (subst: (var_typ ref * typ) list) : typ option =
  match subst with
    [] -> None
  | (r', t) :: _ when r == r' -> Some t
  | _ :: rest -> find_subst r rest

(** Apply a substitution to a type, following links *)
let rec substitute (subst: (var_typ ref * typ) list) (t: typ) : typ =
  match t with
    Var ({contents = Link t'}) -> substitute subst t'
  | Var ({contents = Unbound _} as r) ->
      (match find_subst r subst with Some t' -> t' | None -> t)
  | App (f, args) -> App (substitute subst f, List.map (substitute subst) args)
  | Sgn s -> Sgn { s with 
      xtors = List.map (fun x -> 
        { x with
          arguments = List.map (chiral_map (substitute subst)) x.arguments
        ; main = substitute subst x.main 
        }) s.xtors 
    }
  | Ext _ | Rigid _ | Sym _ -> t

(** Occurs check: does variable r occur in type t? *)
let rec occurs (r: var_typ ref) (t: typ) : bool =
  match t with
    Var r' when r == r' -> true
  | Var {contents = Link t'} -> occurs r t'
  | Var {contents = Unbound _} -> false
  | App (f, args) -> occurs r f || List.exists (occurs r) args
  | Sgn s -> List.exists (fun x -> 
      List.exists (occurs_chiral r) x.arguments || occurs r x.main
    ) s.xtors
  | Ext _ | Rigid _ | Sym _ -> false

and occurs_chiral (r: var_typ ref) (ct: chiral_typ) : bool =
  match ct with Lhs t | Rhs t -> occurs r t

(** Decompose an equation into a list of type equalities.
    Extracts all Equal pairs from the equation structure. *)
let rec decompose_eq (eq: equation) : (typ * typ) list =
  match eq with
    Equal (t1, t2) -> [(t1, t2)]
  | And (e1, e2) -> decompose_eq e1 @ decompose_eq e2
  | Implies (assum, body) -> decompose_eq assum @ decompose_eq body
  | Exists (_, e) -> decompose_eq e
  | True -> []

(** Unify two lists of types pairwise *)
let rec unify_args (args1: typ list) (args2: typ list) (env: solving_env) 
    : solving_env option =
  match args1, args2 with
    [], [] -> Some env
  | t1 :: rest1, t2 :: rest2 ->
      Option.bind (unify t1 t2 env) (unify_args rest1 rest2)
  | _ -> None (* Length mismatch *)

and solve (c: equation) (env: solving_env) : solving_env option =
  match c with
    True -> Some env
  | Equal (t1, t2) -> unify t1 t2 env
  | And (c1, c2) -> Option.bind (solve c1 env) (solve c2)
  | Exists (_, c) -> solve c env
  | Implies (assumption, body) ->
      (* Add assumption to local equalities, solve body *)
      solve body {
        env with local_eqs = decompose_eq assumption @ env.local_eqs
      }

and unify (t1: typ) (t2: typ) (env: solving_env) : solving_env option =
  let t1 = substitute env.subst t1 in
  let t2 = substitute env.subst t2 in
  match t1, t2 with
    Ext e1, Ext e2 -> if e1 = e2 then Some env else None
  | Var r1, Var r2 when !r1 = !r2 -> Some env
  | Var ({contents = Unbound _} as r), t 
  | t, Var ({contents = Unbound _} as r) ->
      (* Occurs check, then link *)
      if occurs r t then None
      else (r := Link t; Some env)
  | Sym s1, Sym s2 -> 
      if Path.equal s1 s2 then Some env else None
  (* Signatures are nominal *)
  | Sgn sg1, Sgn sg2 -> 
      if Path.equal sg1.name sg2.name then Some env else None
  (* Symbols reference signatures *)
  | Sym s, Sgn sg | Sgn sg, Sym s ->
      if Path.equal s sg.name then Some env else None
  | App (Sym s1, a1), App (Sym s2, a2) ->
      if Path.equal s1 s2 then unify_args a1 a2 env else None
  | Rigid a, Rigid b when Ident.equal a b -> Some env
  | Rigid a, t | t, Rigid a ->
      (* Check if local assumptions tell us rigid 'a equals t *)
      if List.exists (fun (t1, t2) -> 
        (t1 = Rigid a && t2 = t) || (t2 = Rigid a && t1 = t)
      ) env.local_eqs
      then Some env
      else None  (* Rigid variable can't be unified otherwise *)
  | App (f1, a1), App (f2, a2) ->
      Option.bind (unify f1 f2 env) (unify_args a1 a2)
  | _ -> None

(* ========================================================================= *)

type var = Ident.t

type command =
    (* let v = m[τ, ...](Γ); s *)
    (* Binds v as a producer of the signature type that has m as xtor *)
    Let of var * xtor * typ list * var list * command
    (* switch v { m[τ, ...](Γ) ⇒ s, ... } *)
    (* Pattern matches on a producer value of a signature type *)
  | Switch of sgn_typ * var * branch
    (* new v = (Γ){ m[τ, ...](Γ') ⇒ s', ... }; s *)
    (* Binds v as a consumer of a signature type *)
  | New of sgn_typ * var * branch * command
    (* invoke v m[τ, ...](v', ...) *)
    (* Cuts consumer v of a signature type with xtor *)
  | Invoke of var * xtor * var list
    (* ⟨v | k⟩ *)
    (* Cut at type, passing producer v to consumer k *)
  | Axiom of typ * var * var
    (* lit n { (v) ⇒ s } *)
    (* Binds v as a producer of an integer literal *)
  | Lit of int * var * command
    (* add(x, y) { (v) ⇒ s } *)
    (* Binds v as a producer of the sum of x and y *)
  | Add of var * var * var * command
    (* ifz(v) { () ⇒ sThen; () ⇒ sElse } *)
    (* If-zero-branching on integer producer *)
  | Ifz of var * command * command
    (* ret ty v - return the value of v at type ty (terminal) *)
  | Ret of typ * var
    (* end (terminal) *)
  | End

and branch = var list * command