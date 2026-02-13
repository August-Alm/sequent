(**
  module: Common.Types
  description: A type system common to sequent calculus-based intermediate languages.
*)

open Identifiers

type sym = Path.t

type kind = Star | Arrow of kind * kind

val encode: kind -> int
val decode: int -> kind
val compare_kinds: kind -> kind -> int

type ext_typ = Int

type typ =
    Ext of ext_typ
  | Var of var_typ ref
  | Rigid of Ident.t
  | Sym of sym * sgn_typ lazy_t
  | App of typ * typ list
  | Sgn of sgn_typ

and var_typ = Unbound of Ident.t | Link of typ

and sgn_typ =
  { name: sym
  ; parameters: (Ident.t * kind) list
  ; xtors: xtor list;
  }

and xtor =
  { name: sym
  ; parameters: (Ident.t * kind) list
  ; existentials: (Ident.t * kind) list
  ; arguments: chiral_typ list
  ; main: typ
  }

and chiral_typ = Lhs of typ | Rhs of typ

and equation =
    Equal of typ * typ
  | And of equation * equation
  | Exists of var_typ * equation
  | Implies of equation * equation
  | True

val chiral_map: (typ -> typ) -> chiral_typ -> chiral_typ

type kind_error =
    UnboundVariable of Ident.t
  | ExpectedHKT of typ * kind
  | KindMismatch of {expected : kind; actual : kind}
  | ExistentialEscape of {xtor : sym; existential : Ident.t}

val infer_kind: kind Ident.tbl -> typ -> (kind, kind_error) result
val check_kind: kind Ident.tbl -> typ -> kind -> (unit, kind_error) result
val subst_rigid: (Ident.t * typ) list -> typ -> typ
val subst_rigid_sgn: (Ident.t * typ) list -> sgn_typ -> sgn_typ
val subst_rigid_xtor: (Ident.t * typ) list -> xtor -> xtor

type solving_env =
  { subs: (var_typ ref * typ) list
  ; local_eqs: (typ * typ) list
  }

val empty_env: solving_env

val whnf: kind Ident.tbl -> (var_typ ref * typ) list -> typ -> typ
val instantiate: kind Ident.tbl -> sgn_typ lazy_t -> typ list -> sgn_typ
val can_unify_shallow: typ -> typ list -> Path.t -> bool
val can_unify_shallow_types: typ -> typ -> bool
val unify_args: kind Ident.tbl -> typ list -> typ list -> solving_env -> solving_env option
val unify: kind Ident.tbl -> typ -> typ -> solving_env -> solving_env option
val unify_sgn: kind Ident.tbl -> sgn_typ -> sgn_typ -> solving_env -> solving_env option
val unify_xtor: kind Ident.tbl -> xtor -> xtor -> solving_env -> solving_env option
val unify_chiral: kind Ident.tbl -> chiral_typ -> chiral_typ -> solving_env -> solving_env option

val solve: kind Ident.tbl -> equation -> solving_env -> solving_env option