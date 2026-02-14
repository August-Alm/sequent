(**
  module: Core.Terms
  description: Abstract syntax and type checking for the core language.
*)

open Common.Identifiers
open Common.Types

let ( let* ) o f = Utility.( let* ) o f

type var = Ident.t

type command =
    Cut of typ * term * term  (** ⟨producer | consumer⟩ at type **)
  | Add of term * term * term
  | Ifz of term * command * command
  | End

and term =
    Variable of var
  | Lit of int
  (** Constructors build data (Lhs/producer) **)
  | Ctor of sgn_typ * xtor * term list
  (** Destructors build codata (Rhs/consumer) **)
  | Dtor of sgn_typ * xtor * term list
  (** Match consumes data (Rhs/consumer) **)
  | Match of sgn_typ * var * branch list
  (** Comatch produces codata (Lhs/producer) **)
  | Comatch of sgn_typ * var * branch list
  (** Mu binds a continuation **)
  | MuLhs of typ * var * command  (** μL binds Rhs var, forms Lhs **)
  | MuRhs of typ * var * command  (** μR binds Lhs var, forms Rhs **)

and branch = xtor * var list * command
