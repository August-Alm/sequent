(**
  module: Core.Types
  description: A polarized type system for the core sequent calculus.

  It incorporates the following features:
  - Polarity (positive/negative) to distinguish data and codata types
  - Chirality (producer/consumer) to distinguish terms
  - Higher-kinded types
  - Generalized algebraic data types
  - Generalized algebraic codata types
  - Algebraic data types automatically promoted to the kind level
*)

open Common.Types

module CoreBase = struct
  type polarity = Pos | Neg
  let eq_polarity p1 p2 = (p1 = p2)
  let data_polarity = Pos
  let code_polarity = Pos
  let polarities = [Pos; Neg]

  type 'a chiral = Prd of 'a | Cns of 'a
  let chiral_map f = function Prd x -> Prd (f x) | Cns x -> Cns (f x)
  let strip_chirality = function Prd x | Cns x -> x
  let mk_producer x = Prd x
  let mk_consumer x = Cns x
  let is_producer = function Prd _ -> true | Cns _ -> false
  let is_consumer = function Prd _ -> false | Cns _ -> true
end

module CoreTypes = TypeSystem(CoreBase)