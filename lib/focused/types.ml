(**
  module: Focused.Types

  description: A depolarized type system for the focused sequent calculus.

  Types are unpolarized: the same signature can be read as data or codata.
    - Data reading: Let (constructor), Switch (pattern match)
    - Codata reading: New (copattern), Invoke (destructor)
*)

open Common.Types

module FocusedBase = struct
  type polarity = Typ
  let eq_polarity _ _ = true
  let data_polarity = Typ
  let code_polarity = Typ
  let polarities = [Typ]
  
  type 'a chiral = Prd of 'a | Cns of 'a
  let chiral_map f = function Prd x -> Prd (f x) | Cns x -> Cns (f x)
  let strip_chirality = function Prd x | Cns x -> x
  let mk_producer x = Prd x
  let mk_consumer x = Cns x
  let is_producer = function Prd _ -> true | Cns _ -> false
  let is_consumer = function Prd _ -> false | Cns _ -> true
end

module FocusedTypes = TypeSystem(FocusedBase)
