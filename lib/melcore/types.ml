(**
  module: Melcore.Types
  description: Type system of the Melcore language.

  It incorporates the following features:
  - Polarity (positive/negative) to distinguish data and codata types
  - Higher-kinded types
  - Generalized algebraic data types
  - Generalized algebraic codata types
  - Algebraic data types automatically promoted to the kind level
*)

open Common.Types

module MelcoreBase = struct
  type polarity = Typ
  let eq_polarity _ _ = true
  let data_polarity = Typ
  let code_polarity = Typ
  let polarities = [Typ]

  type 'a chiral = 'a
  let chiral_map f x =  f x
  let strip_chirality x = x
  let mk_producer x = x
  let mk_consumer x = x
  let is_producer _ = true
  let is_consumer _ = true
end

module MelcoreTypes = TypeSystem(MelcoreBase)