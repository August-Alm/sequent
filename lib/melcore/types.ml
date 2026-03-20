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
open Common.Uses

module MelcoreBase = struct
  type polarity = Typ
  let eq_polarity _ _ = true
  let data_polarity = Typ
  let code_polarity = Typ
  let polarities = [Typ]

  type 'a chiral = use * 'a
  let chiral_map f (u, x) =  (u, f x)
  let strip_chirality (_, x) = x
  let chiral_use (u, _) = u
  let mk_producer (u, x) = (u, x)
  let mk_consumer (u, x) = (u, x)
  let is_producer _ = true
  let is_consumer _ = true
  (* In Melcore there's no Prd/Cns distinction, usage is covariant *)
  let chiral_sub typ_eq (u1, t1) (u2, t2) = typ_eq t1 t2 && Use.leq u1 u2
end

module MelcoreTypes = TypeSystem(MelcoreBase)