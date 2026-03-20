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
open Common.Uses

module CoreBase = struct
  type polarity = Pos | Neg
  let eq_polarity p1 p2 = (p1 = p2)
  let data_polarity = Pos
  let code_polarity = Neg
  let polarities = [Pos; Neg]

  type 'a chiral = Prd of use * 'a | Cns of use * 'a
  let chiral_map f = function Prd (u, x) -> Prd (u, f x) | Cns (u, x) -> Cns (u, f x)
  let strip_chirality = function Prd (_, x) | Cns (_, x) -> x
  let chiral_use = function Prd (u, _) | Cns (u, _) -> u
  let mk_producer (u, x) = Prd (u, x)
  let mk_consumer (u, x) = Cns (u, x)
  let is_producer = function Prd _ -> true | Cns _ -> false
  let is_consumer = function Prd _ -> false | Cns _ -> true
  let chiral_sub typ_eq ct1 ct2 =
    let t1, t2 = strip_chirality ct1, strip_chirality ct2 in
    if not (typ_eq t1 t2) then false
    else match ct1, ct2 with
      | Prd (u1, _), Prd (u2, _) -> Use.leq u1 u2  (* covariant: prd unr T ≤ prd lin T *)
      | Cns (u1, _), Cns (u2, _) -> Use.leq u2 u1  (* contravariant: cns lin T ≤ cns unr T *)
      | _ -> false  (* chirality mismatch *)
end

module CoreTypes = TypeSystem(CoreBase)