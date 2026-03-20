(**
  module: Axil.Types

  description: A depolarized type system for AXIL.

  Types are unpolarized: the same signature can be read as data or codata.
    - Data reading: Let (constructor), Switch (pattern match)
    - Codata reading: New (copattern), Invoke (destructor)
*)

open Common.Types
open Common.Uses

module AxilBase = struct
  type polarity = Typ
  let eq_polarity _ _ = true
  let data_polarity = Typ
  let code_polarity = Typ
  let polarities = [Typ]
  
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

module AxilTypes = TypeSystem(AxilBase)
