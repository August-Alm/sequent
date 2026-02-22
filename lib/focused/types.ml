(**
  module: Focused.Types

  description: A depolarized type system for the focused sequent calculus.

  Types are unpolarized: the same signature can be read as data or codata.
    - Data reading: Let (constructor), Switch (pattern match)
    - Codata reading: New (copattern), Invoke (destructor)
*)

open Common.Types

module FocusedBase = struct
  type polarity = Pos | Neg
  let eq_polarity p1 p2 = (p1 = p2)
  let data_polarity = Pos
  let code_polarity = Neg
  let polarities = [Pos; Neg]
  (*
  type polarity = Typ
  let eq_polarity _ _ = true
  let data_polarity = Typ
  let code_polarity = Typ
  let polarities = [Typ]
  *)
  type 'a chiral = Prd of 'a | Cns of 'a
  let chiral_map f = function Prd x -> Prd (f x) | Cns x -> Cns (f x)
  let strip_chirality = function Prd x | Cns x -> x
  let mk_producer x = Prd x
  let mk_consumer x = Cns x
  let is_producer = function Prd _ -> true | Cns _ -> false
  let is_consumer = function Prd _ -> false | Cns _ -> true
end

module FocusedTypes = struct
  include TypeSystem(FocusedBase)

  type partity = Even | Odd

  let parity_of (ctx: context) (t: chiral_typ) : partity option =
    match t with
      Prd t ->
      (match infer_kind ctx t with
        Ok (Base Pos) -> Some Even
      | Ok (Base Neg) -> Some Odd
      | _ -> None)
    | Cns t ->
      (match infer_kind ctx t with
        Ok (Base Pos) -> Some Odd
      | Ok (Base Neg) -> Some Even
      | _ -> None)
end