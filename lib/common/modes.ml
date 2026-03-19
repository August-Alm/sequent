(**
  module Common.Modes
  description: Modes describe variable usage.
*)

open Identifiers

module Mod = struct
  
  type use = One | Omega

  type age = Gen of int | Inf

  type t = { use: use; age: age }

  let one = { use = One; age = Gen 0 }
  
  let omega = { use = Omega; age = Inf }

  let up = { use = One; age = Gen 1 }

  let sum m n =
    { use = Omega
    ; age =
        (match m.age, n.age with
          Gen i, Gen j when i = j -> Gen i
        | _ -> Inf)
    }

  let mult m n =
    { use =
        (match m.use, n.use with
          One, One -> One
        | _ -> Omega)
    ; age =
        (match m.age, n.age with
          Gen i, Gen j -> Gen (i + j)
        | _ -> Inf)
    }

  let leq m n =
    (match m.use, n.use with
      One, One | Omega, Omega -> true
    | _ -> false) &&
    (match m.age, n.age with
      Gen i, Gen j when i = j -> true
    | Gen _, Gen _ -> failwith "Incomparable ages!"
    | Gen _, Inf | Inf, Inf -> true
    | _ -> false)
    

end