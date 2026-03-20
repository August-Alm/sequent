(**
  module: Common.Uses
  description: Usage modes for quantitative type system.
*)

type use = Lin | Unr

module Use = struct

  let add _ _ =  Unr

  let mul m n =
    match m, n with
      Lin, u | u, Lin -> u
    | _ -> Unr
  
  (* Subusaging: Unr ≤ Lin (unrestricted can be used where linear expected) *)
  let leq m n =
    match m, n with
      Lin, Lin -> true
    | Unr, Lin -> true  (* key: unr value can fill lin slot *)
    | Unr, Unr -> true
    | _ -> false

  let pp = function Lin -> "1" | Unr -> "ω"

end
