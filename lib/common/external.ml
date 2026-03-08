(**
  module: Common.External
  description: External types and values used across all IRs.
*)

open Stdint

(* External types are always positive *)
type ext_type =
    Int

type ext_value =
    IntVal of int64

let type_of = function
    IntVal _ -> Int


(** Convert ext_type to string *)
let ext_type_to_string = function
    Int -> "int"

(** Convert ext_value to string *)
let ext_value_to_string = function
  | IntVal x -> Int64.to_string x
