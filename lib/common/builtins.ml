(**
  module: Common.Builtins
  description: Built-in types and operations.
*)

open Identifiers
open Types

module Prim = struct

  let i32_t = Path.of_primitive 1 "i32"
  let i32_add = Path.access i32_t "add"
  let i32_ifz = Path.access i32_t "ifz"
  let i32_lit n = Path.access i32_t ("lit_" ^ string_of_int n)

end