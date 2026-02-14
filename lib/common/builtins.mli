(**
  module: Common.Builtins
  description: Built-in types and operations.
*)

open Identifiers
open Types

module Sym: sig
  val fun_t: sym
  val fun_apply: sym
  val raise_t: sym
  val raise_pack: sym
  val lower_t: sym
  val lower_return: sym
  val box_t: sym
  val box_mk: sym
  val all_t: kind -> sym
  val all_instantiate: kind -> sym
  val all_kind_opt: sym -> kind option
end

module Prim: sig
  val fun_sgn: sgn_typ
  val fun_apply: xtor
  val raise_sgn: sgn_typ
  val raise_pack: xtor
  val lower_sgn: sgn_typ
  val lower_return: xtor
  val all_sgn: Ident.t -> kind -> sgn_typ
  val all_instantiate: Ident.t -> kind -> xtor
end
