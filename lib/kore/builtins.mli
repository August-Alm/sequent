(**
  Module: Kore.Builtins
  Description: Built-ins for polarized sequent calculus.
 
  This module defines built-in types and operations for the polarized sequent calculus.
*)

open Common.Identifiers
open Types
open Terms

module Sym: sig
  val i32_t: symbol
  val i32_add: symbol
  val i32_ifz: symbol

  val fun_t: symbol
  val fun_apply: symbol

  val pos_t: symbol
  val pos_close: symbol

  val neg_t: symbol
  val neg_thunk: symbol

  val box_t: symbol
  val box_mk: symbol

  val all_t: kind -> symbol
  val all_ins: kind -> symbol
  val all_kind_opt: symbol -> kind option 
end 

module Ext: sig
  val int_t: tpe
  val int_add: import
  val int_ifz: import
end

module Prim: sig
  
  (**
    code (X:+) → (Y:−) where
      ·: X | X → Y ⊢ Y   --- apply(prd X, cns Y)
  *)
  val fun_t: tpe
  val fun_sgn: signature
  val fun_apply: xtor

  (**
    code ∀(F: k → +) where
      ·{}: | ∀F ⊢{X} F(X)   --- insta{X}(cns F(X))
  *)
  val all_t: kind -> tpe
  val all_sgn: kind -> signature
  val all_insta: kind -> xtor

  (**
    data ↑(A:-) where
      close: A ⊢ ↑A |   --- close(x: prd A)
  *)
  val pos_t: tpe
  val pos_sgn: signature
  val pos_close: xtor

  (**
    code ↓(A:+) where
      thunk: | ↓A ⊢ A   --- thunk(k: cns A)
  *)
  val neg_t: tpe
  val neg_sgn: signature
  val neg_thunk: xtor

  (**
    data □(A:ext) where
      mk: A ⊢ □A   --- mk(x: prd A)
  *)
  val box_t: tpe
  val box_sgn: signature
  val box_mk: xtor
end
