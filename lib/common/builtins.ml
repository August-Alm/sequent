(**
  module: Common.Builtins
  description: Built-in types and operations.
*)

open Identifiers
open Types

module Sym = struct

  let fun_t = Path.of_primitive 100 "fun"
  let fun_apply = Path.access fun_t "apply"

  let raise_t = Path.of_primitive 101 "raise"
  let raise_pack = Path.access raise_t "pack"

  let lower_t = Path.of_primitive 102 "lower"
  let lower_return = Path.access lower_t "return"

  let box_t = Path.of_primitive 103 "box"
  let box_mk = Path.access box_t "mk"

  let exists_t k = Path.of_primitive (999 + 2 * encode k) "exists"
  let exists_pack k = Path.access (exists_t k) "pack"

  let all_t k = Path.of_primitive (1000 + 2 * encode k) "all"
  let all_instantiate k = Path.access (all_t k) "instantiate"

  let all_kind_opt (s: Path.t) =
    match Path.as_ident s with
    | Some id ->
      let n = -Ident.stamp id - 1000 in
      if n >= 0 && n mod 2 = 0 then Some (decode (n / 2)) else None
    | None -> None

  let exists_kind_opt (s: Path.t) =
    match Path.as_ident s with
    | Some id ->
      let n = -Ident.stamp id - 999 in
      if n >= 0 && n mod 2 = 0 then Some (decode (n / 2)) else None
    | None -> None

end

module Prim = struct

  let rec fun_sgn_lazy =
    let a = Ident.mk "a" in
    let b = Ident.mk "b" in
    let ta = Var (ref (Unbound a)) in
    let tb = Var (ref (Unbound b)) in
    lazy
    { name = Sym.fun_t
    ; parameters = [Star; Star]  (* Just kinds, no names *)
    ; xtors = [
        { name = Sym.fun_apply
        ; parameters = [(a, Star); (b, Star)]  (* xtor binds the type vars *)
        ; existentials = []
        ; arguments = [Lhs ta; Rhs tb]
        ; main = App (Sym (Sym.fun_t, fun_sgn_lazy), [ta; tb])
        }
      ]
    }
  
  let fun_sgn = Lazy.force fun_sgn_lazy
  let fun_apply = List.hd fun_sgn.xtors

  let rec raise_sgn_lazy =
    let a = Ident.mk "a" in
    let ta = Var (ref (Unbound a)) in
    lazy
    { name = Sym.raise_t
    ; parameters = [Star]  (* Just kinds *)
    ; xtors = [
        { name = Sym.raise_pack
        ; parameters = [(a, Star)]  (* xtor binds the type var *)
        ; existentials = []
        ; arguments = [Rhs ta]
        ; main = App (Sym (Sym.raise_t, raise_sgn_lazy), [ta])
        }
      ]
    }
  
  let raise_sgn = Lazy.force raise_sgn_lazy
  let raise_pack = List.hd raise_sgn.xtors

  let rec lower_sgn_lazy =
    let a = Ident.mk "a" in
    let ta = Var (ref (Unbound a)) in
    lazy
    { name = Sym.lower_t
    ; parameters = [Star]  (* Just kinds *)
    ; xtors = [
        { name = Sym.lower_return
        ; parameters = [(a, Star)]  (* xtor binds the type var *)
        ; existentials = []
        ; arguments = [Lhs ta]
        ; main = App (Sym (Sym.lower_t, lower_sgn_lazy), [ta])
        }
      ]
    }
  
  let lower_sgn = Lazy.force lower_sgn_lazy
  let lower_return = List.hd lower_sgn.xtors

  let rec all_sgn_lazy a k =
    let t = Ident.mk "t" in
    let tt = Var (ref (Unbound t)) in
    let ta = Var (ref (Unbound a)) in
    lazy
    { name = Sym.all_t k
    ; parameters = [k]  (* Just kinds *)
    ; xtors = [
        { name = Sym.all_instantiate k
        ; parameters = [(t, Arrow (k, Star)); (a, k)]
        ; existentials = []
        ; arguments = [Lhs (App (tt, [ta]))]
        ; main = App (Sym (Sym.all_t k, all_sgn_lazy a k), [App (tt, [ta])])
        }
      ]
    }
  
  let all_sgn a k = Lazy.force (all_sgn_lazy a k)
  let all_instantiate a k = List.hd (all_sgn a k).xtors

end