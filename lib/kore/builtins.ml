(**
  Module: Kore.Builtins
  Description: Built-ins for polarized sequent calculus.
 
  This module defines built-in types and operations for the polarized sequent calculus.
*)

open Common.Identifiers
open Types
open Terms

module Sym = struct
  let i32_t = Path.of_primitive 1 "i32"
  let i32_add = Path.access i32_t "add"
  let i32_ifz = Path.access i32_t "ifz"

  let fun_t = Path.of_primitive 100 "fun"
  let fun_apply = Path.access fun_t "apply"

  let pos_t = Path.of_primitive 200 "pos"
  let pos_close = Path.access pos_t "close"

  let neg_t = Path.of_primitive 201 "neg"
  let neg_thunk = Path.access neg_t "thunk"

  let box_t = Path.of_primitive 202 "box"
  let box_mk = Path.access box_t "mk"


  (* Newton's method for integer square root *)
  let isqrt n =
    if n < 0 then invalid_arg "isqrt"
    else if n = 0 then 0
    else
      let rec go x =
        let x' = (x + n / x) / 2 in
        if x' >= x then x else go x'
      in
      go n

  (* Cantor's diagonal *)
  let cantor_pair x y = (x + y) * (x + y + 1) / 2 + y

  let cantor_unpair p =
    let w = (isqrt (8 * p + 1) - 1) / 2 in
    let t = (w * w + w) / 2 in
    let y = p - t in
    let x = w - y in
    (x, y)

  let rec encode =
    function
    | Pos -> 0
    | Neg -> 1
    | Ext -> 2
    | Arrow (k1, k2) -> cantor_pair (encode k1) (encode k2) + 3

  let rec decode n =
    if n < 3 then
      match n with 0 -> Pos | 1 -> Neg | _ -> Ext
    else
      let (x, y) = cantor_unpair (n - 3) in
      Arrow (decode x, decode y)
  
  let compare_kinds k1 k2 =
    let n1 = encode k1 in
    let n2 = encode k2 in
    compare n1 n2
  
  let all_t k = Path.of_primitive (1000 + encode k) "all"
  let all_ins k = Path.access (all_t k) "insta"

  let all_kind_opt (s : Path.t) =
    match Path.as_ident s with
    | Some id ->
      let n = Ident.stamp id - 1000 in
      if n >= 0 then Some (decode n) else None
    | None -> None
end

module Ext = struct
  let int_t = TyExt (Sym.i32_t)

  let mk_binop sym =
    { name = sym
    ; parameter_types = [Lhs int_t; Lhs int_t]
    ; clauses_types = [[Lhs int_t]]
    }

  let int_add = mk_binop Sym.i32_add
  
  let int_ifz =
    { name = Sym.i32_ifz
    ; parameter_types = [Lhs int_t]
    ; clauses_types = [[]; []]
    }
  
  let imports =
    List.fold_left (fun tbl (imp: import) ->
      Path.add imp.name imp tbl
    ) Path.emptytbl
      [ int_add
      ; int_ifz
      ]
    
end

module Prim = struct

  let fun_apply =
    let a = Ident.mk "a" in
    let b = Ident.mk "b" in
    { name = Sym.fun_apply
    ; parent = Sym.fun_t
    ; quantified = [(a, Pos); (b, Neg)]
    ; parameters = [Lhs (TyVar a); Rhs (TyVar b)]
    ; parent_arguments = [TyVar a; TyVar b]
    ; constraints = None
    }
  let fun_sgn =
    { name = Sym.fun_t
    ; arguments = [(None, Pos); (None, Neg)]
    ; xtors = [fun_apply]
    }
  let fun_t = TyNeg fun_sgn

  let all_insta a k =
    let t = Ident.mk "t" in
    { name = Sym.all_ins k
    ; parent = Sym.all_t k
    ; quantified = [(t, Arrow (k, Neg)); (a, k)]
    ; parameters = [Rhs (TyApp (TyVar t, TyVar a))]
    ; parent_arguments = [TyVar t]
    ; constraints = None
    }
  let all_sgn a k =
    { name = Sym.all_t k
    ; arguments = [(None, Arrow (k, Neg)); (None, k)]
    ; xtors = [all_insta a k]
    }
  let all_t a k = TyNeg (all_sgn a k)
  
  let pos_close =
    let a = Ident.mk "a" in
    { name = Sym.pos_close
    ; parent = Sym.pos_t
    ; quantified = [(a, Neg)]
    ; parameters = [Lhs (TyVar a)]
    ; parent_arguments = [TyVar a]
    ; constraints = None
    }
  let pos_sgn =
    { name = Sym.pos_t
    ; arguments = [(None, Neg)]
    ; xtors = [pos_close]
    }
  let pos_t = TyPos pos_sgn

  let neg_thunk =
    let a = Ident.mk "a" in
    { name = Sym.neg_thunk
    ; parent = Sym.neg_t
    ; quantified = [(a, Pos)]
    ; parameters = [Rhs (TyVar a)]
    ; parent_arguments = [TyVar a]
    ; constraints = None
    }
  let neg_sgn =
    { name = Sym.neg_t
    ; arguments = [(None, Pos)]
    ; xtors = [neg_thunk]
    }
  let neg_t = TyNeg neg_sgn

  let box_mk =
    let a = Ident.mk "a" in
    { name = Sym.box_mk
    ; parent = Sym.box_t
    ; quantified = [(a, Ext)]
    ; parameters = [Lhs (TyVar a)]
    ; parent_arguments = [TyVar a]
    ; constraints = None
    }
  let box_sgn =
    { name = Sym.box_t
    ; arguments = [(None, Ext)]
    ; xtors = [box_mk]
    }
  let box_t = TyNeg box_sgn
  
  let signatures =
    List.fold_left (fun tbl (s, pol, sgn, k) ->
      Path.add s (sgn, pol, k) tbl
    ) Path.emptytbl
      [ (Sym.fun_t, Negative, fun_sgn, Arrow (Pos, Neg))
      ; (Sym.pos_t, Positive, pos_sgn, Arrow (Neg, Pos))
      ; (Sym.neg_t, Negative, neg_sgn, Arrow (Pos, Neg))
      ; (Sym.box_t, Positive, box_sgn, Arrow (Ext, Pos))
      ]
end