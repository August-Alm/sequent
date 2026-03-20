(**
  module: Melcore.Types
  description: Type system of the Melcore language.

  It incorporates the following features:
  - Polarity (positive/negative) to distinguish data and codata types
  - Higher-kinded types
  - Generalized algebraic data types
  - Generalized algebraic codata types
  - Algebraic data types automatically promoted to the kind level
*)

open Common.Types
open Common.Uses

module MelcoreBase = struct
  type polarity = Typ
  let eq_polarity _ _ = true
  let data_polarity = Typ
  let code_polarity = Typ
  let polarities = [Typ]

  type 'a chiral = use * 'a
  let chiral_map f (u, x) =  (u, f x)
  let strip_chirality (_, x) = x
  let chiral_use (u, _) = u
  let mk_producer (u, x) = (u, x)
  let mk_consumer (u, x) = (u, x)
  let is_producer _ = true
  let is_consumer _ = true
  (* In Melcore there's no Prd/Cns distinction, usage is covariant *)
  let chiral_sub typ_eq (u1, t1) (u2, t2) = typ_eq t1 t2 && Use.leq u1 u2
end

module MelcoreTypes = struct
  open Common.Identifiers
  include TypeSystem(MelcoreBase)

  let lack_ctor =
    let a = Ident.mk "a" in
    let b = Ident.mk "b" in
    { name = Prim.lack_ctor_sym
    ; quantified =
      [ (a, Base MelcoreBase.Typ)
      ; (b, Base MelcoreBase.Typ)
      ]
    ; existentials = []
    ; argument_types =
        [ MelcoreBase.mk_producer (Unr, TVar a)
        ; MelcoreBase.mk_producer (Lin, TVar b)
        ]
    ; main = Sgn (Prim.lack_sym, [TVar a; TVar b])
    ; original_index = 0
    }
  
  let lack_dec =
    { name = Prim.lack_sym
    ; data_sort = Data
    ; param_kinds = [Base MelcoreBase.Typ; Base MelcoreBase.Typ]
    ; type_args = []  (* Uninstantiated *)
    ; xtors = [lack_ctor]
    }

  let lack_sgn a b = Sgn (Prim.lack_sym, [a; b])

  let empty_context =
    let ctx = Option.get (add_declaration empty_context unit_dec) in
    Option.get (add_declaration ctx lack_dec)

end