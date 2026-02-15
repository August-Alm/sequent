(**
  module: Encode
  description: Translates from Melcore to Core.
*)

module MTy = Melcore.Types
module MTm = Melcore.Terms
module CTy = Common.Types
module CTm = Core.Terms

open Common.Identifiers
open Common.Builtins

let a = Ident.mk "a"

(* Map Melcore kinds to Core kinds *)
let rec map_kind (k: MTy.kind) : CTy.kind =
  match k with
    MTy.Star -> CTy.Star
  | MTy.Arrow (k1, k2) -> CTy.Arrow (map_kind k1, map_kind k2)

(* Lower ↓(A) *)
let lower (ty: CTy.typ) : CTy.typ = App (Sgn Prim.lower_sgn, [ty])

(* Raise ↑(A) *)
let raise (ty: CTy.typ) : CTy.typ = App (Sgn Prim.raise_sgn, [ty])

(* Check if a Melcore type is positive (data) or negative (codata) *)
let rec is_positive (ty: MTy.typ) : bool option =
  match ty with
    MTy.Ext _ -> Some true
  | MTy.Var _ -> None
  | MTy.Rigid _ -> None
  | MTy.Sym (_, MTy.Pos, _) -> Some true
  | MTy.Sym (_, MTy.Neg, _) -> Some false
  | MTy.App (t, _) -> is_positive t
  | MTy.Fun _ -> Some false
  | MTy.All _ -> Some false
  | MTy.Data _ -> Some true
  | MTy.Code _ -> Some false

let rec map_typ (ty: MTy.typ) : CTy.typ =
  match ty with
    MTy.Ext Int -> CTy.Ext Int
  | MTy.Var v ->
      (match !v with
        Unbound x -> CTy.Var (ref (CTy.Unbound (Ident.mk (Ident.name x))))
      | Link t -> CTy.Var (ref (CTy.Link (map_typ t))))
  | MTy.Rigid r -> CTy.Rigid r
  | MTy.Sym (s, Pos, sgn_lazy) -> CTy.Sym (s, lazy (map_data (Lazy.force sgn_lazy)))
  | MTy.Sym (s, Neg, sgn_lazy) -> CTy.Sym (s, lazy (map_code (Lazy.force sgn_lazy)))
  | MTy.App (t, args) ->
      let t' = map_typ t in
      let arg_tys = List.map map_typ args in
      App (t', arg_tys)
  | MTy.Data sgn -> Sgn (map_data sgn)
  | MTy.Code sgn -> Sgn (map_code sgn)
  | MTy.Fun _ -> failwith "Cannot encode function types directly"
  | MTy.All _ -> failwith "Cannot encode polymorphic types directly"

and map_data (sgn: MTy.sgn_typ) : CTy.sgn_typ =
  { CTy.name = sgn.MTy.name
  ; CTy.parameters = List.map (fun (id, k) -> (id, map_kind k)) sgn.MTy.parameters
  ; CTy.xtors = List.map map_ctor sgn.MTy.xtors
  }

and map_code (sgn: MTy.sgn_typ) : CTy.sgn_typ =
  { CTy.name = sgn.MTy.name
  ; CTy.parameters = List.map (fun (id, k) -> (id, map_kind k)) sgn.MTy.parameters
  ; CTy.xtors = List.map map_dtor sgn.MTy.xtors
  }

and map_ctor (xtor: MTy.xtor) : CTy.xtor =
  { CTy.name = xtor.MTy.name
  ; CTy.parameters = List.map (fun (id, k) -> (id, map_kind k)) xtor.MTy.parameters
  ; CTy.existentials = List.map (fun (id, k) -> (id, map_kind k)) xtor.MTy.existentials
  ; CTy.arguments = List.map (fun a -> CTy.Lhs (map_typ a)) xtor.MTy.arguments
  ; CTy.main = map_typ xtor.MTy.main
  }

and map_dtor (xtor: MTy.xtor) : CTy.xtor =
  let lhs_args, rhs_codomain =
    let args, cod = Utility.split_at_last xtor.MTy.arguments in
    (List.map (fun a -> CTy.Lhs (map_typ a)) args, CTy.Rhs (map_typ cod))
  in
  { CTy.name = xtor.MTy.name
  ; CTy.parameters = List.map (fun (id, k) -> (id, map_kind k)) xtor.MTy.parameters
  ; CTy.existentials = List.map (fun (id, k) -> (id, map_kind k)) xtor.MTy.existentials
  ; CTy.arguments = lhs_args @ [rhs_codomain]
  ; CTy.main = map_typ xtor.MTy.main
  }