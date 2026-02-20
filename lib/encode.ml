(**
  module: Encode
  description: Translates from Melcore to Core.
*)

module MB = Melcore.Types.MelcoreBase
module MTy = Melcore.Types.MelcoreTypes
module MTm = Melcore.Terms
module CB = Core.Types.CoreBase
module CTy = Core.Types.CoreTypes
module CTm = Core.Terms

open Common.Identifiers

(* ========================================================================= *)
(* Type Encoding                                                             *)
(* ========================================================================= *)

let rec encode_type (t: MTy.typ) : CTy.typ =
  match t with
    MTy.Base pol -> CTy.Base (match pol with MB.Pos -> CB.Pos | MB.Neg -> CB.Neg)
  | MTy.Arrow (t1, t2) -> CTy.Arrow (encode_type t1, encode_type t2)
  | MTy.Ext e -> CTy.Ext e
  | MTy.TVar v -> CTy.TVar v
  | MTy.TMeta v -> CTy.TMeta v
  | MTy.Sgn (p, args) -> CTy.Sgn (p, List.map encode_type args)
  | MTy.PromotedCtor (d, c, args) -> CTy.PromotedCtor (d, c, List.map encode_type args)
  | MTy.Fun (t1, t2) -> CTy.Fun (encode_type t1, encode_type t2)
  | MTy.Forall (x, k, body) -> CTy.Forall (x, encode_type k, encode_type body)
  | MTy.Raise t' -> CTy.Raise (encode_type t')
  | MTy.Lower t' -> CTy.Lower (encode_type t')

let encode_xtor (pol: MB.polarity) (x: MTy.xtor) : CTy.xtor =
  let encode_xtor_arg i ty =
    if i = 0 && pol = MB.Neg then CB.Cns (encode_type ty) else CB.Prd (encode_type ty)
  in
  { name = x.name
  ; quantified = List.map (fun (v, k) -> (v, encode_type k)) x.quantified
  ; existentials = List.map (fun (v, k) -> (v, encode_type k)) x.existentials
  ; argument_types = List.mapi encode_xtor_arg x.argument_types
  ; main = encode_type x.main
  }

let encode_dec (d: MTy.dec) : CTy.dec =
  { name = d.name
  ; polarity = (match d.polarity with MB.Pos -> CB.Pos | MB.Neg -> CB.Neg)
  ; param_kinds = List.map encode_type d.param_kinds
  ; xtors = List.map (encode_xtor d.polarity) d.xtors
  }

(* ========================================================================= *)
(* Polarity Helpers                                                          *)
(* ========================================================================= *)

(** Get the polarity of an encoded type *)
let polarity_of (decs: CTy.dec Path.tbl) (t: CTy.typ) : CB.polarity option =
  match t with
    CTy.Base p -> Some p
  | CTy.Ext _ -> Some CB.Pos
  | CTy.Sgn (name, _) ->
      (match Path.find_opt name decs with
        Some dec -> Some dec.polarity | None -> None)
  | CTy.Fun (_, _) -> Some CB.Neg
  | CTy.Forall (_, _, _) -> Some CB.Neg
  | CTy.Raise _ -> Some CB.Pos
  | CTy.Lower _ -> Some CB.Neg
  | _ -> None

(* ========================================================================= *)
(* Term Encoding                                                             *)
(* ========================================================================= *)

(** Encoding context *)
type encode_ctx =
  { decs: CTy.dec Path.tbl   (* Type declarations *)
  }

(** Make a cut between a producer and consumer at a given type.
    The type determines whether it's positive or negative. *)
let make_cut (ty: CTy.typ) (lhs: CTm.term) (rhs: CTm.term) : CTm.command =
  CTm.Cut (ty, lhs, rhs)

(** Encode a Melcore typed term into a Core term.
    
    The encoding follows sequent calculus principles:
    - Producers (data) are terms that can be cut against consumers
    - Consumers (codata) are terms that expect data
    
    Key encodings:
    - Int n → Lit n
    - Var x → Var x
    - Lam(x, a, body) → NewFun(a, b, x, k, ⟨body | k⟩)
    - App(f, arg) → μα.⟨f | apply(arg, α)⟩
    - Ctor(d, c, args) → Ctor(d, c, [], args')
    - Match(scrut, branches) → μα.⟨scrut | Match(d, branches')⟩
    - New(branches) → Comatch(d, branches')
*)
let rec encode_term (ctx: encode_ctx) (tm: MTm.typed_term) : CTm.term =
  match tm with
  | MTm.TypedInt n -> CTm.Lit n

  | MTm.TypedVar (x, _ty) -> CTm.Var x

  | MTm.TypedSym (path, ty) ->
      (* Symbol reference - encoded as a call with no args that returns a value *)
      let ty' = encode_type ty in
      let k = Ident.fresh () in
      CTm.MuPrd (ty', k, CTm.Call (path, [], [CTm.Var k]))

  | MTm.TypedAdd (t1, t2) ->
      (* add(m, n) → μα.add(m', n', α) *)
      let t1' = encode_term ctx t1 in
      let t2' = encode_term ctx t2 in
      let alpha = Ident.fresh () in
      CTm.MuPrd (CTy.Ext Common.Types.Int, alpha,
        CTm.Add (t1', t2', CTm.Var alpha))

  | MTm.TypedLam (x, a, body, _ty) ->
      (* λx:a. body → NewFun(a', b', x, k, ⟨body' | k⟩) *)
      let a' = encode_type a in
      let b' = encode_type (MTm.get_type body) in
      let body' = encode_term ctx body in
      let k = Ident.fresh () in
      CTm.NewFun (a', b', x, k, make_cut b' body' (CTm.Var k))

  | MTm.TypedAll ((tv, k), body, _ty) ->
      (* Λa:k. body → NewForall(a, k', ty', ⟨body' | ...⟩) *)
      let k' = encode_type k in
      let body_ty = encode_type (MTm.get_type body) in
      let body' = encode_term ctx body in
      let alpha = Ident.fresh () in
      CTm.NewForall (tv, k', body_ty, make_cut body_ty body' (CTm.Var alpha))

  | MTm.TypedApp (f, arg, ty) ->
      (* f(arg) → μα.⟨f' | apply(arg', α)⟩ *)
      let f' = encode_term ctx f in
      let arg' = encode_term ctx arg in
      let ty' = encode_type ty in
      let f_ty = encode_type (MTm.get_type f) in
      let arg_ty = encode_type (MTm.get_type arg) in
      let alpha = Ident.fresh () in
      CTm.MuPrd (ty', alpha,
        make_cut f_ty f' (CTm.ApplyDtor (arg_ty, ty', arg', CTm.Var alpha)))

  | MTm.TypedIns (f, ty_arg, _k, result_ty) ->
      (* f{ty_arg} → μα.⟨f' | instantiate[ty_arg'](α)⟩ *)
      let f' = encode_term ctx f in
      let ty_arg' = encode_type ty_arg in
      let result_ty' = encode_type result_ty in
      let f_ty = encode_type (MTm.get_type f) in
      let alpha = Ident.fresh () in
      CTm.MuPrd (result_ty', alpha,
        make_cut f_ty f' (CTm.InstantiateDtor ty_arg'))

  | MTm.TypedLet (x, t1, t2, _ty) ->
      (* let x = t1 in t2 → μα.⟨t1' | μ̃x.⟨t2' | α⟩⟩ *)
      let t1' = encode_term ctx t1 in
      let t2' = encode_term ctx t2 in
      let t1_ty = encode_type (MTm.get_type t1) in
      let t2_ty = encode_type (MTm.get_type t2) in
      let alpha = Ident.fresh () in
      CTm.MuPrd (t2_ty, alpha,
        make_cut t1_ty t1'
          (CTm.MuCns (t1_ty, x, make_cut t2_ty t2' (CTm.Var alpha))))

  | MTm.TypedMatch (scrut, branches, ty) ->
      (* match scrut with { ... } → μα.⟨scrut' | Match(d, branches')⟩ *)
      let scrut' = encode_term ctx scrut in
      let scrut_ty = encode_type (MTm.get_type scrut) in
      let ty' = encode_type ty in
      let dec_name = match scrut_ty with
        | CTy.Sgn (d, _) -> d
        | _ -> failwith "Match scrutinee must be data type"
      in
      let branches' = List.map (encode_match_branch ctx ty') branches in
      let alpha = Ident.fresh () in
      CTm.MuPrd (ty', alpha,
        make_cut scrut_ty scrut' (CTm.Match (dec_name, branches')))

  | MTm.TypedNew (branches, ty) ->
      (* new { ... } → Comatch(d, branches') *)
      let ty' = encode_type ty in
      let dec_name = match ty' with
        | CTy.Sgn (d, _) -> d
        | _ -> failwith "New type must be codata type"
      in
      let branches' = List.map (encode_new_branch ctx) branches in
      CTm.Comatch (dec_name, branches')

  | MTm.TypedCtor (dec, ctor, ty_args, args, _ty) ->
      (* Ctor(d, c, {ty_args}, args) → Ctor(d, c, ty_args', args') *)
      let ty_args' = List.map encode_type ty_args in
      let args' = List.map (encode_term ctx) args in
      CTm.Ctor (dec, ctor, ty_args', args')

  | MTm.TypedDtor (dec, dtor, ty_args, args, ty) ->
      (* Dtor(d, c, {ty_args}, this :: rest) → μα.⟨this' | Dtor(d, c, ty_args', rest' @ [α])⟩ *)
      let ty' = encode_type ty in
      let ty_args' = List.map encode_type ty_args in
      (match args with
      | [] -> failwith "Dtor must have at least a subject argument"
      | this_arg :: rest_args ->
          let this' = encode_term ctx this_arg in
          let this_ty = encode_type (MTm.get_type this_arg) in
          let rest' = List.map (encode_term ctx) rest_args in
          let alpha = Ident.fresh () in
          CTm.MuPrd (ty', alpha,
            make_cut this_ty this' (CTm.Dtor (dec, dtor, ty_args', rest' @ [CTm.Var alpha]))))

  | MTm.TypedIfz (cond, then_br, else_br, ty) ->
      (* ifz cond then t else e → μα.ifz(cond', ⟨then' | α⟩, ⟨else' | α⟩) *)
      let cond' = encode_term ctx cond in
      let then' = encode_term ctx then_br in
      let else' = encode_term ctx else_br in
      let ty' = encode_type ty in
      let alpha = Ident.fresh () in
      CTm.MuPrd (ty', alpha,
        CTm.Ifz (cond',
          make_cut ty' then' (CTm.Var alpha),
          make_cut ty' else' (CTm.Var alpha)))

(** Encode a match branch *)
and encode_match_branch (ctx: encode_ctx) (result_ty: CTy.typ)
    ((xtor, ty_vars, tm_vars, body): MTm.typed_clause) : CTm.branch =
  let body' = encode_term ctx body in
  let k = Ident.fresh () in
  (* The branch body cuts against the result continuation *)
  let cmd = make_cut result_ty body' (CTm.Var k) in
  (xtor, ty_vars, tm_vars @ [k], cmd)

(** Encode a new/comatch branch *)
and encode_new_branch (ctx: encode_ctx)
    ((xtor, ty_vars, tm_vars, body): MTm.typed_clause) : CTm.branch =
  let body' = encode_term ctx body in
  let body_ty = encode_type (MTm.get_type body) in
  let k = Ident.fresh () in
  let cmd = make_cut body_ty body' (CTm.Var k) in
  (xtor, ty_vars, tm_vars @ [k], cmd)

(* ========================================================================= *)
(* Definition Encoding                                                       *)
(* ========================================================================= *)

(** Encode a Melcore typed term definition into a Core definition *)
let encode_term_def (ctx: encode_ctx) (def: MTm.typed_term_def) : CTm.definition =
  let body' = encode_term ctx def.body in
  let return_ty = encode_type def.return_type in
  let k = Ident.fresh () in
  { path = def.name
  ; type_params = List.map (fun (v, k) -> (v, encode_type k)) def.type_params
  ; term_params = List.map (fun (v, t) -> (v, CB.Prd (encode_type t))) def.term_params
      @ [(k, CB.Cns return_ty)]  (* Add return continuation *)
  ; body = make_cut return_ty body' (CTm.Var k)
  }