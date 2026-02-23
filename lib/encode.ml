(**
  module: Encode
  description: Translates from Melcore to Core.
  
  This encoding follows the same principles as simple.ml:
  - Fun(a, b) is encoded as Sgn(fun_sym, [dom; cod]) where dom is positive, cod is negative
  - Negative args are wrapped with Raise
  - Positive results are wrapped with Lower
  - Lambda creates a Comatch against the function signature
  - App cuts against a destructor of the function signature
*)

module MB = Melcore.Types.MelcoreBase
module MTy = Melcore.Types.MelcoreTypes
module MTm = Melcore.Terms
module CB = Core.Types.CoreBase
module CTy = Core.Types.CoreTypes
module CTm = Core.Terms

open Common.Identifiers
open Common.Types

(* ========================================================================= *)
(* Type Encoding                                                             *)
(* ========================================================================= *)

(** Encode a Melcore type to a Core type.
    Mostly structural, but maintains the Fun/Raise/Lower/Forall forms
    as Sgn applications. *)
let rec encode_type (t: MTy.typ) : CTy.typ =
  match t with
    MTy.Base pol -> CTy.Base (match pol with MB.Pos -> CB.Pos | MB.Neg -> CB.Neg)
  | MTy.Arrow (t1, t2) -> CTy.Arrow (encode_type t1, encode_type t2)
  | MTy.Ext e -> CTy.Ext e
  | MTy.TVar v -> CTy.TVar v
  | MTy.TMeta v -> CTy.TMeta v
  | MTy.Sgn (p, args) -> CTy.Sgn (p, List.map encode_type args)
  | MTy.PromotedCtor (d, c, args) -> CTy.PromotedCtor (d, c, List.map encode_type args)
  (* Forall is the only true built-in remaining *)
  | MTy.Forall (x, k, body) -> CTy.Forall (x, encode_type k, encode_type body)

(** Encode an xtor definition *)
let encode_xtor (pol: MB.polarity) (x: MTy.xtor) : CTy.xtor =
  let encode_xtor_arg i (ty: MTy.typ) : CTy.chiral_typ =
    (* First argument of Melcore dtor is consumer *)
    if i = 0 && pol = MB.Neg then CB.Cns (encode_type ty) else
      CB.Prd (encode_type ty)  (* All other arguments are producers *)
  in
  { name = x.name
  ; quantified = List.map (fun (v, k) -> (v, encode_type k)) x.quantified
  ; existentials = List.map (fun (v, k) -> (v, encode_type k)) x.existentials
  ; argument_types = List.mapi encode_xtor_arg x.argument_types
  ; main = encode_type x.main
  }

(** Encode a declaration *)
let encode_dec (d: MTy.dec) : CTy.dec =
  { name = d.name
  ; polarity = (match d.polarity with MB.Pos -> CB.Pos | MB.Neg -> CB.Neg)
  ; param_kinds = List.map encode_type d.param_kinds
  ; type_args = List.map encode_type d.type_args
  ; xtors = List.map (encode_xtor d.polarity) d.xtors
  }

(* ========================================================================= *)
(* Polarity Helpers                                                          *)
(* ========================================================================= *)

(** Get the polarity of an encoded type *)
let polarity_of (ctx: CTy.context) (t: CTy.typ) : CB.polarity option =
  match CTy.infer_kind ctx t with Ok (CTy.Base p) -> Some p | _ -> None

(** Check if a type is positive *)
let is_positive (ctx: CTy.context) (t: CTy.typ) : bool =
  polarity_of ctx t = Some CB.Pos

(** Check if a type is negative *)
let is_negative (ctx: CTy.context) (t: CTy.typ) : bool =
  polarity_of ctx t = Some CB.Neg

(* ========================================================================= *)
(* Term Encoding                                                             *)
(* ========================================================================= *)

(** Encoding context *)
type encode_ctx =
  { types: CTy.context   (* Type-level context with declarations *)
  }

(** Get an instantiated declaration for a symbol with given type arguments *)
let get_instantiated_dec (ctx: encode_ctx) (sym: Path.t) (type_args: CTy.typ list) : CTy.dec =
  match Path.find_opt sym ctx.types.decs with
  | Some dec -> CTy.instantiate_dec dec type_args
  | None -> failwith ("Unknown declaration: " ^ Path.name sym)

(** Make a cut between a producer and consumer at a given type *)
let make_cut (ty: CTy.typ) (lhs: CTm.term) (rhs: CTm.term) : CTm.command =
  CTm.Cut (ty, lhs, rhs)

(** Encode a Melcore typed term into a Core term.
    
    The encoding follows sequent calculus principles (like simple.ml):
    - Producers (data) are terms that can be cut against consumers
    - Consumers (codata) are terms that expect data
    
    Key encodings:
    - Int n → Lit n
    - Var x → Var x
    - Lam(x, a, body) → Comatch(fun_sym, [apply{dom,cod}(k, x) => ...])
    - App(f, arg) → μα.⟨f | Dtor(fun_sym, apply, [α, arg])⟩
    - Ctor(d, c, args) → Ctor(d, c, [], args')
    - Match(scrut, branches) → μα.⟨scrut | Match(d, branches')⟩
    - New(branches) → Comatch(d, branches')
*)
let rec encode_term (ctx: encode_ctx) (tm: MTm.typed_term) : CTm.term =
  match tm with
  | MTm.TypedInt n -> CTm.Lit n

  | MTm.TypedVar (x, _ty) -> CTm.Var x

  | MTm.TypedSym (path, ty) ->
      (* Symbol reference - encoded as a call that returns a value *)
      let ty' = encode_type ty in
      let k = Ident.fresh () in
      CTm.MuPrd (ty', k, CTm.Call (path, [], [CTm.Var k]))

  | MTm.TypedAdd (t1, t2) ->
      (* add(m, n) → μα.add(m', n', α) *)
      let t1' = encode_term ctx t1 in
      let t2' = encode_term ctx t2 in
      let alpha = Ident.fresh () in
      CTm.MuPrd (CTy.Ext Int, alpha,
        CTm.Add (t1', t2', CTm.Var alpha))

  | MTm.TypedLam (x, _a, body, fun_ty) ->
      (* λx:a. body → Comatch(fun_sym, [apply{dom,cod}(k, x) => ⟨body' | k⟩])
         
         The internal function type is Sgn(fun_sym, [dom; cod]) where:
         - dom is positive (negative args wrapped with Raise)
         - cod is negative (positive results wrapped with Lower)
         
         The apply destructor has arguments: [Cns cod; Prd dom]
         So we bind: k: Cns cod, x': Prd dom *)
      let (dom, cod) = match fun_ty with
        | MTy.Sgn (s, [d; c]) when Path.equal s Prim.fun_sym -> 
            (encode_type d, encode_type c)
        | _ -> failwith "TypedLam must have Fun type"
      in
      let body' = encode_term ctx body in
      let body_ty = encode_type (MTm.get_type body) in
      let k = Ident.fresh () in
      let x' = Ident.fresh () in
      (* If dom = Raise(orig_dom), we need to unwrap x' to get the actual x *)
      let inner_cmd = match dom with
        | CTy.Sgn (s, [orig_dom]) when Path.equal s Prim.raise_sym ->
            (* x' : Prd Raise(orig_dom), need to match to extract x : orig_dom *)
            let raise_dec = get_instantiated_dec ctx Prim.raise_sym [orig_dom] in
            make_cut dom (CTm.Var x')
              (CTm.Match (raise_dec,
                [(Prim.thunk_sym, [], [x], 
                  (* Now we have x : orig_dom. Cut body against k. *)
                  wrap_body_for_cod ctx body' body_ty cod k)]))
        | _ ->
            (* No unwrapping needed, x' is directly usable as x *)
            (* But we need to rebind x' as x in the body... 
               Actually, we'll just use x directly *)
            wrap_body_for_cod ctx body' body_ty cod k
      in
      (* For the non-raised case, the branch variable should be x, not x' *)
      let branch_x = match dom with
        | CTy.Sgn (s, [_]) when Path.equal s Prim.raise_sym -> x'
        | _ -> x
      in
      let fun_dec = get_instantiated_dec ctx Prim.fun_sym [dom; cod] in
      (* Branch vars: [k; x] matching apply_xtor.argument_types = [Cns b; Prd a] *)
      CTm.Comatch (fun_dec,
        [(Prim.apply_sym, [], [k; branch_x], inner_cmd)])

  | MTm.TypedAll ((tv, k), body, ty) ->
      (* Λa:k. body → NewForall(a, k', body_ty', ⟨body' | α⟩) *)
      let k' = encode_type k in
      let body_ty' = match ty with
        | MTy.Forall (_, _, inner) -> encode_type inner
        | _ -> failwith "TypedAll must have Forall type"
      in
      let body' = encode_term ctx body in
      let alpha = Ident.fresh () in
      CTm.NewForall (tv, k', body_ty', make_cut body_ty' body' (CTm.Var alpha))

  | MTm.TypedApp (f, arg, result_ty) ->
      (* Beta-reduce if f is a lambda: (λx. body) arg → body[arg/x] *)
      (match f with
      | MTm.TypedLam (x, _a, body, _fun_ty) ->
          let reduced = MTm.subst_term_in_typed_term x arg body in
          encode_term ctx reduced
      (* Handle (Λa. body){ty_arg} arg - first instantiate, then apply *)
      | MTm.TypedIns (MTm.TypedAll ((tv, _k'), body, _forall_ty), ty_arg, _, _) ->
          let sbs = Ident.add tv ty_arg Ident.emptytbl in
          let inst_body = MTm.subst_type_in_typed_term sbs body in
          (* Recursively encode the application - this may trigger lambda beta-reduction *)
          encode_term ctx (MTm.TypedApp (inst_body, arg, result_ty))
      | _ ->
          (* f(arg) → μα.⟨f' | Dtor(fun_sym, apply, [α, arg'])⟩
             
             The apply destructor expects: [Cns cod; Prd dom]
             So we pass: [α (consumer for result); arg' (producer)] 
             
             If cod = Lower(result_ty'), the function returns a suspended computation.
             We need to force it: receive the Lower value, call return, get the Int. *)
          let f' = encode_term ctx f in
          let arg' = encode_term ctx arg in
          let f_ty = encode_type (MTm.get_type f) in
          let result_ty' = encode_type result_ty in
          let (dom, cod) = match f_ty with
            | CTy.Sgn (s, [d; c]) when Path.equal s Prim.fun_sym -> (d, c)
            | _ -> failwith "TypedApp: f must have function type"
          in
          (* Wrap arg if dom is Raise *)
          let wrapped_arg = match dom with
            | CTy.Sgn (s, [orig_dom]) when Path.equal s Prim.raise_sym ->
                let raise_dec = get_instantiated_dec ctx Prim.raise_sym [orig_dom] in
                CTm.Ctor (raise_dec, Prim.thunk_sym, [arg'])
            | _ -> arg'
          in
          let fun_dec = get_instantiated_dec ctx Prim.fun_sym [dom; cod] in
          (match cod with
          | CTy.Sgn (s, [inner_ty]) when Path.equal s Prim.lower_sym ->
              (* cod = Lower(inner_ty), function returns suspended computation.
                 
                 We receive a Lower value and force it:
                 μret.⟨f | apply(μ̃thunk.⟨thunk | return(ret)⟩, arg)⟩
                 
                 - MuPrd at result_ty' (= inner_ty) binds ret to receive the Int
                 - MuCns at cod binds thunk to receive the Lower value  
                 - Inner cut forces: ⟨thunk | return(ret)⟩
                 - When return is called on thunk, we get the Int, which goes to ret *)
              let lower_dec = get_instantiated_dec ctx Prim.lower_sym [inner_ty] in
              let thunk = Ident.fresh () in
              let ret = Ident.fresh () in
              (* MuCns receives the Lower value, forces it, sends Int to ret *)
              let force_cmd = make_cut cod (CTm.Var thunk)
                (CTm.Dtor (lower_dec, Prim.return_sym, [CTm.Var ret])) in
              let force_continuation = CTm.MuCns (cod, thunk, force_cmd) in
              CTm.MuPrd (result_ty', ret,
                make_cut f_ty f'
                  (CTm.Dtor (fun_dec, Prim.apply_sym,
                    [force_continuation; wrapped_arg])))
          | _ ->
              (* cod is already the result type, no forcing needed *)
              let alpha = Ident.fresh () in
              CTm.MuPrd (result_ty', alpha,
                make_cut f_ty f'
                  (CTm.Dtor (fun_dec, Prim.apply_sym,
                    [CTm.Var alpha; wrapped_arg])))))

  | MTm.TypedIns (f, ty_arg, _k, result_ty) ->
      (* Instantiate if f is a TypedAll: (Λa. body){ty_arg} → body[ty_arg/a] *)
      (match f with
      | MTm.TypedAll ((tv, _k'), body, _forall_ty) ->
          let sbs = Ident.add tv ty_arg Ident.emptytbl in
          let reduced = MTm.subst_type_in_typed_term sbs body in
          encode_term ctx reduced
      (* Handle ((λx. body) arg){ty_arg} - first beta-reduce, then instantiate *)
      | MTm.TypedApp (MTm.TypedLam (x, _a, lam_body, _fun_ty), arg, _app_ty) ->
          let reduced = MTm.subst_term_in_typed_term x arg lam_body in
          (* Recursively encode the instantiation - this may trigger forall instantiation *)
          encode_term ctx (MTm.TypedIns (reduced, ty_arg, _k, result_ty))
      | _ ->
          (* f{ty_arg} → μα.⟨f' | instantiate[ty_arg'](α)⟩ *)
          let f' = encode_term ctx f in
          let ty_arg' = encode_type ty_arg in
          let result_ty' = encode_type result_ty in
          let f_ty = encode_type (MTm.get_type f) in
          let alpha = Ident.fresh () in
          CTm.MuPrd (result_ty', alpha,
            make_cut f_ty f' (CTm.InstantiateDtor ty_arg')))

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
      let (dec_name, type_args) = match scrut_ty with
        | CTy.Sgn (d, args) -> (d, args)
        | _ -> failwith "Match scrutinee must be data type"
      in
      let inst_dec = get_instantiated_dec ctx dec_name type_args in
      let branches' = List.map (encode_match_branch ctx ty') branches in
      let alpha = Ident.fresh () in
      CTm.MuPrd (ty', alpha,
        make_cut scrut_ty scrut' (CTm.Match (inst_dec, branches')))

  | MTm.TypedNew (branches, ty) ->
      (* new { ... } → Comatch(d, branches') *)
      let ty' = encode_type ty in
      let (dec_name, type_args) = match ty' with
        | CTy.Sgn (d, args) -> (d, args)
        | _ -> failwith "New type must be codata type"
      in
      let inst_dec = get_instantiated_dec ctx dec_name type_args in
      let branches' = List.map (encode_new_branch ctx) branches in
      CTm.Comatch (inst_dec, branches')

  | MTm.TypedCtor (dec, ctor, ty_args, args, _ty) ->
      (* Ctor(d, c, {ty_args}, args) → Ctor(inst_dec, c, args') *)
      let ty_args' = List.map encode_type ty_args in
      let args' = List.map (encode_term ctx) args in
      let inst_dec = get_instantiated_dec ctx dec ty_args' in
      CTm.Ctor (inst_dec, ctor, args')

  | MTm.TypedDtor (dec, dtor, ty_args, args, ty) ->
      (* Dtor(d, c, {ty_args}, this :: rest) → μα.⟨this' | Dtor(inst_dec, c, rest' @ [α])⟩ *)
      let ty' = encode_type ty in
      let ty_args' = List.map encode_type ty_args in
      let inst_dec = get_instantiated_dec ctx dec ty_args' in
      (match args with
      | [] -> failwith "Dtor must have at least a subject argument"
      | this_arg :: rest_args ->
          let this' = encode_term ctx this_arg in
          let this_ty = encode_type (MTm.get_type this_arg) in
          let rest' = List.map (encode_term ctx) rest_args in
          let alpha = Ident.fresh () in
          CTm.MuPrd (ty', alpha,
            make_cut this_ty this' (CTm.Dtor (inst_dec, dtor, rest' @ [CTm.Var alpha]))))

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

(** Helper: wrap body and cut against k, handling Lower codomain *)
and wrap_body_for_cod (ctx: encode_ctx) (body: CTm.term) (body_ty: CTy.typ) 
    (cod: CTy.typ) (k: Ident.t) : CTm.command =
  match cod with
  | CTy.Sgn (s, [_inner_ty]) when Path.equal s Prim.lower_sym ->
      (* cod = Lower(inner_ty), k : Cns Lower(inner_ty)
         body produces body_ty (= inner_ty)
         We need to produce a Lower value: Comatch { return(r) => Cut(body, r) }
         Then cut: ⟨Comatch{...} | k⟩
         
         The r parameter is where the caller wants the result sent.
         So we just cut body against r - the result goes where caller requested. *)
      let lower_dec = get_instantiated_dec ctx Prim.lower_sym [body_ty] in
      let r = Ident.fresh () in
      make_cut cod
        (CTm.Comatch (lower_dec,
          [(Prim.return_sym, [], [r], 
            CTm.Cut (body_ty, body, CTm.Var r))]))
        (CTm.Var k)
  | _ ->
      (* cod = body_ty, no wrapping needed *)
      make_cut body_ty body (CTm.Var k)

(** Encode a match branch - bind result continuation k *)
and encode_match_branch (ctx: encode_ctx) (result_ty: CTy.typ)
    ((xtor, ty_vars, tm_vars, body): MTm.typed_clause) : CTm.branch =
  let body' = encode_term ctx body in
  let k = Ident.fresh () in
  let cmd = make_cut result_ty body' (CTm.Var k) in
  (xtor, ty_vars, tm_vars @ [k], cmd)

(** Encode a new/comatch branch - bind result continuation k *)
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