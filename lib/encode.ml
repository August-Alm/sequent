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

let get_data_sort (sorts: data_sort Path.tbl) (s: Path.t) : data_sort =
  match Path.find_opt s sorts with
    Some data_sort -> data_sort
  | None -> failwith ("Unknown declaration: " ^ Path.name s)

let raise (ty: CTy.typ) : CTy.typ =
  CTy.Sgn (Prim.raise_sym, [ty])
let lower (ty: CTy.typ) : CTy.typ =
  CTy.Sgn (Prim.lower_sym, [ty])

(** Encode a Melcore type to a Core type *)
let rec encode_type (sorts: data_sort Path.tbl) (t: MTy.typ) : CTy.typ =
  match t with
    MTy.Base Typ -> CTy.Base CB.Pos
  | MTy.Arrow (t1, t2) -> CTy.Arrow (encode_type sorts t1, encode_type sorts t2)
  | MTy.Ext e -> CTy.Ext e
  | MTy.TVar v -> CTy.TVar v
  | MTy.TMeta v -> CTy.TMeta v
  | MTy.Sgn (p, args) ->
      (match get_data_sort sorts p with
        Data -> CTy.Sgn (p, List.map (encode_type sorts) args)
      | Codata -> raise (CTy.Sgn (p, List.map (encode_type sorts) args)))
  | MTy.PromotedCtor (d, c, args) ->
      CTy.PromotedCtor (d, c, List.map (encode_type sorts) args)
  | MTy.Forall (x, k, body) ->
      (* Forall is codata/negative, so wrap result in raise.
         Body type is positive (like all types now), keep it as-is.
         The forall itself works with positive body types. *)
      raise (CTy.Forall (x, encode_type sorts k, encode_type sorts body))

(** Encode an xtor definition *)
let encode_xtor (sorts: data_sort Path.tbl) (ds: data_sort) (x: MTy.xtor) : CTy.xtor =
  let encode_xtor_arg i (ty: MTy.typ) : CTy.chiral_typ =
    (* First argument of Melcore dtor is consumer *)
    if i = 0 && ds = Codata then CB.Cns (encode_type sorts ty) else
      CB.Prd (encode_type sorts ty)  (* All other arguments are producers *)
  in
  (* For codata, the xtor.main is the "internal" type used in cuts after unwrapping.
     It should NOT be wrapped in raise - that wrapping happens at use sites.
     For data, encode_type doesn't wrap anyway. *)
  let encode_main (ty: MTy.typ) : CTy.typ =
    match ty with
    | MTy.Sgn (p, args) when get_data_sort sorts p = Codata ->
        (* Don't wrap codata types in raise for xtor.main *)
        CTy.Sgn (p, List.map (encode_type sorts) args)
    | _ -> encode_type sorts ty
  in
  { name = x.name
  ; quantified = List.map (fun (v, k) -> (v, encode_type sorts k)) x.quantified
  ; existentials = List.map (fun (v, k) -> (v, encode_type sorts k)) x.existentials
  ; argument_types = List.mapi encode_xtor_arg x.argument_types
  ; main = encode_main x.main
  }

(** Encode a declaration *)
let encode_dec (sorts: data_sort Path.tbl) (d: MTy.dec) : CTy.dec =
  { name = d.name
  ; data_sort = d.data_sort
  ; param_kinds = List.map (encode_type sorts) d.param_kinds
  ; type_args = List.map (encode_type sorts) d.type_args
  ; xtors = List.map (encode_xtor sorts d.data_sort) d.xtors
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
  ; data_sorts: data_sort Path.tbl  (* Map from type names to data/codata sort *)
  ; defs: MTm.typed_term_def Path.tbl  (* Definitions for direct call optimization *)
  }

(** Build an encoding context from Melcore type declarations *)
let make_encode_ctx ?(defs=Path.emptytbl) (melcore_decs: MTy.dec list) : encode_ctx =
  let empty_sorts =
    MTy.empty_context.decs
    |> Path.to_list
    |> List.map (fun (p, d) -> (p, d.MTy.data_sort))
    |> Path.of_list
  in
  let sorts = List.fold_left (fun tbl (dec: MTy.dec) ->
    Path.add dec.name dec.data_sort tbl
  ) empty_sorts melcore_decs in
  let core_decs = List.map (encode_dec sorts) melcore_decs in
  let types = List.fold_left CTy.add_dec CTy.empty_context core_decs in
  { types = types; data_sorts = sorts; defs = defs }

(** Get an instantiated declaration for a symbol with given type arguments *)
let get_instantiated_dec (ctx: encode_ctx) (sym: Path.t) (type_args: CTy.typ list) : CTy.dec =
  match Path.find_opt sym ctx.types.decs with
    Some dec -> CTy.instantiate_dec dec type_args
  | None -> failwith ("Unknown declaration: " ^ Path.name sym)

(** Make a cut between a producer and consumer at a given type *)
let make_cut (ty: CTy.typ) (lhs: CTm.term) (rhs: CTm.term) : CTm.command =
  CTm.Cut (ty, lhs, rhs)

(** Collect application spine: f(x)(y)(z) → (f, [x; y; z], result_ty)
    Also collects type instantiations: f{A}(x) → (f, [A], [x], result_ty) *)
let rec collect_app_spine (tm: MTm.typed_term) 
    : MTm.typed_term * MTy.typ list * MTm.typed_term list * MTy.typ =
  match tm with
  | MTm.TypedApp (f, arg, result_ty) ->
      let (head, ty_args, term_args, _) = collect_app_spine f in
      (head, ty_args, term_args @ [arg], result_ty)
  | MTm.TypedIns (f, ty_arg, _k, result_ty) ->
      let (head, ty_args, term_args, _) = collect_app_spine f in
      (head, ty_args @ [ty_arg], term_args, result_ty)
  | _ -> (tm, [], [], MTm.get_type tm)

(** Check if a term is a definition reference that should be called directly *)
let is_def_call (ctx: encode_ctx) (tm: MTm.typed_term) : Path.t option =
  match tm with
  | MTm.TypedSym (path, _) ->
      (match Path.find_opt path ctx.defs with
       | Some def when def.MTm.term_params <> [] -> Some path
       | _ -> None)
  | _ -> None

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
    
    Saturated calls to definitions in TAIL position are encoded as direct Call commands.
*)

(** Eta-expand a partial application of a definition into a first-class value.
    
    For a definition like:
      def id{a}(x: a): a = x
    
    When used without arguments (as `id`), we create:
      thunk(NewForall(a, +, fun(a,a), 
        ⟨Comatch fun(a,a) { apply(k, x) => call id{a}(x, k) } | α⟩))
    
    This is crucial for flow analysis: the resulting forall value contains
    a Call to the original definition, so instantiation flows propagate
    correctly for higher-rank polymorphism. *)
let rec encode_partial_application 
    (ctx: encode_ctx) (path: Path.t) (ty: MTy.typ) (def: MTm.typed_term_def) 
    : CTm.term =
  match ty with
  | MTy.Forall (tv, k, body_ty) ->
      let k' = encode_type ctx.data_sorts k in
      let body_ty' = encode_type ctx.data_sorts body_ty in
      
      (* Recursively encode the body type - this will eventually hit the function case *)
      let inner = encode_partial_application ctx path body_ty def in
      
      let alpha = Ident.fresh () in
      let inner_forall_ty = CTy.Forall (tv, k', body_ty') in
      (* alpha is now bound by NewForall as the continuation *)
      let new_forall = CTm.NewForall (tv, k', body_ty', alpha,
        make_cut body_ty' inner (CTm.Var alpha)) in
      
      (* Wrap in thunk to produce raise(∀...) *)
      let raise_dec = get_instantiated_dec ctx Prim.raise_sym [inner_forall_ty] in
      CTm.Ctor (raise_dec, Prim.thunk_sym, [new_forall])
      
  | MTy.Sgn (sym, [dom; cod]) when sym = Common.Types.Prim.fun_sym ->
      
      let dom' = encode_type ctx.data_sorts dom in
      let cod' = encode_type ctx.data_sorts cod in
      let inner_fun_ty = CTy.Sgn (Prim.fun_sym, [dom'; cod']) in
      
      let k = Ident.fresh () in
      let x = Ident.fresh () in
      
      (* Collect type args from the definition's type params *)
      let ty_args = List.map (fun (v, _) -> CTy.TVar v) def.type_params in
      
      (* Create the call: call path{ty_args}(x, k) *)
      let call_cmd = CTm.Call (path, ty_args, [CTm.Var x; CTm.Var k]) in
      
      let fun_dec = get_instantiated_dec ctx Prim.fun_sym [dom'; cod'] in
      let comatch = CTm.Comatch (fun_dec,
        [(Prim.apply_sym, [], [k; x], call_cmd)]) in
      
      (* Wrap in thunk to produce raise(fun(...)) *)
      let raise_dec = get_instantiated_dec ctx Prim.raise_sym [inner_fun_ty] in
      CTm.Ctor (raise_dec, Prim.thunk_sym, [comatch])
      
  | _ ->
      (* Shouldn't happen for well-typed partial applications *)
      failwith (Printf.sprintf 
        "encode_partial_application: unexpected type %s for %s"
        (Melcore.Printing.typ_to_string ty) (Path.name path))

and encode_term (ctx: encode_ctx) (tm: MTm.typed_term) : CTm.term =
  (* Non-tail position: use standard encoding *)
  encode_term_inner ctx tm

(** Encode a term in tail position - this is where we check for direct calls.
    A saturated call to a definition in tail position becomes a Jump/Call. *)
and encode_term_tail (ctx: encode_ctx) (tm: MTm.typed_term) : CTm.term =
  (* Check if this is a saturated call to a definition in tail position *)
  let (head, ty_args, term_args, result_ty) = collect_app_spine tm in
  match is_def_call ctx head with
  | Some path when term_args <> [] ->
      (* Direct definition call in tail position: f(x)(y) → μk.Call(f, ty_args, [x', y', k]) *)
      let def = Path.find path ctx.defs in
      let expected_term_arity = List.length def.MTm.term_params in
      let actual_term_arity = List.length term_args in
      if actual_term_arity = expected_term_arity then
        (* Fully saturated call - encode arguments recursively (not in tail position) *)
        let ty_args' = List.map (encode_type ctx.data_sorts) ty_args in
        let term_args' = List.map (encode_term ctx) term_args in
        let result_ty' = encode_type ctx.data_sorts result_ty in
        let k = Ident.fresh () in
        CTm.MuPrd (result_ty', k, 
          CTm.Call (path, ty_args', term_args' @ [CTm.Var k]))
      else
        (* Partial application - use standard encoding *)
        encode_term_inner ctx tm
  | _ ->
      encode_term_inner ctx tm

(* Helper to check if a term is a saturated definition call and encode it *)
and try_encode_def_call (ctx: encode_ctx) (tm: MTm.typed_term) : CTm.term option =
  let (head, ty_args, term_args, result_ty) = collect_app_spine tm in
  match is_def_call ctx head with
  | Some path when term_args <> [] ->
      let def = Path.find path ctx.defs in
      let expected_term_arity = List.length def.MTm.term_params in
      let actual_term_arity = List.length term_args in
      if actual_term_arity = expected_term_arity then
        (* Saturated definition call: f(x)(y) → μk.Call(f, ty_args, [x', y', k]) *)
        let ty_args' = List.map (encode_type ctx.data_sorts) ty_args in
        let term_args' = List.map (encode_term ctx) term_args in
        let result_ty' = encode_type ctx.data_sorts result_ty in
        let k = Ident.fresh () in
        Some (CTm.MuPrd (result_ty', k, 
          CTm.Call (path, ty_args', term_args' @ [CTm.Var k])))
      else
        None
  | _ -> None

and encode_term_inner (ctx: encode_ctx) (tm: MTm.typed_term) : CTm.term =
  (* First check if this is a saturated definition call *)
  match try_encode_def_call ctx tm with
  | Some encoded -> encoded
  | None ->
  match tm with
    MTm.TypedInt n -> CTm.Lit n

  | MTm.TypedVar (x, _ty) -> CTm.Var x

  | MTm.TypedSym (path, ty) ->
      (match Path.find_opt path ctx.defs with
       | Some def when def.MTm.term_params = [] ->
           (* Nullary definition: call it and get the value *)
           let ty' = encode_type ctx.data_sorts ty in
           let k = Ident.fresh () in
           CTm.MuPrd (ty', k, CTm.Call (path, [], [CTm.Var k]))
       | Some def ->
           encode_partial_application ctx path ty def
       | None ->
           (* Not a definition - could be a constructor or external symbol *)
           let ty' = encode_type ctx.data_sorts ty in
           let k = Ident.fresh () in
           CTm.MuPrd (ty', k, CTm.Call (path, [], [CTm.Var k])))

  | MTm.TypedAdd (t1, t2) ->
      (* add(m, n) → μα.add(m', n', α) *)
      let t1' = encode_term ctx t1 in
      let t2' = encode_term ctx t2 in
      let alpha = Ident.fresh () in
      CTm.MuPrd (CTy.Ext Int, alpha,
        CTm.Add (t1', t2', CTm.Var alpha))

  | MTm.TypedSub (t1, t2) ->
      (* sub(m, n) → μα.sub(m', n', α) *)
      let t1' = encode_term ctx t1 in
      let t2' = encode_term ctx t2 in
      let alpha = Ident.fresh () in
      CTm.MuPrd (CTy.Ext Int, alpha,
        CTm.Sub (t1', t2', CTm.Var alpha))

  | MTm.TypedLam (x, _a, body, fun_ty) ->
      (* λx:a. body → thunk(Comatch(fun_sym, [apply{dom,cod}(k, x) => ⟨body' | k⟩]))
         
         Since all Melcore types are positive in Core, a function type fun(a,b)
         is encoded as raise(fun(a',b')). The lambda produces a comatch (negative),
         which we wrap in thunk to make it positive.
         
         The apply destructor has arguments: [Cns cod; Prd dom]
         So we bind: k: Cns cod, x: Prd dom
         
         Note: We do NOT unwrap raise here. The body encoding will handle
         unwrapping when x is used (e.g., in application). This ensures
         consistency between the bound variable type and how the body sees it. *)
      let (dom, cod) = match fun_ty with
        | MTy.Sgn (s, [d; c]) when Path.equal s Prim.fun_sym -> 
            (encode_type ctx.data_sorts d, encode_type ctx.data_sorts c)
        | _ -> failwith "TypedLam must have Fun type"
      in
      let body' = encode_term ctx body in
      let body_ty = encode_type ctx.data_sorts (MTm.get_type body) in
      let k = Ident.fresh () in
      let inner_cmd = wrap_body_for_cod ctx body' body_ty cod k in
      let inner_fun_ty = CTy.Sgn (Prim.fun_sym, [dom; cod]) in
      let fun_dec = get_instantiated_dec ctx Prim.fun_sym [dom; cod] in
      let comatch = CTm.Comatch (fun_dec,
        [(Prim.apply_sym, [], [k; x], inner_cmd)]) in
      (* Wrap in thunk to produce raise(fun(...)) *)
      let raise_dec = get_instantiated_dec ctx Prim.raise_sym [inner_fun_ty] in
      CTm.Ctor (raise_dec, Prim.thunk_sym, [comatch])

  | MTm.TypedAll ((tv, k), body, ty) ->
      (* Λa:k. body → thunk(NewForall(a, k', alpha, ⟨body' | alpha⟩))
         
         Forall types are encoded as raise(∀a:k. body_ty).
         The NewForall binds both the type variable and the continuation.
         
         The NewForall body produces body_ty', and the continuation α
         (now bound by NewForall) receives that value. When instantiated, 
         the body runs and the result flows to the instantiation continuation.
         
         NewForall is negative, so wrap in thunk. *)
      let k' = encode_type ctx.data_sorts k in
      let body_ty' = match ty with
          MTy.Forall (_, _, inner) -> encode_type ctx.data_sorts inner
        | _ -> failwith "TypedAll must have Forall type"
      in
      let body' = encode_term ctx body in
      let alpha = Ident.fresh () in
      (* Use body_ty' as the forall body type *)
      let inner_forall_ty = CTy.Forall (tv, k', body_ty') in
      (* alpha is now bound by NewForall as the continuation *)
      let new_forall = CTm.NewForall (tv, k', body_ty', alpha, make_cut body_ty' body' (CTm.Var alpha)) in
      (* Wrap in thunk to produce raise(∀...) *)
      let raise_dec = get_instantiated_dec ctx Prim.raise_sym [inner_forall_ty] in
      CTm.Ctor (raise_dec, Prim.thunk_sym, [new_forall])

  | MTm.TypedApp (f, arg, result_ty) ->
      (* f(arg) where f : raise(fun(dom, cod))
         
         Note: Saturated definition calls are already handled by try_encode_def_call
         at the start of encode_term_inner. This case handles regular function application.
         
         Since function types are encoded as raise(fun(...)), we need to:
         1. Unwrap the raise to get the actual function
         2. Apply it
         
         μα.⟨f' | match { thunk(g) => ⟨g | apply(α, arg')⟩ }⟩ *)
      let f' = encode_term ctx f in
      let arg' = encode_term ctx arg in
      let f_ty = encode_type ctx.data_sorts (MTm.get_type f) in
      let result_ty' = encode_type ctx.data_sorts result_ty in
      
      (* f_ty should be raise(fun(dom, cod)) *)
      let (inner_fun_ty, dom, cod) = match f_ty with
          CTy.Sgn (s, [CTy.Sgn (fun_s, [d; c])]) 
            when Path.equal s Prim.raise_sym && Path.equal fun_s Prim.fun_sym ->
            (CTy.Sgn (Prim.fun_sym, [d; c]), d, c)
        | CTy.Sgn (fun_s, [d; c]) when Path.equal fun_s Prim.fun_sym ->
            (* Fallback: f_ty is already fun(dom, cod) - shouldn't happen but handle it *)
            (f_ty, d, c)
        | _ -> failwith "TypedApp: f must have function type"
      in
      
      (* Wrap arg if dom is Raise *)
      let wrapped_arg = match dom with
          CTy.Sgn (s, [orig_dom]) when Path.equal s Prim.raise_sym ->
            let raise_dec = get_instantiated_dec ctx Prim.raise_sym [orig_dom] in
            CTm.Ctor (raise_dec, Prim.thunk_sym, [arg'])
        | _ -> arg'
      in
      
      let fun_dec = get_instantiated_dec ctx Prim.fun_sym [dom; cod] in
      let raise_dec = get_instantiated_dec ctx Prim.raise_sym [inner_fun_ty] in
      let g = Ident.fresh () in
      
      (* Build the application command *)
      let build_app_cmd (result_cont: CTm.term) : CTm.command =
        make_cut inner_fun_ty (CTm.Var g)
          (CTm.Dtor (fun_dec, Prim.apply_sym, [], [result_cont; wrapped_arg]))
      in
      
      (match cod with
        CTy.Sgn (s, [inner_ty]) when Path.equal s Prim.lower_sym ->
          (* cod = Lower(inner_ty), function returns suspended computation.
             Need to force it. *)
          let lower_dec = get_instantiated_dec ctx Prim.lower_sym [inner_ty] in
          let thunk = Ident.fresh () in
          let ret = Ident.fresh () in
          let force_cmd = make_cut cod (CTm.Var thunk)
            (CTm.Dtor (lower_dec, Prim.return_sym, [], [CTm.Var ret])) in
          let force_continuation = CTm.MuCns (cod, thunk, force_cmd) in
          CTm.MuPrd (result_ty', ret,
            make_cut f_ty f'
              (CTm.Match (raise_dec,
                [(Prim.thunk_sym, [], [g], build_app_cmd force_continuation)])))
      | _ ->
          (* cod is already the result type *)
          let alpha = Ident.fresh () in
          CTm.MuPrd (result_ty', alpha,
            make_cut f_ty f'
              (CTm.Match (raise_dec,
                [(Prim.thunk_sym, [], [g], build_app_cmd (CTm.Var alpha))]))))

  | MTm.TypedIns (f, ty_arg, _k, result_ty) ->
      (* f{ty_arg} where f : raise(∀a:k. body)
         
         Since forall types are encoded as raise(∀...), we need to:
         1. Unwrap the raise to get the actual forall
         2. Instantiate it to get body[a:=ty_arg]
         
         μα.⟨f' | match { thunk(g) => ⟨g | instantiate[ty_arg']⟩ }⟩ 
         
         Note: We removed the lower wrapping, so result_ty' is directly the result. *)
      let f' = encode_term ctx f in
      let ty_arg' = encode_type ctx.data_sorts ty_arg in
      let result_ty' = encode_type ctx.data_sorts result_ty in
      let f_ty = encode_type ctx.data_sorts (MTm.get_type f) in
      
      (* f_ty should be raise(∀a:k. body) *)
      let inner_forall_ty = match f_ty with
          CTy.Sgn (s, [inner]) when Path.equal s Prim.raise_sym -> inner
        | _ -> failwith "TypedIns: f must have forall type (wrapped in raise)"
      in
      
      let raise_dec = get_instantiated_dec ctx Prim.raise_sym [inner_forall_ty] in
      let g = Ident.fresh () in
      let alpha = Ident.fresh () in
      
      CTm.MuPrd (result_ty', alpha,
        make_cut f_ty f'
          (CTm.Match (raise_dec,
            [(Prim.thunk_sym, [], [g],
              make_cut inner_forall_ty (CTm.Var g) (CTm.InstantiateDtor ty_arg'))])))

  | MTm.TypedLet (x, t1, t2, _ty) ->
      (* let x = t1 in t2 → μα.⟨t1' | μ̃x.⟨t2' | α⟩⟩ *)
      let t1' = encode_term ctx t1 in
      let t2' = encode_term_tail ctx t2 in  (* t2 is in tail position *)
      let t1_ty = encode_type ctx.data_sorts (MTm.get_type t1) in
      let t2_ty = encode_type ctx.data_sorts (MTm.get_type t2) in
      let alpha = Ident.fresh () in
      CTm.MuPrd (t2_ty, alpha,
        make_cut t1_ty t1'
          (CTm.MuCns (t1_ty, x, make_cut t2_ty t2' (CTm.Var alpha))))

  | MTm.TypedMatch (scrut, branches, ty) ->
      (* match scrut with { ... } → μα.⟨scrut' | Match(d, branches')⟩ *)
      let scrut' = encode_term ctx scrut in
      let scrut_ty = encode_type ctx.data_sorts (MTm.get_type scrut) in
      let ty' = encode_type ctx.data_sorts ty in
      let (dec_name, type_args) = match scrut_ty with
          CTy.Sgn (d, args) -> (d, args)
        | _ -> failwith "Match scrutinee must be data type"
      in
      let inst_dec = get_instantiated_dec ctx dec_name type_args in
      let alpha = Ident.fresh () in
      let branches' = List.map (encode_match_branch ctx inst_dec ty' alpha) branches in
      CTm.MuPrd (ty', alpha,
        make_cut scrut_ty scrut' (CTm.Match (inst_dec, branches')))

  | MTm.TypedNew (branches, ty) ->
      (* new { ... } → thunk(Comatch(d, branches'))
         
         Since codata types are encoded as raise(codata), we wrap the comatch
         in thunk to produce a positive value. *)
      let ty' = encode_type ctx.data_sorts ty in
      (* ty' is raise(inner_codata_ty) *)
      let inner_codata_ty = match ty' with
          CTy.Sgn (s, [inner]) when Path.equal s Prim.raise_sym -> inner
        | _ -> failwith "New type must be codata type (wrapped in raise)"
      in
      let (dec_name, type_args) = match inner_codata_ty with
          CTy.Sgn (d, args) -> (d, args)
        | _ -> failwith "New type must be codata type"
      in
      let inst_dec = get_instantiated_dec ctx dec_name type_args in
      let branches' = List.map (encode_new_branch ctx inst_dec) branches in
      let comatch = CTm.Comatch (inst_dec, branches') in
      (* Wrap in thunk *)
      let raise_dec = get_instantiated_dec ctx Prim.raise_sym [inner_codata_ty] in
      CTm.Ctor (raise_dec, Prim.thunk_sym, [comatch])

  | MTm.TypedCtor (dec, ctor, ty_args, args, _ty) ->
      (* Ctor(d, c, {ty_args}, args) → Ctor(inst_dec, c, args')
         ty_args contains BOTH dec params AND xtor existentials.
         We need to split them: only dec params go to instantiate_dec. *)
      let ty_args' = List.map (encode_type ctx.data_sorts) ty_args in
      let args' = List.map (encode_term ctx) args in
      (* Get the original dec to find how many params it has *)
      let orig_dec = match Path.find_opt dec ctx.types.decs with
          Some d -> d
        | None -> failwith ("Unknown declaration: " ^ Path.name dec)
      in
      let n_dec_params = List.length orig_dec.param_kinds in
      let dec_type_args = List.filteri (fun i _ -> i < n_dec_params) ty_args' in
      let inst_dec = get_instantiated_dec ctx dec dec_type_args in
      CTm.Ctor (inst_dec, ctor, args')

  | MTm.TypedDtor (dec, dtor, ty_args, args, ty) ->
      (* Dtor(d, c, {ty_args}, this :: rest) where this : raise(codata)
         
         ty_args contains BOTH dec params AND xtor existentials.
         We need to split them: only dec params go to instantiate_dec.
         
         Since codata types are wrapped in raise, we need to unwrap before calling.
         μα.⟨this' | match { thunk(g) => ⟨g | Dtor(inst_dec, c, rest' @ [α])⟩ }⟩ *)
      let ty' = encode_type ctx.data_sorts ty in
      let ty_args' = List.map (encode_type ctx.data_sorts) ty_args in
      (* Get the original dec to find how many params it has *)
      let orig_dec = match Path.find_opt dec ctx.types.decs with
          Some d -> d
        | None -> failwith ("Unknown declaration: " ^ Path.name dec)
      in
      let n_dec_params = List.length orig_dec.param_kinds in
      let dec_type_args = List.filteri (fun i _ -> i < n_dec_params) ty_args' in
      let exist_type_args = List.filteri (fun i _ -> i >= n_dec_params) ty_args' in
      let inst_dec = get_instantiated_dec ctx dec dec_type_args in
      (match args with
        [] -> failwith "Dtor must have at least a subject argument"
      | this_arg :: rest_args ->
          let this' = encode_term ctx this_arg in
          let this_ty = encode_type ctx.data_sorts (MTm.get_type this_arg) in
          (* rest' needs to be reversed because:
            - Melcore rest_args are in surface order: [arg1, arg2, ...]
            - Core argument_types are stored reversed: [result; argN; ...; arg1]
            - So after prepending alpha (result), we need [alpha; argN; ...; arg1] *)
          let rest' = List.rev (List.map (encode_term ctx) rest_args) in
          let alpha = Ident.fresh () in
          
          (* this_ty is raise(inner_codata_ty) *)
          let inner_codata_ty = match this_ty with
              CTy.Sgn (s, [inner]) when Path.equal s Prim.raise_sym -> inner
            | _ -> failwith "Dtor subject must have codata type (wrapped in raise)"
          in
          let raise_dec = get_instantiated_dec ctx Prim.raise_sym [inner_codata_ty] in
          let g = Ident.fresh () in
          
          CTm.MuPrd (ty', alpha,
            make_cut this_ty this'
              (CTm.Match (raise_dec,
                [(Prim.thunk_sym, [], [g],
                  (* In Core, dtor args are: [continuation, rest args reversed]
                     The continuation (alpha) comes FIRST *)
                  make_cut inner_codata_ty (CTm.Var g)
                    (CTm.Dtor (inst_dec, dtor, exist_type_args, [CTm.Var alpha] @ rest')))]))))

  | MTm.TypedIfz (cond, then_br, else_br, ty) ->
      (* ifz cond then t else e → μα.ifz(cond', ⟨then' | α⟩, ⟨else' | α⟩) *)
      let cond' = encode_term ctx cond in
      let then' = encode_term_tail ctx then_br in  (* branches are in tail position *)
      let else' = encode_term_tail ctx else_br in
      let ty' = encode_type ctx.data_sorts ty in
      let alpha = Ident.fresh () in
      CTm.MuPrd (ty', alpha,
        CTm.Ifz (cond',
          make_cut ty' then' (CTm.Var alpha),
          make_cut ty' else' (CTm.Var alpha)))

(** Helper: wrap body and cut against k, handling Lower codomain *)
and wrap_body_for_cod (ctx: encode_ctx) (body: CTm.term) (body_ty: CTy.typ) 
    (cod: CTy.typ) (k: Ident.t) : CTm.command =
  match cod with
    CTy.Sgn (s, [_inner_ty]) when Path.equal s Prim.lower_sym ->
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

(** Encode a match branch - alpha is the outer continuation variable.
    The inst_dec is the instantiated declaration, which has quantified = []
    and only existentials remain. We need to filter ty_vars to keep only
    the existential part (drop the quantified vars that are now fixed). *)
and encode_match_branch (ctx: encode_ctx) (inst_dec: CTy.dec) (result_ty: CTy.typ) (alpha: Ident.t)
    ((xtor, ty_vars, tm_vars, body): MTm.typed_clause) : CTm.branch =
  let body' = encode_term_tail ctx body in  (* branch body is in tail position *)
  let cmd = make_cut result_ty body' (CTm.Var alpha) in
  (* Find the xtor in the instantiated dec to get existential count *)
  let n_exist = match List.find_opt (fun (x: CTy.xtor) -> Path.equal x.name xtor) inst_dec.xtors with
    | Some inst_xtor -> List.length inst_xtor.existentials
    | None -> 0  (* Should not happen for valid code *)
  in
  (* Keep only the last n_exist type vars (existentials come after quantified) *)
  let exist_ty_vars = 
    if n_exist = 0 then []
    else 
      let n_total = List.length ty_vars in
      let start = n_total - n_exist in
      List.filteri (fun i _ -> i >= start) ty_vars
  in
  (xtor, exist_ty_vars, tm_vars, cmd)

(** Encode a new/comatch branch - bind result continuation k.
    Similar to encode_match_branch, filter ty_vars to keep only existentials.
    
    In Core, codata xtor arguments are ordered: [cns return_type, prd argN, ...prd arg1]
    (reversed from surface order). So the continuation k comes FIRST, then tm_vars reversed. *)
and encode_new_branch (ctx: encode_ctx) (inst_dec: CTy.dec)
    ((xtor, ty_vars, tm_vars, body): MTm.typed_clause) : CTm.branch =
  let body' = encode_term_tail ctx body in  (* branch body is in tail position *)
  let body_ty = encode_type ctx.data_sorts (MTm.get_type body) in
  let k = Ident.fresh () in
  let cmd = make_cut body_ty body' (CTm.Var k) in
  (* Find the xtor in the instantiated dec to get existential count *)
  let n_exist = match List.find_opt (fun (x: CTy.xtor) -> Path.equal x.name xtor) inst_dec.xtors with
    | Some inst_xtor -> List.length inst_xtor.existentials
    | None -> 0
  in
  (* Keep only the last n_exist type vars (existentials come after quantified) *)
  let exist_ty_vars = 
    if n_exist = 0 then []
    else 
      let n_total = List.length ty_vars in
      let start = n_total - n_exist in
      List.filteri (fun i _ -> i >= start) ty_vars
  in
  (* k comes first (consumer for return), then the pattern variables REVERSED
     to match the reversed order in argument_types *)
  (xtor, exist_ty_vars, [k] @ List.rev tm_vars, cmd)

(* ========================================================================= *)
(* Definition Encoding                                                       *)
(* ========================================================================= *)

(** Encode a Melcore typed term definition into a Core definition *)
let encode_def (ctx: encode_ctx) (def: MTm.typed_term_def) : CTm.definition =
  (* Use encode_term_tail for the body - this enables tail call optimization *)
  let body' = encode_term_tail ctx def.body in
  let return_ty = encode_type ctx.data_sorts def.return_type in
  let k = Ident.fresh () in
  { path = def.name
  ; type_params = List.map (fun (v, k) ->
        (v, encode_type ctx.data_sorts k)
      ) def.type_params
  ; term_params = List.map (fun (v, t) ->
        (v, CB.Prd (encode_type ctx.data_sorts t))
      ) def.term_params
      @ [(k, CB.Cns return_ty)]  (* Add return continuation *)
  ; body = make_cut return_ty body' (CTm.Var k)
  }

(* Alias for backward compatibility *)
let encode_term_def = encode_def