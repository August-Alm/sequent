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
  { name = x.name
  ; quantified = List.map (fun (v, k) -> (v, encode_type sorts k)) x.quantified
  ; existentials = List.map (fun (v, k) -> (v, encode_type sorts k)) x.existentials
  ; argument_types = List.mapi encode_xtor_arg x.argument_types
  ; main = encode_type sorts x.main
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
  }

(** Build an encoding context from Melcore type declarations *)
let make_encode_ctx (melcore_decs: MTy.dec list) : encode_ctx =
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
  { types = types; data_sorts = sorts }

(** Get an instantiated declaration for a symbol with given type arguments *)
let get_instantiated_dec (ctx: encode_ctx) (sym: Path.t) (type_args: CTy.typ list) : CTy.dec =
  match Path.find_opt sym ctx.types.decs with
    Some dec -> CTy.instantiate_dec dec type_args
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
    MTm.TypedInt n -> CTm.Lit n

  | MTm.TypedVar (x, _ty) -> CTm.Var x

  | MTm.TypedSym (path, ty) ->
      (* Symbol reference - encoded as a call that returns a value *)
      let ty' = encode_type ctx.data_sorts ty in
      let k = Ident.fresh () in
      CTm.MuPrd (ty', k, CTm.Call (path, [], [CTm.Var k]))

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
      (* Λa:k. body → thunk(NewForall(a, k', body_ty', ⟨body' | α⟩))
         
         Forall types are encoded as raise(∀a:k. lower(body_ty)).
         But at the term level, we produce body_ty' directly (positive).
         The lower wrapping is just for typing the forall.
         
         The NewForall body produces body_ty', and the continuation α
         receives that value. When instantiated, the body runs and
         the result flows to the instantiation continuation.
         
         NewForall is negative, so wrap in thunk. *)
      let k' = encode_type ctx.data_sorts k in
      let body_ty' = match ty with
          MTy.Forall (_, _, inner) -> encode_type ctx.data_sorts inner
        | _ -> failwith "TypedAll must have Forall type"
      in
      let body' = encode_term ctx body in
      let alpha = Ident.fresh () in
      (* Use body_ty' as the forall body type, NOT lower(body_ty') *)
      let inner_forall_ty = CTy.Forall (tv, k', body_ty') in
      let new_forall = CTm.NewForall (tv, k', body_ty', make_cut body_ty' body' (CTm.Var alpha)) in
      (* Wrap in thunk to produce raise(∀...) *)
      let raise_dec = get_instantiated_dec ctx Prim.raise_sym [inner_forall_ty] in
      CTm.Ctor (raise_dec, Prim.thunk_sym, [new_forall])

  | MTm.TypedApp (f, arg, result_ty) ->
      (* f(arg) where f : raise(fun(dom, cod))
         
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
        | CTy.Sgn (s, [CTy.Sgn (fun_s, [d; c])]) 
            when Path.equal s Prim.raise_sym && Path.equal fun_s Prim.fun_sym ->
            (CTy.Sgn (Prim.fun_sym, [d; c]), d, c)
        | CTy.Sgn (fun_s, [d; c]) when Path.equal fun_s Prim.fun_sym ->
            (* Fallback: f_ty is already fun(dom, cod) - shouldn't happen but handle it *)
            (f_ty, d, c)
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
      let raise_dec = get_instantiated_dec ctx Prim.raise_sym [inner_fun_ty] in
      let g = Ident.fresh () in
      
      (* Build the application command *)
      let build_app_cmd (result_cont: CTm.term) : CTm.command =
        make_cut inner_fun_ty (CTm.Var g)
          (CTm.Dtor (fun_dec, Prim.apply_sym, [result_cont; wrapped_arg]))
      in
      
      (match cod with
        | CTy.Sgn (s, [inner_ty]) when Path.equal s Prim.lower_sym ->
            (* cod = Lower(inner_ty), function returns suspended computation.
               Need to force it. *)
            let lower_dec = get_instantiated_dec ctx Prim.lower_sym [inner_ty] in
            let thunk = Ident.fresh () in
            let ret = Ident.fresh () in
            let force_cmd = make_cut cod (CTm.Var thunk)
              (CTm.Dtor (lower_dec, Prim.return_sym, [CTm.Var ret])) in
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
        | CTy.Sgn (s, [inner]) when Path.equal s Prim.raise_sym -> inner
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
      let t2' = encode_term ctx t2 in
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
      let branches' = List.map (encode_match_branch ctx ty') branches in
      let alpha = Ident.fresh () in
      CTm.MuPrd (ty', alpha,
        make_cut scrut_ty scrut' (CTm.Match (inst_dec, branches')))

  | MTm.TypedNew (branches, ty) ->
      (* new { ... } → thunk(Comatch(d, branches'))
         
         Since codata types are encoded as raise(codata), we wrap the comatch
         in thunk to produce a positive value. *)
      let ty' = encode_type ctx.data_sorts ty in
      (* ty' is raise(inner_codata_ty) *)
      let inner_codata_ty = match ty' with
        | CTy.Sgn (s, [inner]) when Path.equal s Prim.raise_sym -> inner
        | _ -> failwith "New type must be codata type (wrapped in raise)"
      in
      let (dec_name, type_args) = match inner_codata_ty with
          CTy.Sgn (d, args) -> (d, args)
        | _ -> failwith "New type must be codata type"
      in
      let inst_dec = get_instantiated_dec ctx dec_name type_args in
      let branches' = List.map (encode_new_branch ctx) branches in
      let comatch = CTm.Comatch (inst_dec, branches') in
      (* Wrap in thunk *)
      let raise_dec = get_instantiated_dec ctx Prim.raise_sym [inner_codata_ty] in
      CTm.Ctor (raise_dec, Prim.thunk_sym, [comatch])

  | MTm.TypedCtor (dec, ctor, ty_args, args, _ty) ->
      (* Ctor(d, c, {ty_args}, args) → Ctor(inst_dec, c, args') *)
      let ty_args' = List.map (encode_type ctx.data_sorts) ty_args in
      let args' = List.map (encode_term ctx) args in
      let inst_dec = get_instantiated_dec ctx dec ty_args' in
      CTm.Ctor (inst_dec, ctor, args')

  | MTm.TypedDtor (dec, dtor, ty_args, args, ty) ->
      (* Dtor(d, c, {ty_args}, this :: rest) where this : raise(codata)
         
         Since codata types are wrapped in raise, we need to unwrap before calling.
         μα.⟨this' | match { thunk(g) => ⟨g | Dtor(inst_dec, c, rest' @ [α])⟩ }⟩ *)
      let ty' = encode_type ctx.data_sorts ty in
      let ty_args' = List.map (encode_type ctx.data_sorts) ty_args in
      let inst_dec = get_instantiated_dec ctx dec ty_args' in
      (match args with
        [] -> failwith "Dtor must have at least a subject argument"
      | this_arg :: rest_args ->
          let this' = encode_term ctx this_arg in
          let this_ty = encode_type ctx.data_sorts (MTm.get_type this_arg) in
          let rest' = List.map (encode_term ctx) rest_args in
          let alpha = Ident.fresh () in
          
          (* this_ty is raise(inner_codata_ty) *)
          let inner_codata_ty = match this_ty with
            | CTy.Sgn (s, [inner]) when Path.equal s Prim.raise_sym -> inner
            | _ -> failwith "Dtor subject must have codata type (wrapped in raise)"
          in
          let raise_dec = get_instantiated_dec ctx Prim.raise_sym [inner_codata_ty] in
          let g = Ident.fresh () in
          
          CTm.MuPrd (ty', alpha,
            make_cut this_ty this'
              (CTm.Match (raise_dec,
                [(Prim.thunk_sym, [], [g],
                  make_cut inner_codata_ty (CTm.Var g)
                    (CTm.Dtor (inst_dec, dtor, rest' @ [CTm.Var alpha])))]))))

  | MTm.TypedIfz (cond, then_br, else_br, ty) ->
      (* ifz cond then t else e → μα.ifz(cond', ⟨then' | α⟩, ⟨else' | α⟩) *)
      let cond' = encode_term ctx cond in
      let then' = encode_term ctx then_br in
      let else' = encode_term ctx else_br in
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
  let body_ty = encode_type ctx.data_sorts (MTm.get_type body) in
  let k = Ident.fresh () in
  let cmd = make_cut body_ty body' (CTm.Var k) in
  (xtor, ty_vars, tm_vars @ [k], cmd)

(* ========================================================================= *)
(* Definition Encoding                                                       *)
(* ========================================================================= *)

(** Encode a Melcore typed term definition into a Core definition *)
let encode_term_def (ctx: encode_ctx) (def: MTm.typed_term_def) : CTm.definition =
  let body' = encode_term ctx def.body in
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