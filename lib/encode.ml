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

(* Map Melcore kinds to Core kinds *)
let rec map_kind (k: MTy.kind) : CTy.kind =
  match k with
    MTy.Star -> CTy.Star
  | MTy.Arrow (k1, k2) -> CTy.Arrow (map_kind k1, map_kind k2)

(* Lower ↓(A) *)
let lower (ty: CTy.typ) : CTy.typ = 
  CTy.App (CTy.Sym (Sym.lower_t, Prim.lower_sgn_lazy), [ty])

(* Raise ↑(A) *)
let raise (ty: CTy.typ) : CTy.typ = 
  CTy.App (CTy.Sym (Sym.raise_t, Prim.raise_sgn_lazy), [ty])

(* Check if a Melcore type is positive (data) or negative (codata)
   Type variables are always positive (Uniform CBV). *)
let rec is_positive (ty: MTy.typ) : bool =
  match ty with
    MTy.Ext _ -> true
  | MTy.Var _ -> true  (* Uniform CBV: type variables are positive *)
  | MTy.Rigid _ -> true  (* Uniform CBV: type variables are positive *)
  | MTy.Sym (_, MTy.Pos, _) -> true
  | MTy.Sym (_, MTy.Neg, _) -> false
  | MTy.App (t, _) -> is_positive t
  | MTy.Fun _ -> false
  | MTy.All _ -> false
  | MTy.Data _ -> true
  | MTy.Code _ -> false

let rec map_typ (ty: MTy.typ) : CTy.typ =
  match ty with
    MTy.Ext Int -> CTy.Ext Int
  | MTy.Var v ->
      (match !v with
        Unbound x -> CTy.Var (ref (CTy.Unbound x))
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
  | MTy.Fun (a, b) ->
      (* Encoding of A → B:
        - Argument: if positive stays as-is, if negative is raised ↑A'
          (computations must be suspended into values)
        - Result: if positive is lowered ↓B', if negative is ↓↑B'
          (computations must be packed before returning) *)
      let a' = map_typ a in
      let b' = map_typ b in
      let a_part = if is_positive a then a' else raise a' in
      let b_part = if is_positive b then lower b' else lower (raise b') in
      App (Sym (Sym.fun_t, Prim.fun_sgn_lazy), [a_part; b_part])
  | MTy.All ((x, k), body) ->
      (* Encoding of ∀(x:k). B:
        - If B is positive, lower it: ↓B'
        - If B is negative, ↓↑B' (pack then return) *)
      let k' = map_kind k in
      let body' = map_typ body in
      let body_part = if is_positive body then lower body' else lower (raise body') in
      App (Sym (Sym.all_t k', Prim.all_sgn_lazy x k'), [body_part])

and map_data (sgn: MTy.sgn_typ) : CTy.sgn_typ =
  { CTy.name = sgn.MTy.name
  ; CTy.parameters = List.map map_kind sgn.MTy.parameters
  ; CTy.xtors = List.map map_ctor sgn.MTy.xtors
  }

and map_code (sgn: MTy.sgn_typ) : CTy.sgn_typ =
  { CTy.name = sgn.MTy.name
  ; CTy.parameters = List.map map_kind sgn.MTy.parameters
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

(* ========================================================================= *)
(* Helpers for constructing instantiated signatures                          *)
(* ========================================================================= *)

(* Instantiate the Fun signature with concrete types a and b *)
let instantiate_fun_sgn kctx (a: CTy.typ) (b: CTy.typ) : CTy.sgn_typ =
  CTy.instantiate kctx Prim.fun_sgn_lazy [a; b]

let instantiate_fun_apply kctx (a: CTy.typ) (b: CTy.typ) : CTy.xtor =
  List.hd (instantiate_fun_sgn kctx a b).xtors

(* Instantiate the Lower signature with concrete type a *)
let instantiate_lower_sgn kctx (a: CTy.typ) : CTy.sgn_typ =
  CTy.instantiate kctx Prim.lower_sgn_lazy [a]

let instantiate_lower_return kctx (a: CTy.typ) : CTy.xtor =
  List.hd (instantiate_lower_sgn kctx a).xtors

(* Instantiate the Raise signature with concrete type a *)
let instantiate_raise_sgn kctx (a: CTy.typ) : CTy.sgn_typ =
  CTy.instantiate kctx Prim.raise_sgn_lazy [a]

let instantiate_raise_pack kctx (a: CTy.typ) : CTy.xtor =
  List.hd (instantiate_raise_sgn kctx a).xtors

(* Instantiate the All signature with a concrete body type *)
let instantiate_all_sgn kctx (k: CTy.kind) (body: CTy.typ) : CTy.sgn_typ =
  let a_var = Ident.fresh () in
  CTy.instantiate kctx (Prim.all_sgn_lazy a_var k) [body]

let instantiate_all_instantiate kctx (k: CTy.kind) (body: CTy.typ) : CTy.xtor =
  List.hd (instantiate_all_sgn kctx k body).xtors

(* ========================================================================= *)
(* Term Encoding                                                             *)
(* ========================================================================= *)

(* Helper: wrap a term body in nested lambdas for the given (var, type) pairs.
   build_lambdas [(x1, T1); (x2, T2)] body 
   = TypedLam(x1, T1, TypedLam(x2, T2, body, T2 -> body_ty), T1 -> T2 -> body_ty) *)
let build_lambdas (var_tys: (Ident.t * MTy.typ) list) (body: MTm.typed_term) : MTm.typed_term =
  List.fold_right
    (fun (v, ty) body ->
      let body_ty = MTm.get_type body in
      MTm.TypedLam (v, ty, body, MTy.Fun (ty, body_ty)))
    var_tys
    body

(* Helper: wrap a term body in nested type abstractions for the given (var, kind) pairs.
   build_alls [(a1, K1); (a2, K2)] body 
   = TypedAll((a1, K1), TypedAll((a2, K2), body, ∀a2:K2. body_ty), ∀a1:K1.∀a2:K2. body_ty) *)
let build_alls (var_kinds: (Ident.t * MTy.kind) list) (body: MTm.typed_term) : MTm.typed_term =
  List.fold_right
    (fun (v, k) body ->
      let body_ty = MTm.get_type body in
      MTm.TypedAll ((v, k), body, MTy.All ((v, k), body_ty)))
    var_kinds
    body

(* Helper: apply type instantiations to a term.
   Given t : ∀a1...an. T and vars [(x1,k1)...(xn,kn)],
   returns (t{Rigid x1}...{Rigid xn}, subst) where subst maps ai to Rigid xi *)
let apply_type_args (t: MTm.typed_term) (type_args: (Ident.t * MTy.kind) list) : MTm.typed_term * (Ident.t * MTy.typ) list =
  List.fold_left
    (fun (acc, subst) (v, k) ->
      let acc_ty = MTm.get_type acc in
      match MTy.whnf Ident.emptytbl [] acc_ty with
        | MTy.All ((x, _), body) ->
            let ty_arg = MTy.Rigid v in
            let new_subst = (x, ty_arg) :: subst in
            let result_ty = MTy.subst_rigid new_subst body in
            (MTm.TypedIns (acc, ty_arg, k, result_ty), new_subst)
        | _ -> failwith "Expected All type for type instantiation")
    (t, [])
    type_args

(* Helper: apply term arguments to a term *)
let apply_term_args (subst: (Ident.t * MTy.typ) list) (t: MTm.typed_term) (term_args: (Ident.t * MTy.typ) list) : MTm.typed_term =
  List.fold_left
    (fun acc (v, ty) ->
      let acc_ty = MTm.get_type acc in
      match MTy.whnf Ident.emptytbl [] acc_ty with
        | MTy.Fun (_, cod) -> MTm.TypedApp (acc, MTm.TypedVar (v, ty), MTy.subst_rigid subst cod)
        | _ -> failwith "Expected function type")
    t
    term_args

(* Encode a term of a given type, wrapping appropriately for polarity.
  - Positive types produce Lhs (producers/values)
  - Negative types produce Rhs (consumers/computations)
  When we need a positive result from a negative term, we must wrap. *)

(* Helper: collect a chain of applications to a symbol.
   Returns Some (path, sym_ty, args) if tm is App(...App(Sym(path, sym_ty), arg1)..., argN)
   where args = [arg1; ...; argN] in application order. *)
let rec collect_symbol_app_chain (tm: MTm.typed_term) : (Path.t * MTy.typ * MTm.typed_term list) option =
  match tm with
    MTm.TypedSym (path, ty) -> Some (path, ty, [])
  | MTm.TypedApp (f, arg, _) ->
      (match collect_symbol_app_chain f with
        Some (path, sym_ty, args) -> Some (path, sym_ty, args @ [arg])
      | None -> None)
  | _ -> None

let rec map_term (defs: MTm.typed_definitions) (kctx: CTy.kind Ident.tbl) (ctx: MTy.typ Ident.tbl) (tm: MTm.typed_term) : CTm.term =
  (* First, check if this is an application chain to a symbol *)
  match collect_symbol_app_chain tm with
    Some (path, sym_ty, args) when args <> [] ->
      (* Application(s) to a symbol - handle the whole chain together *)
      encode_symbol_with_args defs kctx ctx path sym_ty args (MTm.get_type tm)
  | _ ->
      (* Normal dispatch *)
      match tm with
        MTm.TypedInt n -> CTm.Lit n
      
      | MTm.TypedAdd (t1, t2) ->
          (* t1 + t2 where t1, t2 : Int
            Translates to: μL k. add(t1', t2', k) *)
          let t1' = map_term defs kctx ctx t1 in
      let t2' = map_term defs kctx ctx t2 in
      let k = Ident.fresh () in
      CTm.MuLhs (CTy.Ext Int, k, CTm.Add (t1', t2', CTm.Var k))
  
  | MTm.TypedIfz (cond, then_branch, else_branch, result_ty) ->
      (* ifz cond then t else u where cond : Int, t and u : B
         Translates to: μL/μR k. ifz(cond') then ⟨t' | k⟩ else ⟨u' | k⟩ *)
      let b = result_ty in
      let cond' = map_term defs kctx ctx cond in
      let then' = map_term defs kctx ctx then_branch in
      let else' = map_term defs kctx ctx else_branch in
      let k = Ident.fresh () in
      let b' = map_typ b in
      let make_mu = if is_positive b then
        (fun ty k cmd -> CTm.MuLhs (ty, k, cmd))
      else
        (fun ty k cmd -> CTm.MuRhs (ty, k, cmd))
      in
      let make_branch_cut b' branch k =
        if is_positive b then
          CTm.Cut (b', branch, CTm.Var k)
        else
          CTm.Cut (b', CTm.Var k, branch)
      in
      make_mu b' k
        (CTm.Ifz (cond', 
          make_branch_cut b' then' k,
          make_branch_cut b' else' k))
  
  | MTm.TypedVar (x, _ty) -> 
      CTm.Var x
  
  | MTm.TypedSym (path, ty) ->
      (* Symbol reference: look up definition and call it.
        If the type is polymorphic (All or Fun at top level), this is a
        partial application and should be encoded like a lambda. *)
      encode_sym defs kctx ctx path ty
  
  | MTm.TypedApp (f, arg, result_ty) ->
      (* f arg where f : A → B, arg : A, result : B
        Application is: ⟨ctor_apply[A', B_ret](arg', k) | f'⟩
        wrapped in μL/μR based on whether B is positive/negative. *)
      let f_ty = MTm.get_type f in
      let (a, b) = match MTy.whnf Ident.emptytbl [] f_ty with
        | MTy.Fun (a, b) -> (a, b)
        | _ -> failwith "Application of non-function"
      in
      encode_app defs kctx ctx f arg a b result_ty
  
  | MTm.TypedIns (MTm.TypedAll ((a, _k), body, _all_ty), ty_arg, _, _result_ty) ->
      (* Type-level beta reduction: (Λa. body){ty_arg} -> body[ty_arg/a]
         Substitute the type argument for the bound variable and recurse. *)
      let body' = MTm.subst_type_in_typed_term [(a, ty_arg)] body in
      map_term defs kctx ctx body'

  | MTm.TypedIns (t, ty_arg, _k, result_ty) ->
      (* t{ty_arg} where t : ∀(x:k). B, result : B[ty_arg/x]
        Similar to application but at the type level. *)
      let t_ty = MTm.get_type t in
      let ((_x, k), body) = match MTy.whnf Ident.emptytbl [] t_ty with
        | MTy.All ((x, k), body) -> ((x, k), body)
        | _ -> failwith "Type instantiation of non-forall"
      in
      encode_ins defs kctx ctx t ty_arg k body result_ty
  
  | MTm.TypedLam (x, a, body, _fun_ty) ->
      (* λx:A. body where body: B
        Encoding wraps body appropriately based on polarity of B. *)
      let ctx' = Ident.add x a ctx in
      let b = MTm.get_type body in
      encode_lam defs kctx ctx' x a body b
  
  | MTm.TypedAll ((x, k), body, _all_ty) ->
      (* Λ(x:k). body - type abstraction
        Similar to lambda but binds a type variable. *)
      let body_ty = MTm.get_type body in
      let kctx' = Ident.add x (map_kind k) kctx in
      encode_all defs kctx' ctx x k body body_ty
  
  | MTm.TypedLet (x, t1, t2, _ty) ->
      (* let x = t1 in t2 is equivalent to (λx:A. t2) t1 *)
      let a = MTm.get_type t1 in
      let b = MTm.get_type t2 in
      let lam = MTm.TypedLam (x, a, t2, MTy.Fun (a, b)) in
      let app = MTm.TypedApp (lam, t1, b) in
      map_term defs kctx ctx app
  
  | MTm.TypedMatch (scrut, branches, result_ty) ->
      (* match scrut with { branches }
        Encoding: Cut(scrut_ty, scrut', Match(sgn, encoded_branches)) *)
      encode_match defs kctx ctx scrut branches result_ty
  
  | MTm.TypedNew (branches, result_ty) ->
      (* new { branches } - codata introduction
        Encoding: Comatch(sgn, encoded_branches) *)
      encode_new defs kctx ctx branches result_ty
  
  | MTm.TypedCtor (xtor, args, result_ty) ->
      (* Constructor application, possibly partial.
        If partial, encode like a lambda. *)
      encode_ctor defs kctx ctx xtor args result_ty
  
  | MTm.TypedDtor (xtor, args, result_ty) ->
      (* Destructor application, possibly partial.
        If partial, encode like a lambda. *)
      encode_dtor defs kctx ctx xtor args result_ty

(* Encode a symbol applied to some arguments.
  This handles the case where we have App(...App(Sym(path), arg1)..., argN).
  If fully saturated, emit a Call. If partial, wrap remaining args in lambdas. *)
and encode_symbol_with_args (defs: MTm.typed_definitions) (kctx: CTy.kind Ident.tbl) (ctx: MTy.typ Ident.tbl) 
    (path: Path.t) (_sym_ty: MTy.typ) (args: MTm.typed_term list) (result_ty: MTy.typ) : CTm.term =
  match Path.find_opt path defs with
    None -> failwith ("Undefined symbol: " ^ Path.name path)
  | Some def ->
      let num_term_args = List.length def.term_args in
      let provided = List.length args in
      if provided = num_term_args then
        (* Fully saturated: emit Call *)
        let encoded_args = List.map (map_term defs kctx ctx) args in
        CTm.MuLhs (map_typ result_ty, Ident.fresh (), CTm.Call (path, [], encoded_args))
      else if provided < num_term_args then
        (* Partial application: wrap remaining args in lambdas *)
        let remaining_params = List.filteri (fun i _ -> i >= provided) def.term_args in
        let fresh_vars = List.map (fun (_, ty) -> (Ident.fresh (), ty)) remaining_params in
        let all_args = args @ List.map (fun (v, ty) -> MTm.TypedVar (v, ty)) fresh_vars in
        (* Build the inner application chain: App(...App(Sym, arg1)..., argN) *)
        let inner = List.fold_left2
          (fun acc arg _param_ty ->
            let acc_ty = MTm.get_type acc in
            let result = match MTy.whnf Ident.emptytbl [] acc_ty with
              | MTy.Fun (_, cod) -> cod
              | _ -> failwith "Expected function type in symbol application"
            in
            MTm.TypedApp (acc, arg, result))
          (MTm.TypedSym (path, 
            List.fold_right (fun (_, ty) acc -> MTy.Fun (ty, acc)) def.term_args def.return_type))
          all_args
          (List.map snd def.term_args)
        in
        map_term defs kctx ctx (build_lambdas fresh_vars inner)
      else
        failwith "Too many arguments to symbol"

(* Encode a bare symbol reference (not applied to any arguments).
  If the symbol expects arguments, build a lambda that takes them. *)
and encode_sym (defs: MTm.typed_definitions) (kctx: CTy.kind Ident.tbl) (ctx: MTy.typ Ident.tbl) (path: Path.t) (ty: MTy.typ) : CTm.term =
  match Path.find_opt path defs with
    None -> failwith ("Undefined symbol: " ^ Path.name path)
  | Some def ->
      let num_term_args = List.length def.term_args in
      let num_type_args = List.length def.type_args in
      if num_type_args = 0 && num_term_args = 0 then
        (* No arguments: just call *)
        CTm.MuLhs (map_typ ty, Ident.fresh (), CTm.Call (path, [], []))
      else
        (* Has arguments: build eta-expansion.
           Λa1...Λan. λx1...λxm. path{a1}...{an}(x1)...(xm) *)
        let fresh_type_vars = List.map (fun (_, k) -> (Ident.fresh (), k)) def.type_args in
        let sym = MTm.TypedSym (path, ty) in
        let (with_type_apps, type_subst) = apply_type_args sym fresh_type_vars in
        
        (* Fresh term vars with types from def, substituted for type vars *)
        let fresh_term_vars = List.map (fun (_, arg_ty) ->
          (Ident.fresh (), MTy.subst_rigid type_subst arg_ty)
        ) def.term_args in
        
        let with_term_apps = apply_term_args type_subst with_type_apps fresh_term_vars in
        let with_lambdas = build_lambdas fresh_term_vars with_term_apps in
        let with_alls = build_alls fresh_type_vars with_lambdas in
        map_term defs kctx ctx with_alls

(* Encode function application *)
and encode_app (defs: MTm.typed_definitions) (kctx: CTy.kind Ident.tbl) (ctx: MTy.typ Ident.tbl) 
    (f: MTm.typed_term) (arg: MTm.typed_term) 
    (a: MTy.typ) (b: MTy.typ) (_result_ty: MTy.typ) : CTm.term =
  let f' = map_term defs kctx ctx f in
  let arg' = map_term defs kctx ctx arg in
  let k = Ident.fresh () in
  let a' = map_typ a in
  let b' = map_typ b in
  (* Return type: always ↓b' - no raise wrapper needed *)
  let b_ret = lower b' in
  (* Choose Mu form based on whether result type is positive or negative *)
  let make_mu = if is_positive b then
    (fun ty var cmd -> CTm.MuLhs (ty, var, cmd))
  else
    (fun ty var cmd -> CTm.MuRhs (ty, var, cmd))
  in
  (* For positive a: arg' is used directly
     For negative a: wrap arg' in Pack *)
  let arg_term = if is_positive a then arg' else
    CTm.Ctor (instantiate_raise_sgn kctx a', instantiate_raise_pack kctx a', [arg'])
  in
  let a_eff = if is_positive a then a' else raise a' in
  let the_apply_sgn = instantiate_fun_sgn kctx a_eff b_ret in
  let the_apply_xtor = instantiate_fun_apply kctx a_eff b_ret in
  (* Inner cut between return value x and continuation k *)
  let x = Ident.fresh () in
  let make_inner_cut x k =
    if is_positive b then
      CTm.Cut (b', CTm.Var x, CTm.Var k)
    else
      CTm.Cut (b', CTm.Var k, CTm.Var x)
  in
  (* Continuation that receives the result - simplified: no raise/pack unpacking *)
  let continuation =
    CTm.Match (instantiate_lower_sgn kctx b', [(instantiate_lower_return kctx b', [x], make_inner_cut x k)])
  in
  (* Build the application *)
  make_mu b' k
    (CTm.Cut (CTy.Sgn the_apply_sgn,
      CTm.Ctor (the_apply_sgn, the_apply_xtor, [arg_term; continuation]),
      f'))

(* Encode type instantiation *)
and encode_ins (defs: MTm.typed_definitions) (kctx: CTy.kind Ident.tbl) (ctx: MTy.typ Ident.tbl)
    (t: MTm.typed_term) (_ty_arg: MTy.typ) (kind: MTy.kind) (_body: MTy.typ) (result_ty: MTy.typ) : CTm.term =
  (* t{A} where t : ∀(x:k). B, result : B[A/x]
    Similar to function application but at the type level.
     
    For uniform CBV, type variables are positive. If the type argument A is
    negative, we must raise it to make it positive before instantiation. *)
  let t' = map_term defs kctx ctx t in
  let result_ty' = map_typ result_ty in
  let k = Ident.fresh () in
  
  (* Result type: always lower[result_ty'] *)
  let b_ret = lower result_ty' in
  
  let make_mu = if is_positive result_ty then
    (fun ty var cmd -> CTm.MuLhs (ty, var, cmd))
  else
    (fun ty var cmd -> CTm.MuRhs (ty, var, cmd))
  in
  
  (* Build the instantiate destructor.
    The All signature: All(k)[B] has destructor instantiate[∃t:k->*](arg: t(a))
    We instantiate with the effective type argument (raised if negative). *)
  let x = Ident.fresh () in
  let make_inner_cut x k =
    if is_positive result_ty then
      CTm.Cut (result_ty', CTm.Var x, CTm.Var k)
    else
      CTm.Cut (result_ty', CTm.Var k, CTm.Var x)
  in
  
  (* Continuation that receives the result - simplified: no raise/pack unpacking *)
  let continuation =
    CTm.Match (instantiate_lower_sgn kctx result_ty', [(instantiate_lower_return kctx result_ty', [x], make_inner_cut x k)])
  in
  
  (* Build the Dtor for instantiate using the helper.
     The All signature All(k)[body] is instantiated with body = b_ret = lower[result_ty'].
     The xtor's universal params (t, a) get unified during instantiate. *)
  let k' = map_kind kind in
  let all_sgn = instantiate_all_sgn kctx k' b_ret in
  let inst_xtor = instantiate_all_instantiate kctx k' b_ret in
  
  make_mu result_ty' k
    (CTm.Cut (CTy.Sgn all_sgn,
      t',
      CTm.Dtor (all_sgn, inst_xtor, [continuation])))

(* Encode lambda abstraction *)  
and encode_lam (defs: MTm.typed_definitions) (kctx: CTy.kind Ident.tbl) (ctx: MTy.typ Ident.tbl)
    (x: Ident.t) (a: MTy.typ) (body: MTm.typed_term) (b: MTy.typ) : CTm.term =
  let body' = map_term defs kctx ctx body in
  let k = Ident.fresh () in
  let a' = map_typ a in
  let b' = map_typ b in
  (* Return type: always ↓b' - no need for ↑ wrapper, lower[A] works for any A *)
  let b_ret = lower b' in
  (* Return term: always return[b'](body') - works for both positive and negative *)
  let make_return body' = 
    CTm.Ctor (instantiate_lower_sgn kctx b', instantiate_lower_return kctx b', [body'])
  in
  let a_eff = if is_positive a then a' else raise a' in
  let the_apply_sgn = instantiate_fun_sgn kctx a_eff b_ret in
  let the_apply_xtor = instantiate_fun_apply kctx a_eff b_ret in
  match is_positive a with
    true ->
      (* case { apply[a', b_ret](x, k) ⇒ ⟨return(body') | k⟩ } *)
      CTm.Match (the_apply_sgn, [(the_apply_xtor, [x; k],
        CTm.Cut (b_ret, make_return body', CTm.Var k))])
  | false ->
      (* case { apply[↑a', b_ret](x', k) ⇒
           ⟨x' | case { pack[a'](x) ⇒ ⟨return(body') | k⟩ }⟩ } *)
      let x' = Ident.fresh () in
      CTm.Match (the_apply_sgn, [(the_apply_xtor, [x'; k],
        CTm.Cut (raise a',
          CTm.Var x',
          CTm.Match (instantiate_raise_sgn kctx a', [(instantiate_raise_pack kctx a', [x], 
            CTm.Cut (b_ret, make_return body', CTm.Var k))])))])

(* Encode type abstraction *)
and encode_all (defs: MTm.typed_definitions) (kctx: CTy.kind Ident.tbl) (ctx: MTy.typ Ident.tbl)
    (x: Ident.t) (k: MTy.kind) (body: MTm.typed_term) (body_ty: MTy.typ) : CTm.term =
  (* Λ(x:k). body where body: B
     This creates a codata value that responds to the instantiate destructor.
     
     For uniform CBV, type variables are positive. When someone instantiates
     with a negative type, it will have been raised, so we may need to unpack. *)
  let body' = map_term defs kctx ctx body in
  let body_ty' = map_typ body_ty in
  let k' = map_kind k in
  
  (* Return type: always lower[body_ty'] - no raise wrapper needed *)
  let b_ret = lower body_ty' in
  
  (* Return term: always return[body_ty'](body') *)
  let make_return body' = 
    CTm.Ctor (instantiate_lower_sgn kctx body_ty', instantiate_lower_return kctx body_ty', [body'])
  in
  
  (* Build the All signature for this type abstraction *)
  let all_sgn = Prim.all_sgn x k' in
  let inst_xtor = Prim.all_instantiate x k' in
  
  (* The instantiate destructor binds a continuation.
     comatch { instantiate(kont) => ⟨return(body') | kont⟩ } *)
  let kont = Ident.fresh () in
  CTm.Comatch (all_sgn, [(inst_xtor, [kont],
    CTm.Cut (b_ret, make_return body', CTm.Var kont))])

(* Encode match expression *)
and encode_match (defs: MTm.typed_definitions) (kctx: CTy.kind Ident.tbl) (ctx: MTy.typ Ident.tbl)
    (scrut: MTm.typed_term) (branches: MTm.typed_clause list) (result_ty: MTy.typ) : CTm.term =
  let scrut_ty = MTm.get_type scrut in
  let scrut' = map_term defs kctx ctx scrut in
  let result_ty' = map_typ result_ty in
  let sgn = match MTy.whnf Ident.emptytbl [] scrut_ty with
      MTy.Data sgn -> map_data sgn
    | _ -> failwith "Match on non-data type"
  in
  (* Build continuation that receives result *)
  let k = Ident.fresh () in
  let make_mu = if is_positive result_ty then
    (fun ty var cmd -> CTm.MuLhs (ty, var, cmd))
  else
    (fun ty var cmd -> CTm.MuRhs (ty, var, cmd))
  in
  let make_result_cut result k =
    if is_positive result_ty then
      CTm.Cut (result_ty', result, CTm.Var k)
    else
      CTm.Cut (result_ty', CTm.Var k, result)
  in
  let encoded_branches = List.map (fun (xtor, _ty_vars, tm_vars, body) ->
    let ctx' = List.fold_left2 (fun acc v ty ->
      Ident.add v ty acc
    ) ctx tm_vars (List.map (fun _ -> MTm.fresh ()) tm_vars) in
    let body' = map_term defs kctx ctx' body in
    (map_ctor xtor, tm_vars, make_result_cut body' k)
  ) branches in
  make_mu result_ty' k
    (CTm.Cut (map_typ scrut_ty, scrut', CTm.Match (sgn, encoded_branches)))

(* Encode new expression (codata introduction) *)
and encode_new (defs: MTm.typed_definitions) (kctx: CTy.kind Ident.tbl) (ctx: MTy.typ Ident.tbl)
    (branches: MTm.typed_clause list) (result_ty: MTy.typ) : CTm.term =
  let sgn = match MTy.whnf Ident.emptytbl [] result_ty with
      MTy.Code sgn -> map_code sgn
    | _ -> failwith "New with non-codata type"
  in
  let encoded_branches = List.map (fun (xtor, _ty_vars, tm_vars, body) ->
    let ctx' = List.fold_left2 (fun acc v ty ->
      Ident.add v ty acc
    ) ctx tm_vars (List.map (fun _ -> MTm.fresh ()) tm_vars) in
    let body' = map_term defs kctx ctx' body in
    let body_ty = MTm.get_type body in
    let body_ty' = map_typ body_ty in
    (* For codata, body provides the result to a continuation *)
    let k = List.hd (List.rev tm_vars) in
    let result_cut = if is_positive body_ty then
      CTm.Cut (body_ty', body', CTm.Var k)
    else
      CTm.Cut (body_ty', CTm.Var k, body')
    in
    (map_dtor xtor, tm_vars, result_cut)
  ) branches in
  CTm.Comatch (sgn, encoded_branches)

(* Encode constructor application (possibly partial) *)
and encode_ctor (defs: MTm.typed_definitions) (kctx: CTy.kind Ident.tbl) (ctx: MTy.typ Ident.tbl)
    (xtor: MTy.xtor) (args: MTm.typed_term list) (result_ty: MTy.typ) : CTm.term =
  (* Check if this is a partial application by comparing with xtor arity *)
  let expected_arity = List.length xtor.MTy.arguments in
  let actual_arity = List.length args in
  if actual_arity < expected_arity then
    (* Partial application: encode as lambda *)
    encode_partial_ctor defs kctx ctx xtor args result_ty
  else
    (* Full application: build the constructor directly.
      result_ty is Data(sgn) - already instantiated from type checking. *)
    let args' = List.map (map_term defs kctx ctx) args in
    let core_xtor = map_ctor xtor in
    let sgn = match result_ty with
        MTy.Data sgn -> map_data sgn
      | _ -> failwith "Constructor result type is not Data"
    in
    CTm.Ctor (sgn, core_xtor, args')

(* Encode partial constructor application as lambda *)
and encode_partial_ctor (defs: MTm.typed_definitions) (kctx: CTy.kind Ident.tbl) (ctx: MTy.typ Ident.tbl)
    (xtor: MTy.xtor) (args: MTm.typed_term list) (result_ty: MTy.typ) : CTm.term =
  let actual_arity = List.length args in
  
  (* Type parameters and existentials all become type abstractions.
    Both are universally quantified in partial application - the caller
    chooses the types (even for existentials, which are "caller chooses witness"). *)
  let type_params = xtor.MTy.parameters @ xtor.MTy.existentials in
  
  (* Use original names so references in xtor's argument types match *)
  let remaining_arg_tys = List.filteri (fun i _ -> i >= actual_arity) xtor.MTy.arguments in
  let fresh_var_tys = List.map (fun ty -> (Ident.fresh (), ty)) remaining_arg_tys in
  let fresh_typed_args = List.map (fun (v, ty) -> MTm.TypedVar (v, ty)) fresh_var_tys in
  let all_args = args @ fresh_typed_args in
  
  (* Compute the base type (after peeling off foralls and functions) *)
  let rec peel_foralls ty =
    match MTy.whnf Ident.emptytbl [] ty with
        MTy.All ((_, _), body) -> peel_foralls body
      | t -> t
  in
  let mono_ty = peel_foralls result_ty in
  let base_ty =
    match MTy.whnf Ident.emptytbl [] mono_ty with
      MTy.Fun (_, cod) -> 
        let rec get_codomain n ty = 
          if n <= 0 then ty
          else match MTy.whnf Ident.emptytbl [] ty with
              MTy.Fun (_, cod) -> get_codomain (n - 1) cod
            | _ -> ty
        in
        get_codomain (List.length remaining_arg_tys - 1) cod
    | ty -> ty
  in
  let full_ctor = MTm.TypedCtor (xtor, all_args, base_ty) in
  let with_lambdas = build_lambdas fresh_var_tys full_ctor in
  let with_alls = build_alls type_params with_lambdas in
  map_term defs kctx ctx with_alls

(* Encode destructor application (possibly partial) *)
and encode_dtor (defs: MTm.typed_definitions) (kctx: CTy.kind Ident.tbl) (ctx: MTy.typ Ident.tbl)
    (xtor: MTy.xtor) (args: MTm.typed_term list) (result_ty: MTy.typ) : CTm.term =
  (* For destructors, the last "argument" in the signature is the return type *)
  let all_args = xtor.MTy.arguments in
  let (regular_args, _codomain) = Utility.split_at_last all_args in
  let expected_arity = List.length regular_args in
  let actual_arity = List.length args in
  if actual_arity < expected_arity then
    (* Partial application: encode as lambda *)
    encode_partial_dtor defs kctx ctx xtor args result_ty
  else
    (* Full application: build the destructor.
      xtor.main is Code(sgn) - already instantiated from type checking. *)
    let args' = List.map (map_term defs kctx ctx) args in
    let core_xtor = map_dtor xtor in
    let sgn = match xtor.MTy.main with
        MTy.Code sgn -> map_code sgn
      | _ -> failwith "Destructor main type is not Code"
    in
    CTm.Dtor (sgn, core_xtor, args')

(* Encode partial destructor application as lambda *)
and encode_partial_dtor (defs: MTm.typed_definitions) (kctx: CTy.kind Ident.tbl) (ctx: MTy.typ Ident.tbl)
    (xtor: MTy.xtor) (args: MTm.typed_term list) (result_ty: MTy.typ) : CTm.term =
  let all_xtor_args = xtor.MTy.arguments in
  let (regular_args, _codomain) = Utility.split_at_last all_xtor_args in
  let actual_arity = List.length args in
  
  (* Type parameters and existentials become type abstractions *)
  let type_params = xtor.MTy.parameters @ xtor.MTy.existentials in
  
  let remaining_arg_tys = List.filteri (fun i _ -> i >= actual_arity) regular_args in
  let fresh_var_tys = List.map (fun ty -> (Ident.fresh (), ty)) remaining_arg_tys in
  let fresh_typed_args = List.map (fun (v, ty) -> MTm.TypedVar (v, ty)) fresh_var_tys in
  let all_term_args = args @ fresh_typed_args in
  
  (* Compute the base type (after peeling off foralls and functions) *)
  let rec peel_foralls ty =
    match MTy.whnf Ident.emptytbl [] ty with
        MTy.All ((_, _), body) -> peel_foralls body
      | t -> t
  in
  let mono_ty = peel_foralls result_ty in
  let base_ty = match MTy.whnf Ident.emptytbl [] mono_ty with
    | MTy.Fun (_, cod) -> 
        let rec get_codomain n ty = 
          if n <= 0 then ty
          else match MTy.whnf Ident.emptytbl [] ty with
            | MTy.Fun (_, cod) -> get_codomain (n - 1) cod
            | _ -> ty
        in
        get_codomain (List.length remaining_arg_tys - 1) cod
    | ty -> ty
  in
  let full_dtor = MTm.TypedDtor (xtor, all_term_args, base_ty) in
  let with_lambdas = build_lambdas fresh_var_tys full_dtor in
  let with_alls = build_alls type_params with_lambdas in
  map_term defs kctx ctx with_alls