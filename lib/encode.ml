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
let lower (ty: CTy.typ) : CTy.typ = App (Sgn Prim.lower_sgn, [ty])

(* Raise ↑(A) *)
let raise (ty: CTy.typ) : CTy.typ = App (Sgn Prim.raise_sgn, [ty])

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

(* ========================================================================= *)
(* Helpers for constructing instantiated signatures                          *)
(* ========================================================================= *)

(* Instantiate the Fun signature with concrete types a and b *)
let instantiate_fun_sgn (a: CTy.typ) (b: CTy.typ) : CTy.sgn_typ =
  { Prim.fun_sgn with
    CTy.parameters = []
  ; CTy.xtors = [
      { Prim.fun_apply with
        CTy.parameters = []
      ; CTy.arguments = [CTy.Lhs a; CTy.Rhs b]
      ; CTy.main = CTy.App (CTy.Sym (Sym.fun_t, Prim.fun_sgn_lazy), [a; b])
      }
    ]
  }

let instantiate_fun_apply (a: CTy.typ) (b: CTy.typ) : CTy.xtor =
  List.hd (instantiate_fun_sgn a b).xtors

(* Instantiate the Lower signature with concrete type a *)
let instantiate_lower_sgn (a: CTy.typ) : CTy.sgn_typ =
  { Prim.lower_sgn with
    CTy.parameters = []
  ; CTy.xtors = [
      { Prim.lower_return with
        CTy.parameters = []
      ; CTy.arguments = [CTy.Lhs a]
      ; CTy.main = CTy.App (CTy.Sym (Sym.lower_t, Prim.lower_sgn_lazy), [a])
      }
    ]
  }

let instantiate_lower_return (a: CTy.typ) : CTy.xtor =
  List.hd (instantiate_lower_sgn a).xtors

(* Instantiate the Raise signature with concrete type a *)
let instantiate_raise_sgn (a: CTy.typ) : CTy.sgn_typ =
  { Prim.raise_sgn with
    CTy.parameters = []
  ; CTy.xtors = [
      { Prim.raise_pack with
        CTy.parameters = []
      ; CTy.arguments = [CTy.Rhs a]
      ; CTy.main = CTy.App (CTy.Sym (Sym.raise_t, Prim.raise_sgn_lazy), [a])
      }
    ]
  }

let instantiate_raise_pack (a: CTy.typ) : CTy.xtor =
  List.hd (instantiate_raise_sgn a).xtors

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

(* Encode a term of a given type, wrapping appropriately for polarity.
  - Positive types produce Lhs (producers/values)
  - Negative types produce Rhs (consumers/computations)
  When we need a positive result from a negative term, we must wrap. *)

(* Helper: collect a chain of applications to a symbol.
   Returns Some (path, sym_ty, args) if tm is App(...App(Sym(path, sym_ty), arg1)..., argN)
   where args = [arg1; ...; argN] in application order. *)
let rec collect_symbol_app_chain (tm: MTm.typed_term) : (Path.t * MTy.typ * MTm.typed_term list) option =
  match tm with
  | MTm.TypedSym (path, ty) -> Some (path, ty, [])
  | MTm.TypedApp (f, arg, _) ->
      (match collect_symbol_app_chain f with
       | Some (path, sym_ty, args) -> Some (path, sym_ty, args @ [arg])
       | None -> None)
  | _ -> None

let rec map_term (defs: MTm.typed_definitions) (ctx: MTy.typ Ident.tbl) (tm: MTm.typed_term) : CTm.term =
  (* First, check if this is an application chain to a symbol *)
  match collect_symbol_app_chain tm with
  | Some (path, sym_ty, args) when args <> [] ->
      (* Application(s) to a symbol - handle the whole chain together *)
      encode_symbol_with_args defs ctx path sym_ty args (MTm.get_type tm)
  | _ ->
      (* Normal dispatch *)
      match tm with
        MTm.TypedInt n -> CTm.Lit n
      
      | MTm.TypedAdd (t1, t2) ->
          (* t1 + t2 where t1, t2 : Int
            Translates to: μL k. add(t1', t2', k) *)
          let t1' = map_term defs ctx t1 in
      let t2' = map_term defs ctx t2 in
      let k = Ident.fresh () in
      CTm.MuLhs (CTy.Ext Int, k, CTm.Add (t1', t2', CTm.Var k))
  
  | MTm.TypedVar (x, _ty) -> 
      CTm.Var x
  
  | MTm.TypedSym (path, ty) ->
      (* Symbol reference: look up definition and call it.
        If the type is polymorphic (All or Fun at top level), this is a
        partial application and should be encoded like a lambda. *)
      encode_sym defs ctx path ty
  
  | MTm.TypedApp (f, arg, result_ty) ->
      (* f arg where f : A → B, arg : A, result : B
        Application is: ⟨ctor_apply[A', B_ret](arg', k) | f'⟩
        wrapped in μL/μR based on whether B is positive/negative. *)
      let f_ty = MTm.get_type f in
      let (a, b) = match MTy.whnf Ident.emptytbl [] f_ty with
        | MTy.Fun (a, b) -> (a, b)
        | _ -> failwith "Application of non-function"
      in
      encode_app defs ctx f arg a b result_ty
  
  | MTm.TypedIns (t, ty_arg, _k, result_ty) ->
      (* t{ty_arg} where t : ∀(x:k). B, result : B[ty_arg/x]
        Similar to application but at the type level. *)
      let t_ty = MTm.get_type t in
      let ((_x, _), body) = match MTy.whnf Ident.emptytbl [] t_ty with
        | MTy.All ((x, k), body) -> ((x, k), body)
        | _ -> failwith "Type instantiation of non-forall"
      in
      encode_ins defs ctx t ty_arg body result_ty
  
  | MTm.TypedLam (x, a, body, _fun_ty) ->
      (* λx:A. body where body: B
        Encoding wraps body appropriately based on polarity of B. *)
      let ctx' = Ident.add x a ctx in
      let b = MTm.get_type body in
      encode_lam defs ctx' x a body b
  
  | MTm.TypedAll ((x, k), body, _all_ty) ->
      (* Λ(x:k). body - type abstraction
        Similar to lambda but binds a type variable. *)
      let body_ty = MTm.get_type body in
      encode_all defs ctx x k body body_ty
  
  | MTm.TypedLet (x, t1, t2, _ty) ->
      (* let x = t1 in t2 is equivalent to (λx:A. t2) t1 *)
      let a = MTm.get_type t1 in
      let b = MTm.get_type t2 in
      let lam = MTm.TypedLam (x, a, t2, MTy.Fun (a, b)) in
      let app = MTm.TypedApp (lam, t1, b) in
      map_term defs ctx app
  
  | MTm.TypedMatch (scrut, branches, result_ty) ->
      (* match scrut with { branches }
        Encoding: Cut(scrut_ty, scrut', Match(sgn, encoded_branches)) *)
      encode_match defs ctx scrut branches result_ty
  
  | MTm.TypedNew (branches, result_ty) ->
      (* new { branches } - codata introduction
        Encoding: Comatch(sgn, encoded_branches) *)
      encode_new defs ctx branches result_ty
  
  | MTm.TypedCtor (xtor, args, result_ty) ->
      (* Constructor application, possibly partial.
        If partial, encode like a lambda. *)
      encode_ctor defs ctx xtor args result_ty
  
  | MTm.TypedDtor (xtor, args, result_ty) ->
      (* Destructor application, possibly partial.
        If partial, encode like a lambda. *)
      encode_dtor defs ctx xtor args result_ty

(* Encode a symbol applied to some arguments.
   This handles the case where we have App(...App(Sym(path), arg1)..., argN).
   If fully saturated, emit a Call. If partial, wrap remaining args in lambdas. *)
and encode_symbol_with_args (defs: MTm.typed_definitions) (ctx: MTy.typ Ident.tbl) 
    (path: Path.t) (_sym_ty: MTy.typ) (args: MTm.typed_term list) (result_ty: MTy.typ) : CTm.term =
  match Path.find_opt path defs with
  | None -> failwith ("Undefined symbol: " ^ Path.name path)
  | Some def ->
      let num_term_args = List.length def.term_args in
      let provided = List.length args in
      if provided = num_term_args then
        (* Fully saturated: emit Call *)
        let encoded_args = List.map (map_term defs ctx) args in
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
        map_term defs ctx (build_lambdas fresh_vars inner)
      else
        failwith "Too many arguments to symbol"

(* Encode a bare symbol reference (not applied to any arguments).
   If the symbol expects arguments, build a lambda that takes them. *)
and encode_sym (defs: MTm.typed_definitions) (ctx: MTy.typ Ident.tbl) (path: Path.t) (ty: MTy.typ) : CTm.term =
  match Path.find_opt path defs with
  | None -> failwith ("Undefined symbol: " ^ Path.name path)
  | Some def ->
      let num_term_args = List.length def.term_args in
      let num_type_args = List.length def.type_args in
      if num_type_args > 0 then
        failwith "Type-polymorphic symbols not yet implemented"
      else if num_term_args = 0 then
        (* No arguments: just call *)
        CTm.MuLhs (map_typ ty, Ident.fresh (), CTm.Call (path, [], []))
      else
        (* Has term arguments: build eta-expansion as TypedLam and recurse.
           This will be picked up by collect_symbol_app_chain in the recursive call. *)
        let fresh_vars = List.map (fun (_, ty) -> (Ident.fresh (), ty)) def.term_args in
        let sym = MTm.TypedSym (path, ty) in
        let applied = List.fold_left2
          (fun acc (v, arg_ty) _param_ty ->
            let acc_ty = MTm.get_type acc in
            let result = match MTy.whnf Ident.emptytbl [] acc_ty with
              | MTy.Fun (_, cod) -> cod
              | _ -> failwith "Expected function type"
            in
            MTm.TypedApp (acc, MTm.TypedVar (v, arg_ty), result))
          sym
          fresh_vars
          def.term_args
        in
        map_term defs ctx (build_lambdas fresh_vars applied)

(* Encode function application *)
and encode_app (defs: MTm.typed_definitions) (ctx: MTy.typ Ident.tbl) 
    (f: MTm.typed_term) (arg: MTm.typed_term) 
    (a: MTy.typ) (b: MTy.typ) (_result_ty: MTy.typ) : CTm.term =
  let f' = map_term defs ctx f in
  let arg' = map_term defs ctx arg in
  let k = Ident.fresh () in
  let a' = map_typ a in
  let b' = map_typ b in
  (* Return type: ↓b' for positive b, ↓↑b' for negative b *)
  let b_ret = if is_positive b then lower b' else lower (raise b') in
  (* Choose Mu form based on whether result type is positive or negative *)
  let make_mu = if is_positive b then
    (fun ty var cmd -> CTm.MuLhs (ty, var, cmd))
  else
    (fun ty var cmd -> CTm.MuRhs (ty, var, cmd))
  in
  (* For positive a: arg' is used directly
     For negative a: wrap arg' in Pack *)
  let arg_term = if is_positive a then arg' else
    CTm.Ctor (instantiate_raise_sgn a', instantiate_raise_pack a', [arg'])
  in
  let a_eff = if is_positive a then a' else raise a' in
  let the_apply_sgn = instantiate_fun_sgn a_eff b_ret in
  let the_apply_xtor = instantiate_fun_apply a_eff b_ret in
  (* Inner cut between return value x and continuation k *)
  let x = Ident.fresh () in
  let make_inner_cut x k =
    if is_positive b then
      CTm.Cut (b', CTm.Var x, CTm.Var k)
    else
      CTm.Cut (b', CTm.Var k, CTm.Var x)
  in
  (* Continuation that receives the result *)
  let continuation =
    if is_positive b then
      CTm.Match (instantiate_lower_sgn b', [(instantiate_lower_return b', [x], make_inner_cut x k)])
    else
      let packed = Ident.fresh () in
      let raised_b = raise b' in
      CTm.Match (instantiate_lower_sgn raised_b, [(instantiate_lower_return raised_b, [packed],
        CTm.Cut (raised_b, CTm.Var packed, 
          CTm.Match (instantiate_raise_sgn b', [(instantiate_raise_pack b', [x], make_inner_cut x k)])))])
  in
  (* Build the application *)
  make_mu b' k
    (CTm.Cut (CTy.Sgn the_apply_sgn,
      CTm.Ctor (the_apply_sgn, the_apply_xtor, [arg_term; continuation]),
      f'))

(* Encode type instantiation *)
and encode_ins (defs: MTm.typed_definitions) (ctx: MTy.typ Ident.tbl)
    (t: MTm.typed_term) (ty_arg: MTy.typ) (_body: MTy.typ) (result_ty: MTy.typ) : CTm.term =
  (* t{A} where t : ∀(x:k). B, result : B[A/x]
     Similar to function application but at the type level.
     
     For uniform CBV, type variables are positive. If the type argument A is
     negative, we must raise it to make it positive before instantiation. *)
  let t' = map_term defs ctx t in
  let result_ty' = map_typ result_ty in
  let k = Ident.fresh () in
  
  (* Determine if we need to raise the type argument *)
  let ty_arg' = map_typ ty_arg in
  let ty_arg_eff = if is_positive ty_arg then ty_arg' else raise ty_arg' in
  
  (* The result type encoding follows the same pattern as function results *)
  let b_ret = if is_positive result_ty then lower result_ty' else lower (raise result_ty') in
  
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
  
  (* Continuation that receives the result *)
  let continuation =
    if is_positive result_ty then
      CTm.Match (instantiate_lower_sgn result_ty', [(instantiate_lower_return result_ty', [x], make_inner_cut x k)])
    else
      let packed = Ident.fresh () in
      let raised_b = raise result_ty' in
      CTm.Match (instantiate_lower_sgn raised_b, [(instantiate_lower_return raised_b, [packed],
        CTm.Cut (raised_b, CTm.Var packed, 
          CTm.Match (instantiate_raise_sgn result_ty', [(instantiate_raise_pack result_ty', [x], make_inner_cut x k)])))])
  in
  
  (* Build the Dtor for instantiate. 
     The All signature is parameterized by the (effective) type argument. *)
  let a_var = Ident.fresh () in
  let k' = CTy.Star in (* Simplified - should come from the All type *)
  let all_sgn = 
    { CTy.name = Sym.all_t k'
    ; CTy.parameters = []  (* instantiated *)
    ; CTy.xtors = [
        { CTy.name = Sym.all_instantiate k'
        ; CTy.parameters = []
        ; CTy.existentials = []
        ; CTy.arguments = [CTy.Rhs b_ret]  (* continuation expecting the result *)
        ; CTy.main = CTy.App (CTy.Sym (Sym.all_t k', Prim.all_sgn_lazy a_var k'), [ty_arg_eff])
        }
      ]
    }
  in
  let inst_xtor = List.hd all_sgn.xtors in
  
  make_mu result_ty' k
    (CTm.Cut (CTy.Sgn all_sgn,
      t',
      CTm.Dtor (all_sgn, inst_xtor, [continuation])))

(* Encode lambda abstraction *)  
and encode_lam (defs: MTm.typed_definitions) (ctx: MTy.typ Ident.tbl)
    (x: Ident.t) (a: MTy.typ) (body: MTm.typed_term) (b: MTy.typ) : CTm.term =
  let body' = map_term defs ctx body in
  let k = Ident.fresh () in
  let a' = map_typ a in
  let b' = map_typ b in
  (* Return type: ↓b' for positive b, ↓↑b' for negative b *)
  let b_ret = if is_positive b then lower b' else lower (raise b') in
  (* Return term construction based on polarity *)
  let make_return body' = 
    if is_positive b then
      CTm.Ctor (instantiate_lower_sgn b', instantiate_lower_return b', [body'])
    else
      let raised_b = raise b' in
      CTm.Ctor (instantiate_lower_sgn raised_b, instantiate_lower_return raised_b,
        [CTm.Ctor (instantiate_raise_sgn b', instantiate_raise_pack b', [body'])])
  in
  let a_eff = if is_positive a then a' else raise a' in
  let the_apply_sgn = instantiate_fun_sgn a_eff b_ret in
  let the_apply_xtor = instantiate_fun_apply a_eff b_ret in
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
          CTm.Match (instantiate_raise_sgn a', [(instantiate_raise_pack a', [x], 
            CTm.Cut (b_ret, make_return body', CTm.Var k))])))])

(* Encode type abstraction *)
and encode_all (defs: MTm.typed_definitions) (ctx: MTy.typ Ident.tbl)
    (x: Ident.t) (k: MTy.kind) (body: MTm.typed_term) (body_ty: MTy.typ) : CTm.term =
  (* Λ(x:k). body where body: B
     This creates a codata value that responds to the instantiate destructor.
     
     For uniform CBV, type variables are positive. When someone instantiates
     with a negative type, it will have been raised, so we may need to unpack. *)
  let body' = map_term defs ctx body in
  let body_ty' = map_typ body_ty in
  let k' = map_kind k in
  
  (* The return type handling follows the same pattern as lambdas *)
  let b_ret = if is_positive body_ty then lower body_ty' else lower (raise body_ty') in
  
  (* Return term construction based on polarity of body *)
  let make_return body' = 
    if is_positive body_ty then
      CTm.Ctor (instantiate_lower_sgn body_ty', instantiate_lower_return body_ty', [body'])
    else
      let raised_b = raise body_ty' in
      CTm.Ctor (instantiate_lower_sgn raised_b, instantiate_lower_return raised_b,
        [CTm.Ctor (instantiate_raise_sgn body_ty', instantiate_raise_pack body_ty', [body'])])
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
and encode_match (defs: MTm.typed_definitions) (ctx: MTy.typ Ident.tbl)
    (scrut: MTm.typed_term) (branches: MTm.typed_clause list) (result_ty: MTy.typ) : CTm.term =
  let scrut_ty = MTm.get_type scrut in
  let scrut' = map_term defs ctx scrut in
  let result_ty' = map_typ result_ty in
  let sgn = match MTy.whnf Ident.emptytbl [] scrut_ty with
    | MTy.Data sgn -> map_data sgn
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
    let body' = map_term defs ctx' body in
    let core_xtor =
      { CTy.name = xtor.MTy.name
      ; CTy.parameters = List.map (fun (id, k) -> (id, map_kind k)) xtor.MTy.parameters
      ; CTy.existentials = List.map (fun (id, k) -> (id, map_kind k)) xtor.MTy.existentials
      ; CTy.arguments = List.map (fun a -> CTy.Lhs (map_typ a)) xtor.MTy.arguments
      ; CTy.main = map_typ xtor.MTy.main
      }
    in
    (core_xtor, tm_vars, make_result_cut body' k)
  ) branches in
  make_mu result_ty' k
    (CTm.Cut (map_typ scrut_ty, scrut', CTm.Match (sgn, encoded_branches)))

(* Encode new expression (codata introduction) *)
and encode_new (defs: MTm.typed_definitions) (ctx: MTy.typ Ident.tbl)
    (branches: MTm.typed_clause list) (result_ty: MTy.typ) : CTm.term =
  let sgn = match MTy.whnf Ident.emptytbl [] result_ty with
    | MTy.Code sgn -> map_code sgn
    | _ -> failwith "New with non-codata type"
  in
  let encoded_branches = List.map (fun (xtor, _ty_vars, tm_vars, body) ->
    let ctx' = List.fold_left2 (fun acc v ty ->
      Ident.add v ty acc
    ) ctx tm_vars (List.map (fun _ -> MTm.fresh ()) tm_vars) in
    let body' = map_term defs ctx' body in
    let body_ty = MTm.get_type body in
    let body_ty' = map_typ body_ty in
    (* For codata, body provides the result to a continuation *)
    let result_cut = if is_positive body_ty then
      let k = List.hd (List.rev tm_vars) in
      CTm.Cut (body_ty', body', CTm.Var k)
    else
      let k = List.hd (List.rev tm_vars) in
      CTm.Cut (body_ty', CTm.Var k, body')
    in
    let (dtor_args, dtor_cod) = Utility.split_at_last xtor.MTy.arguments in
    let core_xtor =
      { CTy.name = xtor.MTy.name
      ; CTy.parameters = List.map (fun (id, k) -> (id, map_kind k)) xtor.MTy.parameters
      ; CTy.existentials = List.map (fun (id, k) -> (id, map_kind k)) xtor.MTy.existentials
      ; CTy.arguments = 
          List.map (fun a -> CTy.Lhs (map_typ a)) dtor_args @ [CTy.Rhs (map_typ dtor_cod)]
      ; CTy.main = map_typ xtor.MTy.main
      }
    in
    (core_xtor, tm_vars, result_cut)
  ) branches in
  CTm.Comatch (sgn, encoded_branches)

(* Encode constructor application (possibly partial) *)
and encode_ctor (defs: MTm.typed_definitions) (ctx: MTy.typ Ident.tbl)
    (xtor: MTy.xtor) (args: MTm.typed_term list) (result_ty: MTy.typ) : CTm.term =
  (* Check if this is a partial application by comparing with xtor arity *)
  let expected_arity = List.length xtor.MTy.arguments in
  let actual_arity = List.length args in
  if actual_arity < expected_arity then
    (* Partial application: encode as lambda *)
    encode_partial_ctor defs ctx xtor args result_ty
  else
    (* Full application: build the constructor directly.
       result_ty is Data(sgn) - already instantiated from type checking. *)
    let args' = List.map (map_term defs ctx) args in
    let core_xtor = map_ctor xtor in
    let sgn = match result_ty with
      | MTy.Data sgn -> map_data sgn
      | _ -> failwith "Constructor result type is not Data"
    in
    CTm.Ctor (sgn, core_xtor, args')

(* Encode partial constructor application as lambda *)
and encode_partial_ctor (defs: MTm.typed_definitions) (ctx: MTy.typ Ident.tbl)
    (xtor: MTy.xtor) (args: MTm.typed_term list) (result_ty: MTy.typ) : CTm.term =
  let actual_arity = List.length args in
  let remaining_arg_tys = List.filteri (fun i _ -> i >= actual_arity) xtor.MTy.arguments in
  let fresh_var_tys = List.map (fun ty -> (Ident.fresh (), ty)) remaining_arg_tys in
  let fresh_typed_args = List.map (fun (v, ty) -> MTm.TypedVar (v, ty)) fresh_var_tys in
  let all_args = args @ fresh_typed_args in
  (* Compute the base type (after all function types are peeled off) *)
  let base_ty = match MTy.whnf Ident.emptytbl [] result_ty with
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
  let full_ctor = MTm.TypedCtor (xtor, all_args, base_ty) in
  map_term defs ctx (build_lambdas fresh_var_tys full_ctor)

(* Encode destructor application (possibly partial) *)
and encode_dtor (defs: MTm.typed_definitions) (ctx: MTy.typ Ident.tbl)
    (xtor: MTy.xtor) (args: MTm.typed_term list) (result_ty: MTy.typ) : CTm.term =
  (* For destructors, the last "argument" in the signature is the return type *)
  let all_args = xtor.MTy.arguments in
  let (regular_args, _codomain) = Utility.split_at_last all_args in
  let expected_arity = List.length regular_args in
  let actual_arity = List.length args in
  if actual_arity < expected_arity then
    (* Partial application: encode as lambda *)
    encode_partial_dtor defs ctx xtor args result_ty
  else
    (* Full application: build the destructor.
       xtor.main is Code(sgn) - already instantiated from type checking. *)
    let args' = List.map (map_term defs ctx) args in
    let core_xtor = map_dtor xtor in
    let sgn = match xtor.MTy.main with
      | MTy.Code sgn -> map_code sgn
      | _ -> failwith "Destructor main type is not Code"
    in
    CTm.Dtor (sgn, core_xtor, args')

(* Encode partial destructor application as lambda *)
and encode_partial_dtor (defs: MTm.typed_definitions) (ctx: MTy.typ Ident.tbl)
    (xtor: MTy.xtor) (args: MTm.typed_term list) (result_ty: MTy.typ) : CTm.term =
  let all_args = xtor.MTy.arguments in
  let (regular_args, _codomain) = Utility.split_at_last all_args in
  let actual_arity = List.length args in
  let remaining_arg_tys = List.filteri (fun i _ -> i >= actual_arity) regular_args in
  let fresh_var_tys = List.map (fun ty -> (Ident.fresh (), ty)) remaining_arg_tys in
  let fresh_typed_args = List.map (fun (v, ty) -> MTm.TypedVar (v, ty)) fresh_var_tys in
  let all_term_args = args @ fresh_typed_args in
  let base_ty = match MTy.whnf Ident.emptytbl [] result_ty with
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
  map_term defs ctx (build_lambdas fresh_var_tys full_dtor)