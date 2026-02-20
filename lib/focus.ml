(**
  Module: Focus
  Description: Translates Core to Focused.
  
  This transformation canonicalizes Core sequent calculus terms into Focused form.
*)

open Common.Identifiers

module CB = Core.Types.CoreBase
module CTy = Core.Types.CoreTypes
module CTm = Core.Terms
module FB = Focused.Types.FocusedBase
module FTy = Focused.Types.FocusedTypes
module FTm = Focused.Terms

(* ========================================================================= *)
(* Substitution                                                              *)
(* ========================================================================= *)

module Sub = struct
  (** A substitution is a finite map from identifiers to identifiers *)
  type t = Ident.t Ident.tbl

  let empty : t = Ident.emptytbl

  let add (x: Ident.t) (y: Ident.t) (s: t) : t =
    Ident.add x y s

  let apply (s: t) (x: Ident.t) : Ident.t =
    match Ident.find_opt x s with
    | Some y -> y
    | None -> x
end

(* ========================================================================= *)
(* Type Encoding                                                             *)
(* ========================================================================= *)

let rec focus_type (t: CTy.typ) : FTy.typ =
  match t with
    CTy.Base _ -> FTy.Base FB.Typ
  | CTy.Arrow (t1, t2) -> FTy.Arrow (focus_type t1, focus_type t2)
  | CTy.Ext e -> FTy.Ext e
  | CTy.TVar v -> FTy.TVar v
  | CTy.TMeta v -> FTy.TMeta v
  | CTy.Sgn (p, args) -> FTy.Sgn (p, List.map focus_type args)
  | CTy.PromotedCtor (d, c, args) -> FTy.PromotedCtor (d, c, List.map focus_type args)
  | CTy.Fun (t1, t2) -> FTy.Fun (focus_type t1, focus_type t2)
  | CTy.Forall (x, k, body) -> FTy.Forall (x, focus_type k, focus_type body)
  | CTy.Raise t' -> FTy.Raise (focus_type t')
  | CTy.Lower t' -> FTy.Lower (focus_type t')

let focus_xtor (x: CTy.xtor) : FTy.xtor =
  let focus_xtor_arg (ty: CTy.chiral_typ) : FTy.chiral_typ =
    match ty with
      CB.Prd t -> FB.Prd (focus_type t)
    | CB.Cns t -> FB.Cns (focus_type t)
  in
  { name = x.name
  ; quantified = List.map (fun (v, k) -> (v, focus_type k)) x.quantified
  ; existentials = List.map (fun (v, k) -> (v, focus_type k)) x.existentials
  ; argument_types = List.map focus_xtor_arg x.argument_types
  ; main = focus_type x.main
  }

let focus_dec (d: CTy.dec) : FTy.dec =
  { name = d.name
  ; polarity = FB.Typ
  ; param_kinds = List.map focus_type d.param_kinds
  ; xtors = List.map focus_xtor d.xtors
  }

let focus_chiral (ct: CTy.chiral_typ) : FTy.chiral_typ =
  match ct with
    CB.Prd t -> FB.Prd (focus_type t)
  | CB.Cns t -> FB.Cns (focus_type t)

(* ========================================================================= *)
(* Target Language                                                           *)
(* ========================================================================= *)

(**
  Intermediate representation for focusing.
  
  This is analogous to simple.ml's Target module, but generalized for
  polymorphic types. The key distinctions:
  
  - LetCtor/LetDtor: bind a producer/consumer from an xtor application
  - LetMatch/LetComatch: bind a result from building a pattern/copattern
  - CutCtor/CutDtor: invoke an xtor against a continuation
  - CutMatch/CutComatch: invoke a pattern/copattern against a value
  
  Built-in types (Fun, Forall, Raise, Lower) have their own variants.
*)
module Target = struct

  type command =
    (* User-defined xtors *)
    | LetCtor of Path.t * Path.t * FTy.typ list * Ident.t list * Ident.t * command
    | LetDtor of Path.t * Path.t * FTy.typ list * Ident.t list * Ident.t * command
    | LetMatch of Path.t * branch list * Ident.t * command
    | LetComatch of Path.t * branch list * Ident.t * command
    | CutCtor of Path.t * Path.t * FTy.typ list * Ident.t list * Ident.t
    | CutDtor of Path.t * Path.t * FTy.typ list * Ident.t * Ident.t list
    | CutMatch of Path.t * Ident.t * branch list
    | CutComatch of Path.t * branch list * Ident.t
    (* Built-in Fun type *)
    | LetApply of FTy.typ * FTy.typ * Ident.t * Ident.t * Ident.t * command
    | LetNewFun of FTy.typ * FTy.typ * Ident.t * Ident.t * command * Ident.t * command
    | CutApply of FTy.typ * FTy.typ * Ident.t * Ident.t * Ident.t
    | CutNewFun of FTy.typ * FTy.typ * Ident.t * Ident.t * command * Ident.t
    (* Built-in Forall type *)
    | LetInstantiate of Ident.t * FTy.typ * FTy.typ * Ident.t * command
    | LetNewForall of Ident.t * FTy.typ * FTy.typ * command * Ident.t * command
    | CutInstantiate of Ident.t * FTy.typ * FTy.typ * Ident.t
    | CutNewForall of Ident.t * FTy.typ * FTy.typ * command * Ident.t
    (* Built-in Raise type *)
    | LetThunk of FTy.typ * Ident.t * Ident.t * command
    | LetMatchRaise of FTy.typ * Ident.t * command * Ident.t * command
    | CutThunk of FTy.typ * Ident.t * Ident.t
    | CutMatchRaise of FTy.typ * Ident.t * Ident.t * command
    (* Built-in Lower type *)
    | LetReturn of FTy.typ * Ident.t * Ident.t * command
    | LetNewLower of FTy.typ * Ident.t * command * Ident.t * command
    | CutReturn of FTy.typ * Ident.t * Ident.t
    | CutNewLower of FTy.typ * Ident.t * command * Ident.t
    (* Primitives *)
    | LetInt of int * Ident.t * command
    | CutInt of Ident.t * Ident.t
    | Add of Ident.t * Ident.t * Ident.t * command
    | Ifz of Ident.t * command * command
    | Call of Path.t * FTy.typ list * Ident.t list
    (* Terminals *)
    | Ret of FTy.typ * Ident.t
    | End

  and branch = Path.t * Ident.t list * Ident.t list * command

  (** Apply renaming to a command *)
  let rec rename_command (h: Sub.t) : command -> command = function
    | LetCtor (d, c, tys, args, x, cont) ->
        let x' = Ident.fresh () in
        LetCtor (d, c, tys, List.map (Sub.apply h) args, x',
          rename_command (Sub.add x x' h) cont)
    | LetDtor (d, c, tys, args, a, cont) ->
        let a' = Ident.fresh () in
        LetDtor (d, c, tys, List.map (Sub.apply h) args, a',
          rename_command (Sub.add a a' h) cont)
    | LetMatch (d, branches, x, cont) ->
        let x' = Ident.fresh () in
        LetMatch (d, List.map (rename_branch h) branches, x',
          rename_command (Sub.add x x' h) cont)
    | LetComatch (d, branches, a, cont) ->
        let a' = Ident.fresh () in
        LetComatch (d, List.map (rename_branch h) branches, a',
          rename_command (Sub.add a a' h) cont)
    | CutCtor (d, c, tys, args, a) ->
        CutCtor (d, c, tys, List.map (Sub.apply h) args, Sub.apply h a)
    | CutDtor (d, c, tys, x, args) ->
        CutDtor (d, c, tys, Sub.apply h x, List.map (Sub.apply h) args)
    | CutMatch (d, x, branches) ->
        CutMatch (d, Sub.apply h x, List.map (rename_branch h) branches)
    | CutComatch (d, branches, a) ->
        CutComatch (d, List.map (rename_branch h) branches, Sub.apply h a)
    (* Built-in Fun *)
    | LetApply (t1, t2, x, y, v, cont) ->
        let v' = Ident.fresh () in
        LetApply (t1, t2, Sub.apply h x, Sub.apply h y, v',
          rename_command (Sub.add v v' h) cont)
    | LetNewFun (t1, t2, x, k, body, v, cont) ->
        let x' = Ident.fresh () in
        let k' = Ident.fresh () in
        let v' = Ident.fresh () in
        LetNewFun (t1, t2, x', k', rename_command (Sub.add x x' (Sub.add k k' h)) body, v',
          rename_command (Sub.add v v' h) cont)
    | CutApply (t1, t2, x, y, a) ->
        CutApply (t1, t2, Sub.apply h x, Sub.apply h y, Sub.apply h a)
    | CutNewFun (t1, t2, x, k, body, a) ->
        let x' = Ident.fresh () in
        let k' = Ident.fresh () in
        CutNewFun (t1, t2, x', k', rename_command (Sub.add x x' (Sub.add k k' h)) body,
          Sub.apply h a)
    (* Built-in Forall *)
    | LetInstantiate (a, k, ty, v, cont) ->
        let v' = Ident.fresh () in
        LetInstantiate (a, k, ty, v', rename_command (Sub.add v v' h) cont)
    | LetNewForall (a, k, ty, body, v, cont) ->
        let a' = Ident.fresh () in
        let v' = Ident.fresh () in
        LetNewForall (a', k, ty, rename_command (Sub.add a a' h) body, v',
          rename_command (Sub.add v v' h) cont)
    | CutInstantiate (a, k, ty, v) ->
        CutInstantiate (a, k, ty, Sub.apply h v)
    | CutNewForall (a, k, ty, body, v) ->
        let a' = Ident.fresh () in
        CutNewForall (a', k, ty, rename_command (Sub.add a a' h) body, Sub.apply h v)
    (* Built-in Raise *)
    | LetThunk (t, x, v, cont) ->
        let v' = Ident.fresh () in
        LetThunk (t, Sub.apply h x, v', rename_command (Sub.add v v' h) cont)
    | LetMatchRaise (t, x, body, v, cont) ->
        let x' = Ident.fresh () in
        let v' = Ident.fresh () in
        LetMatchRaise (t, x', rename_command (Sub.add x x' h) body, v',
          rename_command (Sub.add v v' h) cont)
    | CutThunk (t, x, a) ->
        CutThunk (t, Sub.apply h x, Sub.apply h a)
    | CutMatchRaise (t, x, a, body) ->
        let x' = Ident.fresh () in
        CutMatchRaise (t, x', Sub.apply h a, rename_command (Sub.add x x' h) body)
    (* Built-in Lower *)
    | LetReturn (t, x, v, cont) ->
        let v' = Ident.fresh () in
        LetReturn (t, Sub.apply h x, v', rename_command (Sub.add v v' h) cont)
    | LetNewLower (t, k, body, v, cont) ->
        let k' = Ident.fresh () in
        let v' = Ident.fresh () in
        LetNewLower (t, k', rename_command (Sub.add k k' h) body, v',
          rename_command (Sub.add v v' h) cont)
    | CutReturn (t, x, a) ->
        CutReturn (t, Sub.apply h x, Sub.apply h a)
    | CutNewLower (t, k, body, a) ->
        let k' = Ident.fresh () in
        CutNewLower (t, k', rename_command (Sub.add k k' h) body, Sub.apply h a)
    (* Primitives *)
    | LetInt (n, x, cont) ->
        let x' = Ident.fresh () in
        LetInt (n, x', rename_command (Sub.add x x' h) cont)
    | CutInt (x, a) ->
        CutInt (Sub.apply h x, Sub.apply h a)
    | Add (x, y, k, cont) ->
        let k' = Ident.fresh () in
        Add (Sub.apply h x, Sub.apply h y, k', rename_command (Sub.add k k' h) cont)
    | Ifz (v, s1, s2) ->
        Ifz (Sub.apply h v, rename_command h s1, rename_command h s2)
    | Call (p, tys, args) ->
        Call (p, tys, List.map (Sub.apply h) args)
    | Ret (ty, x) -> Ret (ty, Sub.apply h x)
    | End -> End

  and rename_branch (h: Sub.t) ((xtor, ty_vars, tm_vars, body): branch) : branch =
    let tm_vars' = List.map (fun _ -> Ident.fresh ()) tm_vars in
    let h' = List.fold_left2 (fun acc p p' -> Sub.add p p' acc) h tm_vars tm_vars' in
    (xtor, ty_vars, tm_vars', rename_command h' body)

  (** Lookup and inline the body of a branch by xtor name *)
  let lookup_branch_body (branches: branch list) (xtor: Path.t)
      (arg_vars: Ident.t list) : command =
    match List.find_opt (fun (name, _, _, _) -> Path.equal name xtor) branches with
    | Some (_, _, params, body) ->
        let sub = List.fold_left2 (fun acc p v -> Sub.add p v acc)
                    Sub.empty params arg_vars in
        rename_command sub body
    | None -> End
end

(* ========================================================================= *)
(* Transformation: Core → Target                                             *)
(* ========================================================================= *)

module Transform = struct

  (** Generate fresh parameter names *)
  let fresh_params (ps: 'a list) : Ident.t list =
    List.map (fun _ -> Ident.fresh ()) ps

  (** Transform Core branches to Target branches *)
  let rec transform_branches (branches: CTm.branch list) (h: Sub.t) : Target.branch list =
    List.map (fun (xtor, ty_vars, tm_vars, body) ->
      let tm_vars' = fresh_params tm_vars in
      let h' = List.fold_left2 (fun acc p p' -> Sub.add p p' acc) h tm_vars tm_vars' in
      (xtor, ty_vars, tm_vars', transform_command body h')
    ) branches

  (** Bind a single term, calling continuation with the resulting variable *)
  and bind_term (term: CTm.term) (h: Sub.t)
      (k: Ident.t -> Target.command) : Target.command =
    match term with
    | CTm.Var x ->
        k (Sub.apply h x)

    | CTm.Ctor (d, c, tys, args) ->
        bind_terms args h (fun arg_vars ->
          let x = Ident.fresh () in
          Target.LetCtor (d, c, List.map focus_type tys, arg_vars, x, k x))

    | CTm.Dtor (d, c, tys, args) ->
        bind_terms args h (fun arg_vars ->
          let a = Ident.fresh () in
          Target.LetDtor (d, c, List.map focus_type tys, arg_vars, a, k a))

    | CTm.Match (d, bs) ->
        let x = Ident.fresh () in
        Target.LetMatch (d, transform_branches bs h, x, k x)

    | CTm.Comatch (d, bs) ->
        let a = Ident.fresh () in
        Target.LetComatch (d, transform_branches bs h, a, k a)

    | CTm.MuPrd (ty, x, s) ->
        (* μP(x, s) as a term: builds the xtor table for the type *)
        transform_mu_prd ty x s h k

    | CTm.MuCns (ty, a, s) ->
        (* μC(a, s) as a term: builds the xtor table for the type *)
        transform_mu_cns ty a s h k

    | CTm.NewFun (t1, t2, x, kv, body) ->
        let t1' = focus_type t1 in
        let t2' = focus_type t2 in
        let a = Ident.fresh () in
        let x' = Ident.fresh () in
        let kv' = Ident.fresh () in
        Target.LetNewFun (t1', t2', x', kv',
          transform_command body (Sub.add x x' (Sub.add kv kv' h)),
          a, k a)

    | CTm.ApplyDtor (t1, t2, arg, ret) ->
        let t1' = focus_type t1 in
        let t2' = focus_type t2 in
        bind_term arg h (fun arg_var ->
          bind_term ret h (fun ret_var ->
            let a = Ident.fresh () in
            Target.LetApply (t1', t2', arg_var, ret_var, a, k a)))

    | CTm.NewForall (a, knd, ty, body) ->
        let knd' = focus_type knd in
        let ty' = focus_type ty in
        let v = Ident.fresh () in
        let a' = Ident.fresh () in
        Target.LetNewForall (a', knd', ty',
          transform_command body (Sub.add a a' h),
          v, k v)

    | CTm.InstantiateDtor ty_arg ->
        let ty_arg' = focus_type ty_arg in
        let a = Ident.fresh () in
        (* InstantiateDtor needs special handling - it's just a destructor term *)
        Target.LetInstantiate (a, ty_arg', ty_arg', a, k a)

    | CTm.ThunkCtor (t, inner) ->
        let t' = focus_type t in
        bind_term inner h (fun inner_var ->
          let v = Ident.fresh () in
          Target.LetThunk (t', inner_var, v, k v))

    | CTm.MatchRaise (t, x, body) ->
        let t' = focus_type t in
        let v = Ident.fresh () in
        let x' = Ident.fresh () in
        Target.LetMatchRaise (t', x',
          transform_command body (Sub.add x x' h),
          v, k v)

    | CTm.NewLower (t, kv, body) ->
        let t' = focus_type t in
        let v = Ident.fresh () in
        let kv' = Ident.fresh () in
        Target.LetNewLower (t', kv',
          transform_command body (Sub.add kv kv' h),
          v, k v)

    | CTm.ReturnDtor (t, arg) ->
        let t' = focus_type t in
        bind_term arg h (fun arg_var ->
          let a = Ident.fresh () in
          Target.LetReturn (t', arg_var, a, k a))

    | CTm.Lit n ->
        let x = Ident.fresh () in
        Target.LetInt (n, x, k x)

  (** Transform MuPrd: builds appropriate xtor table for the type *)
  and transform_mu_prd (ty: CTy.typ) (x: Ident.t) (s: CTm.command) (h: Sub.t)
      (k: Ident.t -> Target.command) : Target.command =
    let _ty' = focus_type ty in
    match ty with
    | CTy.Sgn (d, _) ->
        (* For a signature type, we build a match with all branches *)
        let _bound = Ident.fresh () in
        Target.LetMatch (d,
          [(* TODO: need to look up dec to build branches *)],
          x,
          transform_command s (Sub.add x x h))

    | CTy.Fun (t1, t2) ->
        let t1' = focus_type t1 in
        let t2' = focus_type t2 in
        let bound = Ident.fresh () in
        let arg = Ident.fresh () in
        let ret = Ident.fresh () in
        let inner = Target.LetApply (t1', t2', arg, ret, bound, k bound) in
        Target.LetNewFun (t1', t2', arg, ret, inner, x,
          transform_command s (Sub.add x x h))

    | CTy.Raise t ->
        let t' = focus_type t in
        let bound = Ident.fresh () in
        let inner = Ident.fresh () in
        Target.LetMatchRaise (t', inner,
          Target.LetThunk (t', inner, bound, k bound),
          x,
          transform_command s (Sub.add x x h))

    | _ ->
        (* For other types, just transform the body *)
        let x' = Ident.fresh () in
        Target.LetInt (0, x', (* placeholder *)
          transform_command s (Sub.add x x' h))

  (** Transform MuCns: builds appropriate xtor table for the type *)
  and transform_mu_cns (ty: CTy.typ) (a: Ident.t) (s: CTm.command) (h: Sub.t)
      (k: Ident.t -> Target.command) : Target.command =
    let _ty' = focus_type ty in
    match ty with
    | CTy.Sgn (d, _) ->
        let _bound = Ident.fresh () in
        Target.LetComatch (d,
          [],  (* TODO: need to look up dec to build branches *)
          a,
          transform_command s (Sub.add a a h))

    | CTy.Fun (t1, t2) ->
        let t1' = focus_type t1 in
        let t2' = focus_type t2 in
        let bound = Ident.fresh () in
        let arg = Ident.fresh () in
        let ret = Ident.fresh () in
        let a' = Ident.fresh () in
        let inner_body = Target.LetApply (t1', t2', arg, ret, a',
          transform_command s (Sub.add a a' h)) in
        Target.LetNewFun (t1', t2', arg, ret, inner_body, bound, k bound)

    | CTy.Lower t ->
        let t' = focus_type t in
        let bound = Ident.fresh () in
        let inner = Ident.fresh () in
        Target.LetNewLower (t', inner,
          Target.LetReturn (t', inner, bound, k bound),
          a,
          transform_command s (Sub.add a a h))

    | _ ->
        let a' = Ident.fresh () in
        Target.LetInt (0, a',
          transform_command s (Sub.add a a' h))

  (** Bind multiple terms *)
  and bind_terms (terms: CTm.term list) (h: Sub.t)
      (k: Ident.t list -> Target.command) : Target.command =
    match terms with
    | [] -> k []
    | t :: rest ->
        bind_term t h (fun v ->
          bind_terms rest h (fun vs -> k (v :: vs)))

  (** Main transformation function *)
  and transform_command (cmd: CTm.command) (h: Sub.t) : Target.command =
    match cmd with
    (* Cut at a signature type *)
    | CTm.Cut (CTy.Sgn (d, _) as ty, lhs, rhs) ->
        transform_cut_sgn d ty lhs rhs h

    (* Cut at Fun type *)
    | CTm.Cut (CTy.Fun (t1, t2), lhs, rhs) ->
        transform_cut_fun t1 t2 lhs rhs h

    (* Cut at Forall type *)
    | CTm.Cut (CTy.Forall (a, k, body), lhs, rhs) ->
        transform_cut_forall a k body lhs rhs h

    (* Cut at Raise type *)
    | CTm.Cut (CTy.Raise t, lhs, rhs) ->
        transform_cut_raise t lhs rhs h

    (* Cut at Lower type *)
    | CTm.Cut (CTy.Lower t, lhs, rhs) ->
        transform_cut_lower t lhs rhs h

    (* Cut at Ext type (e.g., Int) *)
    | CTm.Cut (CTy.Ext _, lhs, rhs) ->
        bind_term lhs h (fun lhs_var ->
          bind_term rhs h (fun rhs_var ->
            Target.CutInt (lhs_var, rhs_var)))

    (* Other cuts - fallback *)
    | CTm.Cut (_, lhs, rhs) ->
        bind_term lhs h (fun lhs_var ->
          bind_term rhs h (fun rhs_var ->
            Target.CutInt (lhs_var, rhs_var)))

    | CTm.Call (path, tys, args) ->
        bind_terms args h (fun arg_vars ->
          Target.Call (path, List.map focus_type tys, arg_vars))

    | CTm.Add (m, n, k) ->
        bind_term m h (fun m_var ->
          bind_term n h (fun n_var ->
            bind_term k h (fun k_var ->
              let res = Ident.fresh () in
              Target.Add (m_var, n_var, res,
                Target.CutInt (res, k_var)))))

    | CTm.Ifz (cond, s1, s2) ->
        bind_term cond h (fun cond_var ->
          Target.Ifz (cond_var, transform_command s1 h, transform_command s2 h))

    | CTm.End -> Target.End

  (** Transform cut at signature type *)
  and transform_cut_sgn (d: Path.t) (_ty: CTy.typ) (lhs: CTm.term) (rhs: CTm.term)
      (h: Sub.t) : Target.command =
    match lhs, rhs with
    | CTm.Var x, CTm.Var _y ->
        (* ⟨x | y⟩ at Sgn: need to match on x and invoke y for each branch *)
        (* For now, simplified: *)
        Target.CutMatch (d, Sub.apply h x, [])

    | CTm.Var x, CTm.Match (_, bs) ->
        Target.CutMatch (d, Sub.apply h x, transform_branches bs h)

    | CTm.Var x, CTm.MuCns (_, a, r) ->
        transform_command r (Sub.add a (Sub.apply h x) h)

    | CTm.Ctor (_, c, tys, args), CTm.Var y ->
        bind_terms args h (fun arg_vars ->
          Target.CutCtor (d, c, List.map focus_type tys, arg_vars, Sub.apply h y))

    | CTm.Ctor (_, c, _tys, args), CTm.Match (_, bs) ->
        bind_terms args h (fun arg_vars ->
          Target.lookup_branch_body (transform_branches bs h) c arg_vars)

    | CTm.Ctor (_, c, tys, args), CTm.MuCns (_, a, r) ->
        bind_terms args h (fun arg_vars ->
          let a' = Ident.fresh () in
          Target.LetCtor (d, c, List.map focus_type tys, arg_vars, a',
            transform_command r (Sub.add a a' h)))

    | CTm.MuPrd (_, x, s), CTm.Var y ->
        transform_command s (Sub.add x (Sub.apply h y) h)

    | CTm.MuPrd (_, x, s), CTm.Match (_, bs) ->
        let x' = Ident.fresh () in
        Target.LetMatch (d, transform_branches bs h, x',
          transform_command s (Sub.add x x' h))

    | CTm.MuPrd (_, x, s), CTm.MuCns (_, _a, _r) ->
        let x' = Ident.fresh () in
        Target.LetMatch (d,
          (* Build branches that construct and pass to r *)
          [],
          x',
          transform_command s (Sub.add x x' h))

    | CTm.Comatch (_, bs), CTm.Var y ->
        Target.CutComatch (d, transform_branches bs h, Sub.apply h y)

    | CTm.Comatch (_, bs), CTm.Dtor (_, c, _tys, args) ->
        bind_terms args h (fun arg_vars ->
          Target.lookup_branch_body (transform_branches bs h) c arg_vars)

    | CTm.Comatch (_, bs), CTm.MuCns (_, a, r) ->
        let a' = Ident.fresh () in
        Target.LetComatch (d, transform_branches bs h, a',
          transform_command r (Sub.add a a' h))

    | CTm.MuPrd (_, x, s), CTm.Dtor (_, c, tys, args) ->
        bind_terms args h (fun arg_vars ->
          let x' = Ident.fresh () in
          Target.LetDtor (d, c, List.map focus_type tys, arg_vars, x',
            transform_command s (Sub.add x x' h)))

    | CTm.Var x, CTm.Dtor (_, c, tys, args) ->
        bind_terms args h (fun arg_vars ->
          Target.CutDtor (d, c, List.map focus_type tys, Sub.apply h x, arg_vars))

    | _ ->
        bind_term lhs h (fun lhs_var ->
          bind_term rhs h (fun _rhs_var ->
            Target.CutMatch (d, lhs_var, [])))

  (** Transform cut at Fun type *)
  and transform_cut_fun (t1: CTy.typ) (t2: CTy.typ) (lhs: CTm.term) (rhs: CTm.term)
      (h: Sub.t) : Target.command =
    let t1' = focus_type t1 in
    let t2' = focus_type t2 in
    match lhs, rhs with
    | CTm.Var x, CTm.Var y ->
        let arg = Ident.fresh () in
        let ret = Ident.fresh () in
        Target.CutNewFun (t1', t2', arg, ret,
          Target.CutApply (t1', t2', arg, ret, Sub.apply h x),
          Sub.apply h y)

    | CTm.Var x, CTm.ApplyDtor (_, _, arg, ret) ->
        bind_term arg h (fun arg_var ->
          bind_term ret h (fun ret_var ->
            Target.CutApply (t1', t2', arg_var, ret_var, Sub.apply h x)))

    | CTm.Var x, CTm.MuCns (_, a, r) ->
        transform_command r (Sub.add a (Sub.apply h x) h)

    | CTm.NewFun (_, _, x, k, body), CTm.Var y ->
        let x' = Ident.fresh () in
        let k' = Ident.fresh () in
        Target.CutNewFun (t1', t2', x', k',
          transform_command body (Sub.add x x' (Sub.add k k' h)),
          Sub.apply h y)

    | CTm.NewFun (_, _, x, kv, body), CTm.ApplyDtor (_, _, arg, ret) ->
        bind_term arg h (fun arg_var ->
          bind_term ret h (fun ret_var ->
            let h' = Sub.add x arg_var (Sub.add kv ret_var h) in
            transform_command body h'))

    | CTm.NewFun (_, _, x, kv, body), CTm.MuCns (_, a, r) ->
        let x' = Ident.fresh () in
        let kv' = Ident.fresh () in
        let a' = Ident.fresh () in
        let inner_body = transform_command body (Sub.add x x' (Sub.add kv kv' h)) in
        Target.LetNewFun (t1', t2', x', kv', inner_body, a',
          transform_command r (Sub.add a a' h))

    | CTm.MuPrd (_, x, s), CTm.Var y ->
        transform_command s (Sub.add x (Sub.apply h y) h)

    | CTm.MuPrd (_, x, s), CTm.ApplyDtor (_, _, arg, ret) ->
        bind_term arg h (fun arg_var ->
          bind_term ret h (fun ret_var ->
            let x' = Ident.fresh () in
            Target.LetApply (t1', t2', arg_var, ret_var, x',
              transform_command s (Sub.add x x' h))))

    | CTm.MuPrd (_, x, s), CTm.MuCns (_, a, r) ->
        let arg = Ident.fresh () in
        let ret = Ident.fresh () in
        let a' = Ident.fresh () in
        let x' = Ident.fresh () in
        let inner_body = Target.LetApply (t1', t2', arg, ret, a',
            transform_command r (Sub.add a a' h)) in
        Target.LetNewFun (t1', t2', arg, ret, inner_body, x',
          transform_command s (Sub.add x x' h))

    | _ ->
        bind_term lhs h (fun lhs_var ->
          bind_term rhs h (fun rhs_var ->
            let arg = Ident.fresh () in
            let ret = Ident.fresh () in
            Target.CutNewFun (t1', t2', arg, ret,
              Target.CutApply (t1', t2', arg, ret, lhs_var),
              rhs_var)))

  (** Transform cut at Forall type *)
  and transform_cut_forall (a: Ident.t) (k: CTy.typ) (body: CTy.typ)
      (lhs: CTm.term) (rhs: CTm.term) (h: Sub.t) : Target.command =
    let k' = focus_type k in
    let body' = focus_type body in
    match lhs, rhs with
    | CTm.Var x, CTm.Var y ->
        let a' = Ident.fresh () in
        Target.CutNewForall (a', k', body',
          Target.CutInstantiate (a', k', body', Sub.apply h x),
          Sub.apply h y)

    | CTm.Var x, CTm.InstantiateDtor ty_arg ->
        let ty_arg' = focus_type ty_arg in
        Target.CutInstantiate (a, ty_arg', body', Sub.apply h x)

    | CTm.Var x, CTm.MuCns (_, av, r) ->
        transform_command r (Sub.add av (Sub.apply h x) h)

    | CTm.NewForall (_, _, _, cmd), CTm.InstantiateDtor _ty_arg ->
        (* Substitute type argument into body *)
        transform_command cmd h

    | CTm.NewForall (av, _, _, cmd), CTm.MuCns (_, bv, r) ->
        let v = Ident.fresh () in
        let av' = Ident.fresh () in
        Target.LetNewForall (av', k', body',
          transform_command cmd (Sub.add av av' h),
          v,
          transform_command r (Sub.add bv v h))

    | CTm.MuPrd (_, x, s), CTm.Var y ->
        transform_command s (Sub.add x (Sub.apply h y) h)

    | _ ->
        bind_term lhs h (fun lhs_var ->
          bind_term rhs h (fun rhs_var ->
            let a' = Ident.fresh () in
            Target.CutNewForall (a', k', body',
              Target.CutInstantiate (a', k', body', lhs_var),
              rhs_var)))

  (** Transform cut at Raise type *)
  and transform_cut_raise (t: CTy.typ) (lhs: CTm.term) (rhs: CTm.term)
      (h: Sub.t) : Target.command =
    let t' = focus_type t in
    match lhs, rhs with
    | CTm.Var x, CTm.Var y ->
        let inner = Ident.fresh () in
        Target.CutMatchRaise (t', inner, Sub.apply h y,
          Target.CutThunk (t', inner, Sub.apply h x))

    | CTm.Var x, CTm.MatchRaise (_, v, body) ->
        let v' = Ident.fresh () in
        Target.CutMatchRaise (t', v', Sub.apply h x,
          transform_command body (Sub.add v v' h))

    | CTm.Var x, CTm.MuCns (_, a, r) ->
        transform_command r (Sub.add a (Sub.apply h x) h)

    | CTm.ThunkCtor (_, inner), CTm.Var y ->
        bind_term inner h (fun inner_var ->
          Target.CutThunk (t', inner_var, Sub.apply h y))

    | CTm.ThunkCtor (_, inner), CTm.MatchRaise (_, v, body) ->
        bind_term inner h (fun inner_var ->
          transform_command body (Sub.add v inner_var h))

    | CTm.ThunkCtor (_, inner), CTm.MuCns (_, a, r) ->
        bind_term inner h (fun inner_var ->
          let a' = Ident.fresh () in
          Target.LetThunk (t', inner_var, a',
            transform_command r (Sub.add a a' h)))

    | CTm.MuPrd (_, x, s), CTm.Var y ->
        transform_command s (Sub.add x (Sub.apply h y) h)

    | CTm.MuPrd (_, x, s), CTm.MatchRaise (_, v, body) ->
        let x' = Ident.fresh () in
        let v' = Ident.fresh () in
        Target.LetMatchRaise (t', v',
          transform_command body (Sub.add v v' h),
          x',
          transform_command s (Sub.add x x' h))

    | _ ->
        bind_term lhs h (fun lhs_var ->
          bind_term rhs h (fun rhs_var ->
            let inner = Ident.fresh () in
            Target.CutMatchRaise (t', inner, rhs_var,
              Target.CutThunk (t', inner, lhs_var))))

  (** Transform cut at Lower type *)
  and transform_cut_lower (t: CTy.typ) (lhs: CTm.term) (rhs: CTm.term)
      (h: Sub.t) : Target.command =
    let t' = focus_type t in
    match lhs, rhs with
    | CTm.Var x, CTm.Var y ->
        let inner = Ident.fresh () in
        Target.CutNewLower (t', inner,
          Target.CutReturn (t', inner, Sub.apply h x),
          Sub.apply h y)

    | CTm.Var x, CTm.ReturnDtor (_, arg) ->
        bind_term arg h (fun arg_var ->
          Target.CutReturn (t', arg_var, Sub.apply h x))

    | CTm.Var x, CTm.MuCns (_, a, r) ->
        transform_command r (Sub.add a (Sub.apply h x) h)

    | CTm.NewLower (_, k, body), CTm.Var y ->
        let k' = Ident.fresh () in
        Target.CutNewLower (t', k',
          transform_command body (Sub.add k k' h),
          Sub.apply h y)

    | CTm.NewLower (_, k, body), CTm.ReturnDtor (_, arg) ->
        bind_term arg h (fun arg_var ->
          transform_command body (Sub.add k arg_var h))

    | CTm.NewLower (_, k, body), CTm.MuCns (_, a, r) ->
        let k' = Ident.fresh () in
        let a' = Ident.fresh () in
        Target.LetNewLower (t', k',
          transform_command body (Sub.add k k' h),
          a',
          transform_command r (Sub.add a a' h))

    | CTm.MuPrd (_, x, s), CTm.Var y ->
        transform_command s (Sub.add x (Sub.apply h y) h)

    | CTm.MuPrd (_, x, s), CTm.ReturnDtor (_, arg) ->
        bind_term arg h (fun arg_var ->
          let x' = Ident.fresh () in
          Target.LetReturn (t', arg_var, x',
            transform_command s (Sub.add x x' h)))

    | _ ->
        bind_term lhs h (fun lhs_var ->
          bind_term rhs h (fun rhs_var ->
            let inner = Ident.fresh () in
            Target.CutNewLower (t', inner,
              Target.CutReturn (t', inner, lhs_var),
              rhs_var)))

  (** Entry point *)
  let transform (cmd: CTm.command) : Target.command =
    transform_command cmd Sub.empty
end

(* ========================================================================= *)
(* Collapse: Target → Focused                                                *)
(* ========================================================================= *)

module Collapse = struct

  (** Collapse a Target branch to a Focused branch *)
  let rec collapse_branch ((xtor, ty_vars, tm_vars, body): Target.branch) : FTm.branch =
    (xtor, ty_vars, tm_vars, collapse_command body)

  (** Main collapse transformation *)
  and collapse_command : Target.command -> FTm.command = function
    (* User-defined xtors - Let becomes Let, LetMatch becomes New *)
    | Target.LetCtor (d, c, tys, args, x, cont) ->
        FTm.Let (x, d, c, tys, args, collapse_command cont)
    | Target.LetDtor (d, c, tys, args, a, cont) ->
        FTm.Let (a, d, c, tys, args, collapse_command cont)
    | Target.LetMatch (d, branches, x, cont) ->
        FTm.New (d, x, List.map collapse_branch branches, collapse_command cont)
    | Target.LetComatch (d, branches, a, cont) ->
        FTm.New (d, a, List.map collapse_branch branches, collapse_command cont)

    (* User-defined xtors - Cut becomes Switch/Invoke *)
    | Target.CutCtor (d, c, tys, args, a) ->
        FTm.Invoke (a, d, c, tys, args)
    | Target.CutDtor (d, c, tys, x, args) ->
        FTm.Invoke (x, d, c, tys, args)
    | Target.CutMatch (d, x, branches) ->
        FTm.Switch (d, x, List.map collapse_branch branches)
    | Target.CutComatch (d, branches, a) ->
        FTm.Switch (d, a, List.map collapse_branch branches)

    (* Built-in Fun *)
    | Target.LetApply (t1, t2, x, y, v, cont) ->
        FTm.LetApply (v, t1, t2, x, y, collapse_command cont)
    | Target.LetNewFun (t1, t2, x, k, body, v, cont) ->
        FTm.NewFun (v, t1, t2, x, k, collapse_command body, collapse_command cont)
    | Target.CutApply (t1, t2, x, y, a) ->
        FTm.InvokeApply (a, t1, t2, x, y)
    | Target.CutNewFun (t1, t2, x, k, body, a) ->
        FTm.SwitchFun (a, t1, t2, x, k, collapse_command body)

    (* Built-in Forall *)
    | Target.LetInstantiate (a, k, ty, v, cont) ->
        FTm.LetInstantiate (v, a, k, ty, collapse_command cont)
    | Target.LetNewForall (a, k, _ty, body, v, cont) ->
        FTm.NewForall (v, a, k, collapse_command body, collapse_command cont)
    | Target.CutInstantiate (_a, k, ty, v) ->
        FTm.InvokeInstantiate (v, ty, k)
    | Target.CutNewForall (a, k, _ty, body, v) ->
        FTm.SwitchForall (v, a, k, collapse_command body)

    (* Built-in Raise *)
    | Target.LetThunk (t, x, v, cont) ->
        FTm.LetThunk (v, t, x, collapse_command cont)
    | Target.LetMatchRaise (t, x, body, v, cont) ->
        FTm.NewRaise (v, t, x, collapse_command body, collapse_command cont)
    | Target.CutThunk (t, x, a) ->
        FTm.InvokeThunk (a, t, x)
    | Target.CutMatchRaise (t, x, a, body) ->
        FTm.SwitchRaise (a, t, x, collapse_command body)

    (* Built-in Lower *)
    | Target.LetReturn (t, x, v, cont) ->
        FTm.LetReturn (v, t, x, collapse_command cont)
    | Target.LetNewLower (t, k, body, v, cont) ->
        FTm.NewLower (v, t, k, collapse_command body, collapse_command cont)
    | Target.CutReturn (t, x, a) ->
        FTm.InvokeReturn (a, t, x)
    | Target.CutNewLower (t, k, body, a) ->
        FTm.SwitchLower (a, t, k, collapse_command body)

    (* Primitives *)
    | Target.LetInt (n, x, cont) ->
        FTm.Lit (n, x, collapse_command cont)
    | Target.CutInt (x, k) ->
        FTm.Axiom (FTy.Ext Common.Types.Int, x, k)
    | Target.Add (x, y, k, cont) ->
        FTm.Add (x, y, k, collapse_command cont)
    | Target.Ifz (v, s1, s2) ->
        FTm.Ifz (v, collapse_command s1, collapse_command s2)
    | Target.Call (_path, _tys, _args) ->
        (* Calls need a return continuation - for now return End *)
        FTm.End

    | Target.Ret (ty, x) -> FTm.Ret (ty, x)
    | Target.End -> FTm.End

  (** Full pipeline: Core → Focused *)
  let focus_command (cmd: CTm.command) : FTm.command =
    collapse_command (Transform.transform cmd)
end

(** Top-level entry point *)
let focus_command = Collapse.focus_command