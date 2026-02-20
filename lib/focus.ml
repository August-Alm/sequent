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

(** Check if a focused type is negative (codata: Fun, Forall, Lower).
    Following simple.ml: negative types flip chirality during collapse. *)
let is_negative (t: FTy.typ) : bool =
  match t with
  | FTy.Fun _ | FTy.Forall _ | FTy.Lower _ -> true
  | _ -> false

(** Flip chirality for negative types, like simple.ml's collapse_chiral.
    Prd (neg) → Cns, Cns (neg) → Prd. Positive types unchanged. *)
let collapse_chiral (ct: FTy.chiral_typ) : FTy.chiral_typ =
  match ct with
  | FB.Prd t when is_negative t -> FB.Cns t
  | FB.Cns t when is_negative t -> FB.Prd t
  | _ -> ct

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

  (* Target uses CTy (polarized types) so collapse_chiral can flip for negative types. *)
  type command =
    (* User-defined xtors *)
    | LetCtor of Path.t * Path.t * CTy.typ list * Ident.t list * Ident.t * command
    | LetDtor of Path.t * Path.t * CTy.typ list * Ident.t list * Ident.t * command
    | LetMatch of Path.t * branch list * Ident.t * command
    | LetComatch of Path.t * branch list * Ident.t * command
    | CutCtor of Path.t * Path.t * CTy.typ list * Ident.t list * Ident.t
    | CutDtor of Path.t * Path.t * CTy.typ list * Ident.t * Ident.t list
    | CutMatch of Path.t * Ident.t * branch list
    | CutComatch of Path.t * branch list * Ident.t
    (* Built-in Fun type *)
    | LetApply of CTy.typ * CTy.typ * Ident.t * Ident.t * Ident.t * command
    | LetNewFun of CTy.typ * CTy.typ * Ident.t * Ident.t * command * Ident.t * command
    | CutApply of CTy.typ * CTy.typ * Ident.t * Ident.t * Ident.t
    | CutNewFun of CTy.typ * CTy.typ * Ident.t * Ident.t * command * Ident.t
    (* Built-in Forall type *)
    | LetInstantiate of Ident.t * CTy.typ * CTy.typ * Ident.t * command
    | LetNewForall of Ident.t * CTy.typ * CTy.typ * command * Ident.t * command
    | CutInstantiate of Ident.t * CTy.typ * CTy.typ * Ident.t
    | CutNewForall of Ident.t * CTy.typ * CTy.typ * command * Ident.t
    (* Built-in Raise type *)
    | LetThunk of CTy.typ * Ident.t * Ident.t * command
    | LetMatchRaise of CTy.typ * Ident.t * command * Ident.t * command
    | CutThunk of CTy.typ * Ident.t * Ident.t
    | CutMatchRaise of CTy.typ * Ident.t * Ident.t * command
    (* Built-in Lower type *)
    | LetReturn of CTy.typ * Ident.t * Ident.t * command
    | LetNewLower of CTy.typ * Ident.t * command * Ident.t * command
    | CutReturn of CTy.typ * Ident.t * Ident.t
    | CutNewLower of CTy.typ * Ident.t * command * Ident.t
    (* Primitives *)
    | LetInt of int * Ident.t * command
    | CutInt of Ident.t * Ident.t
    | Add of Ident.t * Ident.t * Ident.t * command
    | Ifz of Ident.t * command * command
    | Call of Path.t * CTy.typ list * Ident.t list
    (* Terminals *)
    | Ret of CTy.typ * Ident.t
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

  (** Replace CutInt(v, target) with the result of k(v) in a command.
      This is used for MuPrd/MuCns at Ext types where we need to capture
      the value flowing to a continuation and pass it to k. *)
  let rec replace_cutint (target: Ident.t) (k: Ident.t -> command) : command -> command =
    function
    | CutInt (v, a) when Ident.equal a target -> k v
    | CutInt (v, a) -> CutInt (v, a)
    | LetInt (n, x, cont) -> LetInt (n, x, replace_cutint target k cont)
    | Add (x, y, r, cont) -> Add (x, y, r, replace_cutint target k cont)
    | LetCtor (d, c, tys, args, x, cont) ->
        LetCtor (d, c, tys, args, x, replace_cutint target k cont)
    | LetDtor (d, c, tys, args, a, cont) ->
        LetDtor (d, c, tys, args, a, replace_cutint target k cont)
    | LetMatch (d, branches, x, cont) ->
        LetMatch (d, List.map (replace_cutint_branch target k) branches, x,
          replace_cutint target k cont)
    | LetComatch (d, branches, a, cont) ->
        LetComatch (d, List.map (replace_cutint_branch target k) branches, a,
          replace_cutint target k cont)
    | LetApply (t1, t2, x, y, v, cont) ->
        LetApply (t1, t2, x, y, v, replace_cutint target k cont)
    | LetNewFun (t1, t2, x, kv, body, v, cont) ->
        LetNewFun (t1, t2, x, kv, replace_cutint target k body, v,
          replace_cutint target k cont)
    | LetInstantiate (a, knd, ty, v, cont) ->
        LetInstantiate (a, knd, ty, v, replace_cutint target k cont)
    | LetNewForall (a, knd, ty, body, v, cont) ->
        LetNewForall (a, knd, ty, replace_cutint target k body, v,
          replace_cutint target k cont)
    | LetThunk (t, x, v, cont) ->
        LetThunk (t, x, v, replace_cutint target k cont)
    | LetMatchRaise (t, x, body, v, cont) ->
        LetMatchRaise (t, x, replace_cutint target k body, v,
          replace_cutint target k cont)
    | LetReturn (t, x, v, cont) ->
        LetReturn (t, x, v, replace_cutint target k cont)
    | LetNewLower (t, kv, body, v, cont) ->
        LetNewLower (t, kv, replace_cutint target k body, v,
          replace_cutint target k cont)
    | Ifz (v, s1, s2) ->
        Ifz (v, replace_cutint target k s1, replace_cutint target k s2)
    | cmd -> cmd  (* CutCtor, CutDtor, CutMatch, CutComatch, CutApply, etc. don't need recursion *)

  and replace_cutint_branch (target: Ident.t) (k: Ident.t -> command)
      ((xtor, ty_vars, tm_vars, body): branch) : branch =
    (xtor, ty_vars, tm_vars, replace_cutint target k body)
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
          Target.LetCtor (d, c, tys, arg_vars, x, k x))

    | CTm.Dtor (d, c, tys, args) ->
        bind_terms args h (fun arg_vars ->
          let a = Ident.fresh () in
          Target.LetDtor (d, c, tys, arg_vars, a, k a))

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
        (* Target uses CTy types directly (no conversion to FTy) *)
        let a = Ident.fresh () in
        let x' = Ident.fresh () in
        let kv' = Ident.fresh () in
        Target.LetNewFun (t1, t2, x', kv',
          transform_command body (Sub.add x x' (Sub.add kv kv' h)),
          a, k a)

    | CTm.ApplyDtor (t1, t2, arg, ret) ->
        (* Target uses CTy types directly *)
        bind_term arg h (fun arg_var ->
          bind_term ret h (fun ret_var ->
            let a = Ident.fresh () in
            Target.LetApply (t1, t2, arg_var, ret_var, a, k a)))

    | CTm.NewForall (a, knd, ty, body) ->
        (* Target uses CTy types directly *)
        let v = Ident.fresh () in
        let a' = Ident.fresh () in
        Target.LetNewForall (a', knd, ty,
          transform_command body (Sub.add a a' h),
          v, k v)

    | CTm.InstantiateDtor ty_arg ->
        let a = Ident.fresh () in
        (* InstantiateDtor needs special handling - it's just a destructor term *)
        Target.LetInstantiate (a, ty_arg, ty_arg, a, k a)

    | CTm.ThunkCtor (t, inner) ->
        bind_term inner h (fun inner_var ->
          let v = Ident.fresh () in
          Target.LetThunk (t, inner_var, v, k v))

    | CTm.MatchRaise (t, x, body) ->
        let v = Ident.fresh () in
        let x' = Ident.fresh () in
        Target.LetMatchRaise (t, x',
          transform_command body (Sub.add x x' h),
          v, k v)

    | CTm.NewLower (t, kv, body) ->
        let v = Ident.fresh () in
        let kv' = Ident.fresh () in
        Target.LetNewLower (t, kv',
          transform_command body (Sub.add kv kv' h),
          v, k v)

    | CTm.ReturnDtor (t, arg) ->
        bind_term arg h (fun arg_var ->
          let a = Ident.fresh () in
          Target.LetReturn (t, arg_var, a, k a))

    | CTm.Lit n ->
        let x = Ident.fresh () in
        Target.LetInt (n, x, k x)

  (** Transform MuPrd: builds appropriate xtor table for the type *)
  and transform_mu_prd (ty: CTy.typ) (x: Ident.t) (s: CTm.command) (h: Sub.t)
      (k: Ident.t -> Target.command) : Target.command =
    (* Target uses CTy types directly (no conversion to FTy) *)
    match ty with
    | CTy.Sgn (d, _) ->
        (* For a signature type, we build a match with all branches *)
        let _bound = Ident.fresh () in
        Target.LetMatch (d,
          [(* TODO: need to look up dec to build branches *)],
          x,
          transform_command s (Sub.add x x h))

    | CTy.Fun (t1, t2) ->
        let bound = Ident.fresh () in
        let arg = Ident.fresh () in
        let ret = Ident.fresh () in
        let inner = Target.LetApply (t1, t2, arg, ret, bound, k bound) in
        Target.LetNewFun (t1, t2, arg, ret, inner, x,
          transform_command s (Sub.add x x h))

    | CTy.Raise t ->
        let bound = Ident.fresh () in
        let inner = Ident.fresh () in
        Target.LetMatchRaise (t, inner,
          Target.LetThunk (t, inner, bound, k bound),
          x,
          transform_command s (Sub.add x x h))

    | CTy.Forall (_a, knd, body) ->
        let bound = Ident.fresh () in
        let a' = Ident.fresh () in
        let inner = Target.LetInstantiate (a', knd, body, bound, k bound) in
        Target.LetNewForall (a', knd, body, inner, x,
          transform_command s (Sub.add x x h))

    | CTy.Ext _ ->
        (* For Ext types, MuPrd(x, s) means x is a consumer receiving an ext value.
           Transform s, then replace any CutInt(v, x) with k(v) to capture the result. *)
        let x' = Ident.fresh () in
        let transformed_s = transform_command s (Sub.add x x' h) in
        Target.replace_cutint x' k transformed_s

    | CTy.Lower _ | CTy.Base _ | CTy.Arrow _ | CTy.TVar _ | CTy.TMeta _ | CTy.PromotedCtor _ ->
        (* These types should not appear as mu-bindings in well-typed terms *)
        transform_command s (Sub.add x x h)

  (** Transform MuCns: builds appropriate xtor table for the type *)
  and transform_mu_cns (ty: CTy.typ) (a: Ident.t) (s: CTm.command) (h: Sub.t)
      (k: Ident.t -> Target.command) : Target.command =
    (* Target uses CTy types directly (no conversion to FTy) *)
    match ty with
    | CTy.Sgn (d, _) ->
        let _bound = Ident.fresh () in
        Target.LetComatch (d,
          [],  (* TODO: need to look up dec to build branches *)
          a,
          transform_command s (Sub.add a a h))

    | CTy.Fun (t1, t2) ->
        let bound = Ident.fresh () in
        let arg = Ident.fresh () in
        let ret = Ident.fresh () in
        let a' = Ident.fresh () in
        let inner_body = Target.LetApply (t1, t2, arg, ret, a',
          transform_command s (Sub.add a a' h)) in
        Target.LetNewFun (t1, t2, arg, ret, inner_body, bound, k bound)

    | CTy.Lower t ->
        let bound = Ident.fresh () in
        let inner = Ident.fresh () in
        Target.LetNewLower (t, inner,
          Target.LetReturn (t, inner, bound, k bound),
          a,
          transform_command s (Sub.add a a h))

    | CTy.Forall (_tv, knd, body) ->
        let bound = Ident.fresh () in
        let tv' = Ident.fresh () in
        let a' = Ident.fresh () in
        let inner_body = Target.LetInstantiate (tv', knd, body, a',
          transform_command s (Sub.add a a' h)) in
        Target.LetNewForall (tv', knd, body, inner_body, bound, k bound)

    | CTy.Ext _ ->
        (* For Ext types, MuCns(a, s) means a is a producer providing an ext value.
           We just transform the body s with a mapped to itself - 
           the Cut at Ext type will handle the actual binding. *)
        transform_command s (Sub.add a a h)

    | CTy.Raise _ | CTy.Base _ | CTy.Arrow _ | CTy.TVar _ | CTy.TMeta _ | CTy.PromotedCtor _ ->
        (* These types should not appear as mu-bindings in well-typed terms *)
        transform_command s (Sub.add a a h)

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
          Target.Call (path, tys, arg_vars))

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
          Target.CutCtor (d, c, tys, arg_vars, Sub.apply h y))

    | CTm.Ctor (_, c, _tys, args), CTm.Match (_, bs) ->
        bind_terms args h (fun arg_vars ->
          Target.lookup_branch_body (transform_branches bs h) c arg_vars)

    | CTm.Ctor (_, c, tys, args), CTm.MuCns (_, a, r) ->
        bind_terms args h (fun arg_vars ->
          let a' = Ident.fresh () in
          Target.LetCtor (d, c, tys, arg_vars, a',
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
          Target.LetDtor (d, c, tys, arg_vars, x',
            transform_command s (Sub.add x x' h)))

    | CTm.Var x, CTm.Dtor (_, c, tys, args) ->
        bind_terms args h (fun arg_vars ->
          Target.CutDtor (d, c, tys, Sub.apply h x, arg_vars))

    | _ ->
        bind_term lhs h (fun lhs_var ->
          bind_term rhs h (fun _rhs_var ->
            Target.CutMatch (d, lhs_var, [])))

  (** Transform cut at Fun type *)
  and transform_cut_fun (t1: CTy.typ) (t2: CTy.typ) (lhs: CTm.term) (rhs: CTm.term)
      (h: Sub.t) : Target.command =
    (* Target uses CTy types directly (no conversion to FTy) *)
    match lhs, rhs with
    | CTm.Var x, CTm.Var y ->
        let arg = Ident.fresh () in
        let ret = Ident.fresh () in
        Target.CutNewFun (t1, t2, arg, ret,
          Target.CutApply (t1, t2, arg, ret, Sub.apply h x),
          Sub.apply h y)

    | CTm.Var x, CTm.ApplyDtor (_, _, arg, ret) ->
        bind_term arg h (fun arg_var ->
          bind_term ret h (fun ret_var ->
            Target.CutApply (t1, t2, arg_var, ret_var, Sub.apply h x)))

    | CTm.Var x, CTm.MuCns (_, a, r) ->
        transform_command r (Sub.add a (Sub.apply h x) h)

    | CTm.NewFun (_, _, x, k, body), CTm.Var y ->
        let x' = Ident.fresh () in
        let k' = Ident.fresh () in
        Target.CutNewFun (t1, t2, x', k',
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
        Target.LetNewFun (t1, t2, x', kv', inner_body, a',
          transform_command r (Sub.add a a' h))

    | CTm.MuPrd (_, x, s), CTm.Var y ->
        transform_command s (Sub.add x (Sub.apply h y) h)

    | CTm.MuPrd (_, x, s), CTm.ApplyDtor (_, _, arg, ret) ->
        bind_term arg h (fun arg_var ->
          bind_term ret h (fun ret_var ->
            let x' = Ident.fresh () in
            Target.LetApply (t1, t2, arg_var, ret_var, x',
              transform_command s (Sub.add x x' h))))

    | CTm.MuPrd (_, x, s), CTm.MuCns (_, a, r) ->
        let arg = Ident.fresh () in
        let ret = Ident.fresh () in
        let a' = Ident.fresh () in
        let x' = Ident.fresh () in
        let inner_body = Target.LetApply (t1, t2, arg, ret, a',
            transform_command r (Sub.add a a' h)) in
        Target.LetNewFun (t1, t2, arg, ret, inner_body, x',
          transform_command s (Sub.add x x' h))

    | _ ->
        bind_term lhs h (fun lhs_var ->
          bind_term rhs h (fun rhs_var ->
            let arg = Ident.fresh () in
            let ret = Ident.fresh () in
            Target.CutNewFun (t1, t2, arg, ret,
              Target.CutApply (t1, t2, arg, ret, lhs_var),
              rhs_var)))

  (** Transform cut at Forall type *)
  and transform_cut_forall (a: Ident.t) (k: CTy.typ) (body: CTy.typ)
      (lhs: CTm.term) (rhs: CTm.term) (h: Sub.t) : Target.command =
    (* Target uses CTy types directly (no conversion to FTy) *)
    match lhs, rhs with
    | CTm.Var x, CTm.Var y ->
        let a' = Ident.fresh () in
        Target.CutNewForall (a', k, body,
          Target.CutInstantiate (a', k, body, Sub.apply h x),
          Sub.apply h y)

    | CTm.Var x, CTm.InstantiateDtor ty_arg ->
        Target.CutInstantiate (a, ty_arg, body, Sub.apply h x)

    | CTm.Var x, CTm.MuCns (_, av, r) ->
        transform_command r (Sub.add av (Sub.apply h x) h)

    | CTm.NewForall (_, _, _, cmd), CTm.InstantiateDtor _ty_arg ->
        (* Substitute type argument into body *)
        transform_command cmd h

    | CTm.NewForall (av, _, _, cmd), CTm.MuCns (_, bv, r) ->
        let v = Ident.fresh () in
        let av' = Ident.fresh () in
        Target.LetNewForall (av', k, body,
          transform_command cmd (Sub.add av av' h),
          v,
          transform_command r (Sub.add bv v h))

    | CTm.MuPrd (_, x, s), CTm.Var y ->
        transform_command s (Sub.add x (Sub.apply h y) h)

    | _ ->
        bind_term lhs h (fun lhs_var ->
          bind_term rhs h (fun rhs_var ->
            let a' = Ident.fresh () in
            Target.CutNewForall (a', k, body,
              Target.CutInstantiate (a', k, body, lhs_var),
              rhs_var)))

  (** Transform cut at Raise type *)
  and transform_cut_raise (t: CTy.typ) (lhs: CTm.term) (rhs: CTm.term)
      (h: Sub.t) : Target.command =
    (* Target uses CTy types directly (no conversion to FTy) *)
    match lhs, rhs with
    | CTm.Var x, CTm.Var y ->
        let inner = Ident.fresh () in
        Target.CutMatchRaise (t, inner, Sub.apply h y,
          Target.CutThunk (t, inner, Sub.apply h x))

    | CTm.Var x, CTm.MatchRaise (_, v, body) ->
        let v' = Ident.fresh () in
        Target.CutMatchRaise (t, v', Sub.apply h x,
          transform_command body (Sub.add v v' h))

    | CTm.Var x, CTm.MuCns (_, a, r) ->
        transform_command r (Sub.add a (Sub.apply h x) h)

    | CTm.ThunkCtor (_, inner), CTm.Var y ->
        bind_term inner h (fun inner_var ->
          Target.CutThunk (t, inner_var, Sub.apply h y))

    | CTm.ThunkCtor (_, inner), CTm.MatchRaise (_, v, body) ->
        bind_term inner h (fun inner_var ->
          transform_command body (Sub.add v inner_var h))

    | CTm.ThunkCtor (_, inner), CTm.MuCns (_, a, r) ->
        bind_term inner h (fun inner_var ->
          let a' = Ident.fresh () in
          Target.LetThunk (t, inner_var, a',
            transform_command r (Sub.add a a' h)))

    | CTm.MuPrd (_, x, s), CTm.Var y ->
        transform_command s (Sub.add x (Sub.apply h y) h)

    | CTm.MuPrd (_, x, s), CTm.MatchRaise (_, v, body) ->
        let x' = Ident.fresh () in
        let v' = Ident.fresh () in
        Target.LetMatchRaise (t, v',
          transform_command body (Sub.add v v' h),
          x',
          transform_command s (Sub.add x x' h))

    | _ ->
        bind_term lhs h (fun lhs_var ->
          bind_term rhs h (fun rhs_var ->
            let inner = Ident.fresh () in
            Target.CutMatchRaise (t, inner, rhs_var,
              Target.CutThunk (t, inner, lhs_var))))

  (** Transform cut at Lower type *)
  and transform_cut_lower (t: CTy.typ) (lhs: CTm.term) (rhs: CTm.term)
      (h: Sub.t) : Target.command =
    (* Target uses CTy types directly (no conversion to FTy) *)
    match lhs, rhs with
    | CTm.Var x, CTm.Var y ->
        let inner = Ident.fresh () in
        Target.CutNewLower (t, inner,
          Target.CutReturn (t, inner, Sub.apply h x),
          Sub.apply h y)

    | CTm.Var x, CTm.ReturnDtor (_, arg) ->
        bind_term arg h (fun arg_var ->
          Target.CutReturn (t, arg_var, Sub.apply h x))

    | CTm.Var x, CTm.MuCns (_, a, r) ->
        transform_command r (Sub.add a (Sub.apply h x) h)

    | CTm.NewLower (_, k, body), CTm.Var y ->
        let k' = Ident.fresh () in
        Target.CutNewLower (t, k',
          transform_command body (Sub.add k k' h),
          Sub.apply h y)

    | CTm.NewLower (_, k, body), CTm.ReturnDtor (_, arg) ->
        bind_term arg h (fun arg_var ->
          transform_command body (Sub.add k arg_var h))

    | CTm.NewLower (_, k, body), CTm.MuCns (_, a, r) ->
        let k' = Ident.fresh () in
        let a' = Ident.fresh () in
        Target.LetNewLower (t, k',
          transform_command body (Sub.add k k' h),
          a',
          transform_command r (Sub.add a a' h))

    | CTm.MuPrd (_, x, s), CTm.Var y ->
        transform_command s (Sub.add x (Sub.apply h y) h)

    | CTm.MuPrd (_, x, s), CTm.ReturnDtor (_, arg) ->
        bind_term arg h (fun arg_var ->
          let x' = Ident.fresh () in
          Target.LetReturn (t, arg_var, x',
            transform_command s (Sub.add x x' h)))

    | _ ->
        bind_term lhs h (fun lhs_var ->
          bind_term rhs h (fun rhs_var ->
            let inner = Ident.fresh () in
            Target.CutNewLower (t, inner,
              Target.CutReturn (t, inner, lhs_var),
              rhs_var)))

  (** Entry point *)
  let transform (cmd: CTm.command) : Target.command =
    transform_command cmd Sub.empty
end

(* ========================================================================= *)
(* Collapse: Target → Focused                                                *)
(* ========================================================================= *)

module Collapse = struct

  (** Check if a Core type is negative (codata).
      In Core, Fun, Lower, and Forall are codata (negative).
      Raise, Ext, and user-defined Sgn are data (positive). *)
  let is_negative (t: CTy.typ) : bool =
    match t with
    | CTy.Fun (_, _) -> true    (* Function is codata *)
    | CTy.Lower _ -> true       (* Lower is codata *)
    | CTy.Forall (_, _, _) -> true  (* Forall is codata *)
    | CTy.Raise _ -> false      (* Raise is data *)
    | CTy.Sgn (_, _) -> false   (* User signatures default to positive for now *)
    | CTy.PromotedCtor (_, _, _) -> false
    | CTy.TVar _ -> false       (* Type variables default to positive *)
    | CTy.TMeta _ -> false      (* Meta variables default to positive *)
    | CTy.Ext _ -> false        (* External types (like Int) default to positive *)
    | CTy.Base _ -> false       (* Base kinds are positive *)
    | CTy.Arrow (_, _) -> false (* Arrow kinds are positive *)

  (* NOTE: The chirality flip happens implicitly in collapse:
     For negative types (Fun, Lower, Forall), CutNewXxx forms have the variable
     as a consumer (Cns type) in Core, but SwitchXxx forms expect the variable
     as a producer (Prd type) in Focused.
     
     The key insight from simple.ml: collapse_chiral flips Rhs(Neg s) -> Lhs s.
     In our encoding:
       - CutNewLower/CutNewFun etc. have the "a" variable as a consumer of codata
       - SwitchLower/SwitchFun expect "a" as a producer
       - This flip is correct because consuming codata = providing its structure
     
     The typechecker in focused/terms.ml handles this by expecting producers
     for all Switch forms. The collapse just needs to convert the types properly. *)

  (** Collapse a Target branch to a Focused branch.
      parity: true if we're inside an odd number of negative type bindings *)
  let rec collapse_branch (parity: bool) ((xtor, ty_vars, tm_vars, body): Target.branch) : FTm.branch =
    (xtor, ty_vars, tm_vars, collapse_command parity body)

  (** Main collapse transformation.
      parity tracks whether we're inside an odd number of negative type bindings.
      When parity is true and we have a CutNewXxx for a negative type, the target
      variable has Cns chirality (not flipped), so we must generate NewXxx + Axiom
      instead of SwitchXxx. *)
  and collapse_command (parity: bool) : Target.command -> FTm.command = function
    (* User-defined xtors - Let becomes Let, LetMatch becomes New *)
    | Target.LetCtor (d, c, tys, args, x, cont) ->
        FTm.Let (x, d, c, List.map focus_type tys, args, collapse_command parity cont)
    | Target.LetDtor (d, c, tys, args, a, cont) ->
        FTm.Let (a, d, c, List.map focus_type tys, args, collapse_command parity cont)
    | Target.LetMatch (d, branches, x, cont) ->
        FTm.New (d, x, List.map (collapse_branch parity) branches, collapse_command parity cont)
    | Target.LetComatch (d, branches, a, cont) ->
        FTm.New (d, a, List.map (collapse_branch parity) branches, collapse_command parity cont)

    (* User-defined xtors - Cut becomes Switch/Invoke *)
    | Target.CutCtor (d, c, tys, args, a) ->
        FTm.Invoke (a, d, c, List.map focus_type tys, args)
    | Target.CutDtor (d, c, tys, x, args) ->
        FTm.Invoke (x, d, c, List.map focus_type tys, args)
    | Target.CutMatch (d, x, branches) ->
        FTm.Switch (d, x, List.map (collapse_branch parity) branches)
    | Target.CutComatch (d, branches, a) ->
        FTm.Switch (d, a, List.map (collapse_branch parity) branches)

    (* Built-in Fun - Fun is NEGATIVE *)
    | Target.LetApply (t1, t2, x, y, v, cont) ->
        FTm.LetApply (v, focus_type t1, focus_type t2, x, y, collapse_command parity cont)
    | Target.LetNewFun (t1, t2, x, k, body, v, cont) ->
        (* NewFun binds k: Cns t2. If t2 is negative, flip parity for body *)
        let body_parity = if is_negative t2 then not parity else parity in
        FTm.NewFun (v, focus_type t1, focus_type t2, x, k, 
          collapse_command body_parity body, collapse_command parity cont)
    | Target.CutApply (t1, t2, x, y, a) ->
        FTm.InvokeApply (a, focus_type t1, focus_type t2, x, y)
    | Target.CutNewFun (t1, t2, x, k, body, a) ->
        (* Fun is negative. At parity=false, a becomes Prd (flip), use SwitchFun.
           At parity=true, a stays Cns, use NewFun + Axiom. *)
        let t1' = focus_type t1 in
        let t2' = focus_type t2 in
        let body_parity = if is_negative t2 then not parity else parity in
        if parity then
          let v = Ident.fresh () in
          FTm.NewFun (v, t1', t2', x, k, 
            collapse_command body_parity body,
            FTm.Axiom (FTy.Fun (t1', t2'), v, a))
        else
          FTm.SwitchFun (a, t1', t2', x, k, collapse_command body_parity body)

    (* Built-in Forall - Forall is NEGATIVE *)
    | Target.LetInstantiate (a, k, ty, v, cont) ->
        FTm.LetInstantiate (v, a, focus_type k, focus_type ty, collapse_command parity cont)
    | Target.LetNewForall (a, k, body_ty, body, v, cont) ->
        (* NewForall binds with body type. If body is negative, flip parity *)
        let body_parity = if is_negative body_ty then not parity else parity in
        FTm.NewForall (v, a, focus_type k, 
          collapse_command body_parity body, collapse_command parity cont)
    | Target.CutInstantiate (_a, k, ty, v) ->
        FTm.InvokeInstantiate (v, focus_type ty, focus_type k)
    | Target.CutNewForall (a, k, body_ty, body, v) ->
        (* Forall is negative. Similar logic to CutNewFun. *)
        let k' = focus_type k in
        let body_parity = if is_negative body_ty then not parity else parity in
        if parity then
          let w = Ident.fresh () in
          FTm.NewForall (w, a, k',
            collapse_command body_parity body,
            FTm.Axiom (FTy.Forall (a, k', focus_type body_ty), w, v))
        else
          FTm.SwitchForall (v, a, k', collapse_command body_parity body)

    (* Built-in Raise - Raise is POSITIVE (no flip, no parity change) *)
    | Target.LetThunk (t, x, v, cont) ->
        FTm.LetThunk (v, focus_type t, x, collapse_command parity cont)
    | Target.LetMatchRaise (t, x, body, v, cont) ->
        (* Raise is positive, so inner binding doesn't flip *)
        FTm.NewRaise (v, focus_type t, x, collapse_command parity body, collapse_command parity cont)
    | Target.CutThunk (t, x, a) ->
        FTm.InvokeThunk (a, focus_type t, x)
    | Target.CutMatchRaise (t, x, a, body) ->
        (* Raise is positive, no parity flip *)
        FTm.SwitchRaise (a, focus_type t, x, collapse_command parity body)

    (* Built-in Lower - Lower is NEGATIVE *)
    | Target.LetReturn (t, x, v, cont) ->
        FTm.LetReturn (v, focus_type t, x, collapse_command parity cont)
    | Target.LetNewLower (t, k, body, v, cont) ->
        (* NewLower binds k: Prd t. If t is negative, flip parity *)
        let body_parity = if is_negative t then not parity else parity in
        FTm.NewLower (v, focus_type t, k, 
          collapse_command body_parity body, collapse_command parity cont)
    | Target.CutReturn (t, x, a) ->
        FTm.InvokeReturn (a, focus_type t, x)
    | Target.CutNewLower (t, k, body, a) ->
        (* Lower is negative. At parity=false, a becomes Prd (flip), use SwitchLower.
           At parity=true, a stays Cns, use NewLower + Axiom. *)
        let t' = focus_type t in
        let body_parity = if is_negative t then not parity else parity in
        if parity then
          let v = Ident.fresh () in
          FTm.NewLower (v, t', k,
            collapse_command body_parity body,
            FTm.Axiom (FTy.Lower t', v, a))
        else
          FTm.SwitchLower (a, t', k, collapse_command body_parity body)

    (* Primitives *)
    | Target.LetInt (n, x, cont) ->
        FTm.Lit (n, x, collapse_command parity cont)
    | Target.CutInt (x, k) ->
        FTm.Axiom (FTy.Ext Common.Types.Int, x, k)
    | Target.Add (x, y, k, cont) ->
        FTm.Add (x, y, k, collapse_command parity cont)
    | Target.Ifz (v, s1, s2) ->
        FTm.Ifz (v, collapse_command parity s1, collapse_command parity s2)
    | Target.Call (_path, _tys, _args) ->
        (* Calls need a return continuation - for now return End *)
        FTm.End

    | Target.Ret (ty, x) -> FTm.Ret (focus_type ty, x)
    | Target.End -> FTm.End

  (** Full pipeline: Core → Focused *)
  let focus_command (cmd: CTm.command) : FTm.command =
    collapse_command false (Transform.transform cmd)
end

(** Top-level entry point *)
let focus_command = Collapse.focus_command