(**
  Module: Focus
  Description: Translates Core to Focused.
  
  This transformation canonicalizes Core sequent calculus terms into Focused form.
  It follows the structure of simple.ml, using an intermediate Target representation
  annotated with Core types before collapsing to the final Focused language.
  
  Key insight from simple.ml: chirality flips for negative types during collapse.
  - Positive type T: Prd T → Prd, Cns T → Cns (preserved)
  - Negative type T: Prd T → Cns, Cns T → Prd (flipped)
*)

open Common.Identifiers

module CB = Core.Types.CoreBase
module CTy = Core.Types.CoreTypes
module CTm = Core.Terms
module FB = Focused.Types.FocusedBase
module FTy = Focused.Types.FocusedTypes
module FTm = Focused.Terms

module Prim = Common.Types.Prim

(* ========================================================================= *)
(* Primitive Type Pattern Matching                                           *)
(* ========================================================================= *)

(** Match a type as Fun(t1, t2) *)
let match_fun (t: CTy.typ) : (CTy.typ * CTy.typ) option =
  match t with
  | CTy.Sgn (s, [t1; t2]) when Path.equal s Prim.fun_sym -> Some (t1, t2)
  | _ -> None

(** Match a type as Raise(t) *)
let match_raise (t: CTy.typ) : CTy.typ option =
  match t with
  | CTy.Sgn (s, [t']) when Path.equal s Prim.raise_sym -> Some t'
  | _ -> None

(** Match a type as Lower(t) *)
let match_lower (t: CTy.typ) : CTy.typ option =
  match t with
  | CTy.Sgn (s, [t']) when Path.equal s Prim.lower_sym -> Some t'
  | _ -> None

(** Check if type is a primitive (Fun, Raise, Lower) *)
let is_primitive_path (p: Path.t) : bool =
  Path.equal p Prim.fun_sym ||
  Path.equal p Prim.raise_sym ||
  Path.equal p Prim.lower_sym

(** Check if a Core type is negative (codata).
    In our system: Fun and Lower are negative. Raise is positive.
    Forall is negative. User-defined Sgn types checked by polarity. *)
let is_negative (t: CTy.typ) : bool =
  match t with
  | CTy.Forall (_, _, _) -> true
  | CTy.Sgn (s, _) when Path.equal s Prim.fun_sym -> true
  | CTy.Sgn (s, _) when Path.equal s Prim.lower_sym -> true
  | _ -> false

(* Suppress unused warnings for helpers *)
let _ = match_fun
let _ = match_raise
let _ = match_lower
let _ = is_primitive_path

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
  | CTy.Base _ -> FTy.Base FB.Typ
  | CTy.Arrow (t1, t2) -> FTy.Arrow (focus_type t1, focus_type t2)
  | CTy.Ext e -> FTy.Ext e
  | CTy.TVar v -> FTy.TVar v
  | CTy.TMeta v -> FTy.TMeta v
  | CTy.Sgn (p, args) -> FTy.Sgn (p, List.map focus_type args)
  | CTy.PromotedCtor (d, c, args) -> FTy.PromotedCtor (d, c, List.map focus_type args)
  | CTy.Forall (x, k, body) -> FTy.Forall (x, focus_type k, focus_type body)

let focus_xtor (x: CTy.xtor) : FTy.xtor =
  let focus_xtor_arg (ty: CTy.chiral_typ) : FTy.chiral_typ =
    match ty with
    | CB.Prd t -> FB.Prd (focus_type t)
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
  | CB.Prd t -> FB.Prd (focus_type t)
  | CB.Cns t -> FB.Cns (focus_type t)

(* Suppress unused warnings *)
let _ = focus_xtor
let _ = focus_dec
let _ = focus_chiral

(* ========================================================================= *)
(* Target Language                                                           *)
(* ========================================================================= *)

(**
  Intermediate representation for focusing.
  
  This is analogous to simple.ml's Target module. The Target language is
  annotated with Core types (CTy.typ) so we can determine negativity during
  collapse.
  
  Key forms:
  - LetCtor/LetDtor: bind a producer/consumer from an xtor application
  - LetMatch/LetComatch: bind a result from building a pattern/copattern
  - CutCtor/CutDtor: invoke an xtor against a continuation
  - CutMatch/CutComatch: invoke a pattern/copattern against a value
  
  Forall is handled specially because it has type-level binding.
*)
module Target = struct

  type command =
    (* User-defined and primitive xtors *)
    | LetCtor of Path.t * Path.t * CTy.typ list * Ident.t list * Ident.t * command
    | LetDtor of Path.t * Path.t * CTy.typ list * Ident.t list * Ident.t * command
    | LetMatch of Path.t * branch list * Ident.t * command
    | LetComatch of Path.t * branch list * Ident.t * command
    | CutCtor of Path.t * Path.t * CTy.typ list * Ident.t list * Ident.t
    | CutDtor of Path.t * Path.t * CTy.typ list * Ident.t * Ident.t list
    | CutMatch of Path.t * Ident.t * branch list
    | CutComatch of Path.t * branch list * Ident.t
    (* Built-in Forall type - needs special handling *)
    | LetInstantiate of Ident.t * CTy.typ * CTy.typ * Ident.t * command
    | LetNewForall of Ident.t * CTy.typ * CTy.typ * command * Ident.t * command
    | CutInstantiate of Ident.t * CTy.typ * CTy.typ * Ident.t
    | CutNewForall of Ident.t * CTy.typ * CTy.typ * command * Ident.t
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
    (* Built-in Forall *)
    | LetInstantiate (a, k, ty, v, cont) ->
        let v' = Ident.fresh () in
        LetInstantiate (a, k, ty, v', rename_command (Sub.add v v' h) cont)
    | LetNewForall (a, k, body_ty, body, v, cont) ->
        let a' = Ident.fresh () in
        let v' = Ident.fresh () in
        LetNewForall (a', k, body_ty, rename_command (Sub.add a a' h) body, v',
          rename_command (Sub.add v v' h) cont)
    | CutInstantiate (a, k, ty, v) ->
        CutInstantiate (a, k, ty, Sub.apply h v)
    | CutNewForall (a, k, body_ty, body, v) ->
        let a' = Ident.fresh () in
        CutNewForall (a', k, body_ty, rename_command (Sub.add a a' h) body, Sub.apply h v)
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
        transform_mu_prd ty x s h k

    | CTm.MuCns (ty, a, s) ->
        transform_mu_cns ty a s h k

    | CTm.NewForall (a, k_ty, body_ty, body) ->
        let v = Ident.fresh () in
        let a' = Ident.fresh () in
        Target.LetNewForall (a', k_ty, body_ty,
          transform_command body (Sub.add a a' h),
          v, k v)

    | CTm.InstantiateDtor ty_arg ->
        let a = Ident.fresh () in
        Target.LetInstantiate (a, ty_arg, ty_arg, a, k a)

    | CTm.Lit n ->
        let x = Ident.fresh () in
        Target.LetInt (n, x, k x)

  (** Transform MuPrd: builds appropriate xtor table for the type *)
  and transform_mu_prd (ty: CTy.typ) (x: Ident.t) (s: CTm.command) (h: Sub.t)
      (k: Ident.t -> Target.command) : Target.command =
    match ty with
    | CTy.Sgn (d, _) ->
        let bound = Ident.fresh () in
        Target.LetMatch (d, [], bound,
          transform_command s (Sub.add x bound h))

    | CTy.Forall (_a, k_ty, body_ty) ->
        let bound = Ident.fresh () in
        let a' = Ident.fresh () in
        let inner = Target.LetInstantiate (a', k_ty, body_ty, bound, k bound) in
        Target.LetNewForall (a', k_ty, body_ty, inner, x,
          transform_command s (Sub.add x x h))

    | CTy.Ext _ ->
        transform_command s (Sub.add x x h)

    | _ ->
        transform_command s (Sub.add x x h)

  (** Transform MuCns: builds appropriate xtor table for the type *)
  and transform_mu_cns (ty: CTy.typ) (a: Ident.t) (s: CTm.command) (h: Sub.t)
      (k: Ident.t -> Target.command) : Target.command =
    match ty with
    | CTy.Sgn (d, _) ->
        let bound = Ident.fresh () in
        Target.LetComatch (d, [], bound,
          transform_command s (Sub.add a bound h))

    | CTy.Forall (_tv, k_ty, body_ty) ->
        let bound = Ident.fresh () in
        let tv' = Ident.fresh () in
        let a' = Ident.fresh () in
        let inner_body = Target.LetInstantiate (tv', k_ty, body_ty, a',
          transform_command s (Sub.add a a' h)) in
        Target.LetNewForall (tv', k_ty, body_ty, inner_body, bound, k bound)

    | CTy.Ext _ ->
        transform_command s (Sub.add a a h)

    | _ ->
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
    (* Cut at a signature type (including primitives Fun, Raise, Lower) *)
    | CTm.Cut (CTy.Sgn (d, _tys), lhs, rhs) ->
        transform_cut_sgn d lhs rhs h

    (* Cut at Forall type *)
    | CTm.Cut (CTy.Forall (a, k_ty, body_ty), lhs, rhs) ->
        transform_cut_forall a k_ty body_ty lhs rhs h

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

  (** Transform cut at signature type (includes Fun, Raise, Lower) *)
  and transform_cut_sgn (d: Path.t) (lhs: CTm.term) (rhs: CTm.term)
      (h: Sub.t) : Target.command =
    match lhs, rhs with
    | CTm.Var x, CTm.Var _y ->
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
        Target.LetMatch (d, [], x',
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

  (** Transform cut at Forall type *)
  and transform_cut_forall (a: Ident.t) (k_ty: CTy.typ) (body_ty: CTy.typ)
      (lhs: CTm.term) (rhs: CTm.term) (h: Sub.t) : Target.command =
    match lhs, rhs with
    | CTm.Var x, CTm.Var y ->
        let a' = Ident.fresh () in
        Target.CutNewForall (a', k_ty, body_ty,
          Target.CutInstantiate (a', k_ty, body_ty, Sub.apply h x),
          Sub.apply h y)

    | CTm.Var x, CTm.InstantiateDtor ty_arg ->
        Target.CutInstantiate (a, ty_arg, body_ty, Sub.apply h x)

    | CTm.Var x, CTm.MuCns (_, av, r) ->
        transform_command r (Sub.add av (Sub.apply h x) h)

    | CTm.NewForall (_, _, _, cmd), CTm.InstantiateDtor _ty_arg ->
        transform_command cmd h

    | CTm.NewForall (av, _, _, cmd), CTm.MuCns (_, bv, r) ->
        let v = Ident.fresh () in
        let av' = Ident.fresh () in
        Target.LetNewForall (av', k_ty, body_ty,
          transform_command cmd (Sub.add av av' h),
          v,
          transform_command r (Sub.add bv v h))

    | CTm.MuPrd (_, x, s), CTm.Var y ->
        transform_command s (Sub.add x (Sub.apply h y) h)

    | _ ->
        bind_term lhs h (fun lhs_var ->
          bind_term rhs h (fun rhs_var ->
            let a' = Ident.fresh () in
            Target.CutNewForall (a', k_ty, body_ty,
              Target.CutInstantiate (a', k_ty, body_ty, lhs_var),
              rhs_var)))

  (** Entry point *)
  let transform (cmd: CTm.command) : Target.command =
    transform_command cmd Sub.empty
end

(* ========================================================================= *)
(* Collapse: Target → Focused                                                *)
(* ========================================================================= *)

module Collapse = struct
  (**
    Collapse the Target language to the Focused language.
    
    Key insight from simple.ml: chirality flips for negative types.
    - Positive type T: Prd T → Prd, Cns T → Cns (preserved)
    - Negative type T: Prd T → Cns, Cns T → Prd (flipped)
  *)

  (** Collapse a Target branch to a Focused branch *)
  let rec collapse_branch (parity: bool) ((xtor, ty_vars, tm_vars, body): Target.branch)
      : FTm.branch =
    (xtor, ty_vars, tm_vars, collapse_command parity body)

  (** Main collapse transformation.
      parity: true if we're inside an odd number of negative type bindings *)
  and collapse_command (parity: bool) : Target.command -> FTm.command = function
    (* LetCtor and LetDtor both become Let *)
    | Target.LetCtor (d, c, tys, args, x, cont) ->
        FTm.Let (x, d, c, List.map focus_type tys, args, collapse_command parity cont)
    | Target.LetDtor (d, c, tys, args, a, cont) ->
        FTm.Let (a, d, c, List.map focus_type tys, args, collapse_command parity cont)

    (* LetMatch and LetComatch both become New *)
    | Target.LetMatch (d, branches, x, cont) ->
        FTm.New (d, x, List.map (collapse_branch parity) branches, collapse_command parity cont)
    | Target.LetComatch (d, branches, a, cont) ->
        FTm.New (d, a, List.map (collapse_branch parity) branches, collapse_command parity cont)

    (* CutCtor and CutDtor both become Invoke *)
    | Target.CutCtor (d, c, tys, args, a) ->
        FTm.Invoke (a, d, c, List.map focus_type tys, args)
    | Target.CutDtor (d, c, tys, x, args) ->
        FTm.Invoke (x, d, c, List.map focus_type tys, args)

    (* CutMatch and CutComatch both become Switch *)
    | Target.CutMatch (d, x, branches) ->
        FTm.Switch (d, x, List.map (collapse_branch parity) branches)
    | Target.CutComatch (d, branches, a) ->
        FTm.Switch (d, a, List.map (collapse_branch parity) branches)

    (* Built-in Forall - Forall is NEGATIVE *)
    | Target.LetInstantiate (a, k_ty, body_ty, v, cont) ->
        FTm.LetInstantiate (v, a, focus_type k_ty, focus_type body_ty, collapse_command parity cont)
    | Target.LetNewForall (a, k_ty, body_ty, body, v, cont) ->
        let body_parity = if is_negative body_ty then not parity else parity in
        FTm.NewForall (v, a, focus_type k_ty, 
          collapse_command body_parity body, collapse_command parity cont)
    | Target.CutInstantiate (_a, k_ty, body_ty, v) ->
        FTm.InvokeInstantiate (v, focus_type body_ty, focus_type k_ty)
    | Target.CutNewForall (a, k_ty, body_ty, body, v) ->
        let k' = focus_type k_ty in
        let body_parity = if is_negative body_ty then not parity else parity in
        if parity then
          let w = Ident.fresh () in
          FTm.NewForall (w, a, k',
            collapse_command body_parity body,
            FTm.Axiom (FTy.Forall (a, k', focus_type body_ty), w, v))
        else
          FTm.SwitchForall (v, a, k', collapse_command body_parity body)

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
        FTm.End

    | Target.Ret (ty, x) -> FTm.Ret (focus_type ty, x)
    | Target.End -> FTm.End

  (** Full pipeline: Core → Focused *)
  let focus_command (cmd: CTm.command) : FTm.command =
    collapse_command false (Transform.transform cmd)
end

(** Top-level entry point *)
let focus_command = Collapse.focus_command
