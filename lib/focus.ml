(**
  Module: Focus
  Description: Translates Core to Focused.
  
  This transformation canonicalizes Core sequent calculus terms into Focused form.
  It follows the Idris AxCutNormalForm.idr algorithm closely.
  
  Key insight: chirality flips for negative types during collapse.
  - Positive type T: Prd T → Prd, Cns T → Cns (preserved)
  - Negative type T: Prd T → Cns, Cns T → Prd (flipped)
*)

open Common.Identifiers
open Common.Types

module CB = Core.Types.CoreBase
module CTy = Core.Types.CoreTypes
module CTm = Core.Terms
module FB = Focused.Types.FocusedBase
module FTy = Focused.Types.FocusedTypes
module FTm = Focused.Terms

module Prim = Common.Types.Prim

(** Context for transformation - holds type declarations and kinding context *)
type focus_ctx = 
  { decs: CTy.dec Path.tbl
  ; ty_ctx: CTy.context
  }

let make_focus_ctx (decs: CTy.dec Path.tbl) : focus_ctx =
  let ty_ctx = List.fold_left (fun ctx (_path, dec) -> CTy.add_dec ctx dec) CTy.empty_context (Path.to_list decs) in
  { decs; ty_ctx }

(* ========================================================================= *)
(* Substitution                                                              *)
(* ========================================================================= *)

(**
  Substitution maps source variables to target variables.
  The continuation receives (i: Sub.t, v: Ident.t) where:
  - i represents the "extension" from binding this term (for threading)
  - v is the variable bound to this term's value
  For composition: (compose i j)(x) = i(j(x))
*)
module Sub = struct
  type t = Ident.t Ident.tbl
  
  let empty : t = Ident.emptytbl
  let add (x: Ident.t) (y: Ident.t) (s: t) : t = Ident.add x y s
  
  let apply (s: t) (x: Ident.t) : Ident.t =
    match Ident.find_opt x s with Some y -> y | None -> x
  
  (** Compose: (compose s1 s2)(x) = s1(s2(x)) *)
  let compose (s1: t) (s2: t) : t =
    let s2_lifted = List.map (fun (x, y) -> (x, apply s1 y)) (Ident.to_list s2) in
    let s1_filtered = List.filter (fun (x, _) -> 
      not (List.exists (fun (x', _) -> Ident.equal x x') s2_lifted)) (Ident.to_list s1) in
    Ident.of_list (s2_lifted @ s1_filtered)
end

(* ========================================================================= *)
(* Type Substitution                                                         *)
(* ========================================================================= *)

module TySub = struct
  type t = CTy.typ Ident.tbl
  let empty : t = Ident.emptytbl
  let add (v: Ident.t) (ty: CTy.typ) (s: t) : t = Ident.add v ty s
  let apply (s: t) (v: Ident.t) : CTy.typ = 
    match Ident.find_opt v s with Some ty -> ty | None -> CTy.TVar v
end

let rec subst_type (ts: TySub.t) (t: CTy.typ) : CTy.typ =
  match t with
  | CTy.TVar v -> TySub.apply ts v
  | CTy.TMeta v -> CTy.TMeta v
  | CTy.Base p -> CTy.Base p
  | CTy.Arrow (t1, t2) -> CTy.Arrow (subst_type ts t1, subst_type ts t2)
  | CTy.Ext e -> CTy.Ext e
  | CTy.Sgn (p, args) -> CTy.Sgn (p, List.map (subst_type ts) args)
  | CTy.PromotedCtor (d, c, args) -> CTy.PromotedCtor (d, c, List.map (subst_type ts) args)
  | CTy.Forall (x, k, body) -> CTy.Forall (x, subst_type ts k, subst_type ts body)

let subst_chiral_type (ts: TySub.t) (ct: CTy.chiral_typ) : CTy.chiral_typ =
  match ct with CB.Prd t -> CB.Prd (subst_type ts t) | CB.Cns t -> CB.Cns (subst_type ts t)

let subst_xtor (ts: TySub.t) (x: CTy.xtor) : CTy.xtor =
  { name = x.name
  ; quantified = List.map (fun (v, k) -> (v, subst_type ts k)) x.quantified
  ; existentials = List.map (fun (v, k) -> (v, subst_type ts k)) x.existentials
  ; argument_types = List.map (subst_chiral_type ts) x.argument_types
  ; main = subst_type ts x.main
  }

let subst_dec (ts: TySub.t) (d: CTy.dec) : CTy.dec =
  { name = d.name; data_sort = d.data_sort
  ; param_kinds = List.map (subst_type ts) d.param_kinds
  ; type_args = List.map (subst_type ts) d.type_args
  ; xtors = List.map (subst_xtor ts) d.xtors
  }

let rec subst_term (ts: TySub.t) (t: CTm.term) : CTm.term =
  match t with
  | CTm.Var v -> CTm.Var v
  | CTm.Ctor (dec, c, args) -> CTm.Ctor (subst_dec ts dec, c, List.map (subst_term ts) args)
  | CTm.Dtor (dec, c, exist_tys, args) -> CTm.Dtor (subst_dec ts dec, c, List.map (subst_type ts) exist_tys, List.map (subst_term ts) args)
  | CTm.Match (dec, bs) -> CTm.Match (subst_dec ts dec, List.map (subst_branch ts) bs)
  | CTm.Comatch (dec, bs) -> CTm.Comatch (subst_dec ts dec, List.map (subst_branch ts) bs)
  | CTm.MuPrd (ty, v, cmd) -> CTm.MuPrd (subst_type ts ty, v, subst_command ts cmd)
  | CTm.MuCns (ty, v, cmd) -> CTm.MuCns (subst_type ts ty, v, subst_command ts cmd)
  | CTm.NewForall (v, k, body_ty, cont, cmd) -> 
      CTm.NewForall (v, subst_type ts k, subst_type ts body_ty, cont, subst_command ts cmd)
  | CTm.InstantiateDtor ty -> CTm.InstantiateDtor (subst_type ts ty)
  | CTm.Lit n -> CTm.Lit n

and subst_branch (ts: TySub.t) (xtor, ty_vars, tm_vars, cmd) : CTm.branch =
  (xtor, ty_vars, tm_vars, subst_command ts cmd)

and subst_command (ts: TySub.t) (cmd: CTm.command) : CTm.command =
  match cmd with
  | CTm.Cut (ty, lhs, rhs) -> CTm.Cut (subst_type ts ty, subst_term ts lhs, subst_term ts rhs)
  | CTm.Add (m, n, k) -> CTm.Add (subst_term ts m, subst_term ts n, subst_term ts k)
  | CTm.Sub (m, n, k) -> CTm.Sub (subst_term ts m, subst_term ts n, subst_term ts k)
  | CTm.Ifz (cond, s1, s2) -> CTm.Ifz (subst_term ts cond, subst_command ts s1, subst_command ts s2)
  | CTm.Ret (ty, t) -> CTm.Ret (subst_type ts ty, subst_term ts t)
  | CTm.Call (p, tys, args) -> CTm.Call (p, List.map (subst_type ts) tys, List.map (subst_term ts) args)
  | CTm.End -> CTm.End

(* ========================================================================= *)
(* Polarity Helpers                                                          *)
(* ========================================================================= *)

let polarity_of (ctx: focus_ctx) (t: CTy.typ) : CB.polarity option =
  match t with
  | CTy.Arrow _ -> Some CB.Neg
  | CTy.Sgn (f, _) when Path.equal f Prim.fun_sym -> Some CB.Neg
  | CTy.Sgn (l, _) when Path.equal l Prim.lower_sym -> Some CB.Neg
  | CTy.Sgn (r, _) when Path.equal r Prim.raise_sym -> Some CB.Pos
  | CTy.Forall _ -> Some CB.Neg
  | CTy.Sgn (s, _) ->
      (match Path.find_opt s ctx.decs with
        Some dec -> Some (if dec.data_sort = Data then CB.Pos else CB.Neg)
      | None -> (match CTy.infer_kind ctx.ty_ctx t with Ok (CTy.Base p) -> Some p | _ -> None))
  | _ -> match CTy.infer_kind ctx.ty_ctx t with Ok (CTy.Base p) -> Some p | _ -> None

let is_negative (ctx: focus_ctx) (t: CTy.typ) : bool =
  polarity_of ctx t = Some CB.Neg

let get_dec_from_type (decs: CTy.dec Path.tbl) (ty: CTy.typ) : CTy.dec option =
  match ty with
    CTy.Sgn (s, type_args) ->
      let base_dec = 
        if Path.equal s Prim.fun_sym then Some CTy.fun_dec
        else if Path.equal s Prim.raise_sym then Some CTy.raise_dec
        else if Path.equal s Prim.lower_sym then Some CTy.lower_dec
        else Path.find_opt s decs
      in
      Option.map (fun d -> CTy.instantiate_dec d type_args) base_dec
  | _ -> None

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

let collapse_chiral (ctx: focus_ctx) (ct: CTy.chiral_typ) : FTy.chiral_typ =
  match ct with
  | CB.Prd t -> 
      let neg = is_negative ctx t in
      if neg then FB.Cns (focus_type t) else FB.Prd (focus_type t)
  | CB.Cns t -> 
      let neg = is_negative ctx t in
      if neg then FB.Prd (focus_type t) else FB.Cns (focus_type t)

let collapse_xtor (ctx: focus_ctx) (x: CTy.xtor) : FTy.xtor =
  let extended_ty_ctx = 
    List.fold_left (fun c (v, k) -> { c with CTy.typ_vars = Ident.add v k c.CTy.typ_vars })
      ctx.ty_ctx (x.quantified @ x.existentials)
  in
  let extended_ctx = { ctx with ty_ctx = extended_ty_ctx } in
  { FTy.name = x.name
  ; quantified = List.map (fun (v, k) -> (v, focus_type k)) x.quantified
  ; existentials = List.map (fun (v, k) -> (v, focus_type k)) x.existentials
  ; argument_types = List.map (collapse_chiral extended_ctx) x.argument_types
  ; main = focus_type x.main
  }

let collapse_dec (ctx: focus_ctx) (d: CTy.dec) : FTy.dec =
  { name = d.name; data_sort = d.data_sort
  ; param_kinds = List.map focus_type d.param_kinds
  ; type_args = List.map focus_type d.type_args
  ; xtors = List.map (collapse_xtor ctx) d.xtors
  }

(* ========================================================================= *)
(* Target Language                                                           *)
(* ========================================================================= *)

module Target = struct
  type command =
    | LetCtor of CTy.dec * Path.t * Ident.t list * Ident.t * command
    | LetDtor of CTy.dec * Path.t * Ident.t list * Ident.t * command
    | LetMatch of CTy.dec * branch list * Ident.t * command
    | LetComatch of CTy.dec * branch list * Ident.t * command
    | CutCtor of CTy.dec * Path.t * Ident.t list * Ident.t
    | CutDtor of CTy.dec * Path.t * Ident.t * Ident.t list
    | CutMatch of CTy.dec * Ident.t * branch list
    | CutComatch of CTy.dec * branch list * Ident.t
    (* Forall *)
    | LetInstantiate of Ident.t * CTy.typ * CTy.typ * Ident.t * command
    | LetNewForall of Ident.t * CTy.typ * CTy.typ * command * Ident.t * command
    | CutInstantiate of Ident.t * CTy.typ * CTy.typ * Ident.t
    | CutNewForall of Ident.t * CTy.typ * CTy.typ * command * Ident.t
    (* Primitives *)
    | LetInt of int * Ident.t * command
    | LetNewInt of Ident.t * Ident.t * command * command  (* new k = { v => branch }; cont - int continuation *)
    | CutInt of Ident.t * Ident.t
    (* Administrative cuts at type variables (should be eliminated by monomorphization) *)
    | CutTyped of Ident.t * Ident.t * Ident.t  (* tvar, producer, consumer *)
    | AdministrativeTyped of Ident.t * Ident.t * command * Ident.t * command  (* tvar, x, s1, a, s2 for ⟨µα.s1 | µ~x.s2⟩_T *)
    | Add of Ident.t * Ident.t * Ident.t * command
    | Sub of Ident.t * Ident.t * Ident.t * command
    | Ifz of Ident.t * command * command
    | Call of Path.t * CTy.typ list * Ident.t list
    | Ret of CTy.typ * Ident.t
    | End
  and branch = Path.t * Ident.t list * Ident.t list * command

  (* apply renaming to command *)
  let rec rename (h: Sub.t) : command -> command = function
    | LetCtor (dec, c, args, x, cont) ->
        let x' = Ident.fresh () in
        LetCtor (dec, c, List.map (Sub.apply h) args, x', rename (Sub.add x x' h) cont)
    | LetDtor (dec, c, args, a, cont) ->
        let a' = Ident.fresh () in
        LetDtor (dec, c, List.map (Sub.apply h) args, a', rename (Sub.add a a' h) cont)
    | LetMatch (dec, branches, x, cont) ->
        let x' = Ident.fresh () in
        LetMatch (dec, List.map (rename_branch h) branches, x', rename (Sub.add x x' h) cont)
    | LetComatch (dec, branches, a, cont) ->
        let a' = Ident.fresh () in
        LetComatch (dec, List.map (rename_branch h) branches, a', rename (Sub.add a a' h) cont)
    | CutCtor (dec, c, args, a) ->
        CutCtor (dec, c, List.map (Sub.apply h) args, Sub.apply h a)
    | CutDtor (dec, c, x, args) ->
        CutDtor (dec, c, Sub.apply h x, List.map (Sub.apply h) args)
    | CutMatch (dec, x, branches) ->
        CutMatch (dec, Sub.apply h x, List.map (rename_branch h) branches)
    | CutComatch (dec, branches, a) ->
        CutComatch (dec, List.map (rename_branch h) branches, Sub.apply h a)
    | LetInstantiate (a, k, ty, v, cont) ->
        let v' = Ident.fresh () in
        LetInstantiate (a, k, ty, v', rename (Sub.add v v' h) cont)
    | LetNewForall (a, k, body_ty, body, v, cont) ->
        let a' = Ident.fresh () in let v' = Ident.fresh () in
        LetNewForall (a', k, body_ty, rename (Sub.add a a' h) body, v', rename (Sub.add v v' h) cont)
    | CutInstantiate (a, k, ty, v) -> CutInstantiate (a, k, ty, Sub.apply h v)
    | CutNewForall (a, k, body_ty, body, v) ->
        let a' = Ident.fresh () in
        CutNewForall (a', k, body_ty, rename (Sub.add a a' h) body, Sub.apply h v)
    | LetInt (n, x, cont) ->
        let x' = Ident.fresh () in LetInt (n, x', rename (Sub.add x x' h) cont)
    | LetNewInt (k, v, branch, cont) ->
        let k' = Ident.fresh () in let v' = Ident.fresh () in
        LetNewInt (k', v', rename (Sub.add v v' (Sub.add k k' h)) branch, rename (Sub.add k k' h) cont)
    | CutInt (x, a) -> CutInt (Sub.apply h x, Sub.apply h a)
    | CutTyped (tvar, x, a) -> CutTyped (tvar, Sub.apply h x, Sub.apply h a)
    | AdministrativeTyped (tvar, x, s1, a, s2) ->
        let x' = Ident.fresh () in let a' = Ident.fresh () in
        AdministrativeTyped (tvar, x', rename (Sub.add x x' h) s1, a', rename (Sub.add a a' h) s2)
    | Add (x, y, k, cont) ->
        let k' = Ident.fresh () in Add (Sub.apply h x, Sub.apply h y, k', rename (Sub.add k k' h) cont)
    | Sub (x, y, k, cont) ->
        let k' = Ident.fresh () in Sub (Sub.apply h x, Sub.apply h y, k', rename (Sub.add k k' h) cont)
    | Ifz (v, s1, s2) -> Ifz (Sub.apply h v, rename h s1, rename h s2)
    | Call (p, tys, args) -> Call (p, tys, List.map (Sub.apply h) args)
    | Ret (ty, x) -> Ret (ty, Sub.apply h x)
    | End -> End

  and rename_branch (h: Sub.t) ((xtor, ty_vars, tm_vars, body): branch) : branch =
    let tm_vars' = List.map (fun _ -> Ident.fresh ()) tm_vars in
    let h' = List.fold_left2 (fun acc p p' -> Sub.add p p' acc) h tm_vars tm_vars' in
    (xtor, ty_vars, tm_vars', rename h' body)

  (* lookup branch body and substitute arguments *)
  let lookup_branch (branches: branch list) (xtor: Path.t) (arg_vars: Ident.t list) : command =
    match List.find_opt (fun (name, _, _, _) -> Path.equal name xtor) branches with
    | Some (_, _, params, body) ->
        let sub = List.fold_left2 (fun acc p v -> Sub.add p v acc) Sub.empty params arg_vars in
        rename sub body
    | None -> End
end

(* ========================================================================= *)
(* Transformation: Core → Target                                             *)
(* ========================================================================= *)

module Transform = struct

  let fresh_params (ps: 'a list) : Ident.t list =
    List.map (fun _ -> Ident.fresh ()) ps

  let rec transform_branch (ctx: focus_ctx) ((xtor, ty_vars, tm_vars, body): CTm.branch) (h: Sub.t) 
      : Target.branch =
    let tm_vars' = fresh_params tm_vars in
    let h' = List.fold_left2 (fun acc p p' -> Sub.add p p' acc) h tm_vars tm_vars' in
    (xtor, ty_vars, tm_vars', transform_command ctx body h')

  and transform_branches (ctx: focus_ctx) (branches: CTm.branch list) (h: Sub.t) : Target.branch list =
    List.map (fun b -> transform_branch ctx b h) branches

  (*
    - Variable: k Keep (rename h x)
    - Constructor: bindTerms args h (\i vs => LetConstructor n vs (k (Comp i Weak) Z))
    - Match: LetMatch (transformBranches bs h) (k Weak Z)
    - Comatch: LetComatch (transformBranches bs h) (k Weak Z)
    - Destructor: bindTerms args h (\i vs => LetDestructor n vs (k (Comp i Weak) Z))
    - MuLhsPos: LetMatch (eta-branches with k) (transformCommand s (Lift h))
    - MuRhsPos: LetMatch (eta-branches with s) (k Weak Z)
    - MuLhsNeg: LetComatch (eta-branches with s) (k Weak Z)
    - MuRhsNeg: LetComatch (eta-branches with k) (transformCommand s (Lift h))
  *)
  and bind_term (ctx: focus_ctx) (term: CTm.term) (h: Sub.t)
      (k: Sub.t -> Ident.t -> Target.command) : Target.command =
    match term with
    | CTm.Var x ->
        (* Variable: no context extension, apply h to x *)
        k Sub.empty (Sub.apply h x)

    | CTm.Ctor (dec, c, args) ->
        (* bindTerms args h (\i vs => LetConstructor n vs (k (Comp i Weak) Z)) *)
        bind_terms ctx args h (fun i vs ->
          let x = Ident.fresh () in
          Target.LetCtor (dec, c, vs, x, k i x))

    | CTm.Match (dec, bs) ->
        (* LetMatch (transformBranches bs h) (k Weak Z) *)
        let x = Ident.fresh () in
        Target.LetMatch (dec, transform_branches ctx bs h, x, k Sub.empty x)

    | CTm.Comatch (dec, bs) ->
        (* LetComatch (transformBranches bs h) (k Weak Z) *)
        let a = Ident.fresh () in
        Target.LetComatch (dec, transform_branches ctx bs h, a, k Sub.empty a)

    | CTm.Dtor (dec, c, _exist_tys, args) ->
        (* bindTerms args h (\i vs => LetDestructor n vs (k (Comp i Weak) Z)) *)
        bind_terms ctx args h (fun i vs ->
          let a = Ident.fresh () in
          Target.LetDtor (dec, c, vs, a, k i a))

    | CTm.MuPrd (ty, x, s) ->
        (* MuLhsPos: producer (data type focus)
           For data types: LetMatch (eta-branches with k) (transformCommand s)
           For primitives: inline k at the cut point *)
        (match get_dec_from_type ctx.decs ty with
        | Some dec ->
            let branches = List.map (fun (xtor: CTy.xtor) ->
              let ps = fresh_params xtor.argument_types in
              let z = Ident.fresh () in
              (* For instantiated decs, xtor.existentials has the type params to bind.
                 These are fresh metas created by instantiate_dec/instantiate_xtor. *)
              let ty_vars = List.map fst (xtor.quantified @ xtor.existentials) in
              (xtor.name, ty_vars, ps, Target.LetCtor (dec, xtor.name, ps, z, k Sub.empty z))
            ) dec.xtors in
            let x' = Ident.fresh () in
            Target.LetMatch (dec, branches, x', transform_command ctx s (Sub.add x x' h))
        | None ->
            (match ty with
            | CTy.Ext _ ->
                (* Primitive type (int): create a continuation to capture the result.
                   We create LetNewInt to make a new continuation that calls k when a value arrives. *)
                let cont_var = Ident.fresh () in
                let result_var = Ident.fresh () in
                Target.LetNewInt (cont_var, result_var,
                  k Sub.empty result_var,  (* when result arrives, call k *)
                  transform_command ctx s (Sub.add x cont_var h))  (* pass cont_var as the continuation *)
            | CTy.TVar tvar ->
                (* Type variable: can't eta-expand.
                   Use AdministrativeTyped: ⟨µα.s | µ~z.k(z)⟩_T
                   s is the body (producer), k(z) is the continuation (consumer) *)
                let x' = Ident.fresh () in  (* bound in s *)
                let z = Ident.fresh () in   (* bound in continuation *)
                let s' = transform_command ctx s (Sub.add x x' h) in
                let k_body = k Sub.empty z in
                Target.AdministrativeTyped (tvar, x', s', z, k_body)
            | CTy.Forall _ ->
                (* Forall is handled specially in transform_command *)
                failwith "bind_term MuPrd at Forall: should be handled elsewhere"
            | _ ->
                failwith "bind_term MuPrd: unexpected type"))

    | CTm.MuCns (ty, a, s) ->
        (* MuRhsNeg (consumer, codata type focus) 
           For codata: LetComatch (eta-branches with k) (transformCommand s)
           For primitives: inline k at the cut point *)
        (match get_dec_from_type ctx.decs ty with
        | Some dec ->
            let branches = List.map (fun (xtor: CTy.xtor) ->
              let ps = fresh_params xtor.argument_types in
              let z = Ident.fresh () in
              (* For instantiated decs, xtor.existentials has the type params to bind. *)
              let ty_vars = List.map fst (xtor.quantified @ xtor.existentials) in
              (xtor.name, ty_vars, ps,
                Target.LetDtor (dec, xtor.name, ps, z, k Sub.empty z))
            ) dec.xtors in
            let a' = Ident.fresh () in
            Target.LetComatch (dec, branches, a',
              transform_command ctx s (Sub.add a a' h))
        | None ->
            (match ty with
            | CTy.Ext _ ->
                (* Primitive type (int): transform s, inlining k at cuts from a *)
                transform_command_with_prd_cont ctx s h a k
            | CTy.TVar tvar ->
                (* Type variable: can't eta-expand.
                   Use AdministrativeTyped: ⟨µα.k(z) | µ~z.s[a:=z]⟩_T
                   where k is the continuation producing a value z, and s consumes from a *)
                let z = Ident.fresh () in   (* bound in producer from k *)
                let a' = Ident.fresh () in  (* bound in s *)
                let k_body = k Sub.empty z in  (* producer side: "what we do with result" *)
                let s' = transform_command ctx s (Sub.add a a' h) in  (* consumer side: "how to produce" *)
                Target.AdministrativeTyped (tvar, z, k_body, a', s')
            | CTy.Forall _ ->
                (* Forall is handled specially in transform_command *)
                failwith "bind_term MuCns at Forall: should be handled elsewhere"
            | _ ->
                failwith "bind_term MuCns: unexpected type"))

    | CTm.NewForall (_a, k_ty, body_ty, cont, body) ->
        let v = Ident.fresh () in
        let a' = Ident.fresh () in
        (* The cont variable from NewForall is where results go.
           We need to propagate this correctly. *)
        Target.LetNewForall (a', k_ty, body_ty,
          transform_command ctx body (Sub.add cont (Ident.fresh ()) h), v, k Sub.empty v)

    | CTm.InstantiateDtor ty_arg ->
        let a = Ident.fresh () in
        Target.LetInstantiate (a, ty_arg, ty_arg, a, k Sub.empty a)

    | CTm.Lit n ->
        let x = Ident.fresh () in
        Target.LetInt (n, x, k Sub.empty x)

  and bind_terms (ctx: focus_ctx) (terms: CTm.term list) (h: Sub.t)
      (k: Sub.t -> Ident.t list -> Target.command) : Target.command =
    match terms with
    | [] -> k Sub.empty []
    | t :: rest ->
        bind_term ctx t h (fun i v ->
          bind_terms ctx rest (Sub.compose h i) (fun j vs ->
            k (Sub.compose i j) (Sub.apply j v :: vs)))

  (* Transform command for MuPrd at primitive type.
    When we hit a cut that sends to the target consumer variable,
    we inline the continuation k instead of creating CutInt. *)
  and transform_command_with_cont (ctx: focus_ctx) (cmd: CTm.command) (h: Sub.t) 
      (target_cns: Ident.t) (k: Sub.t -> Ident.t -> Target.command) : Target.command =
    match cmd with
    (* The key case: Cut at Ext type where rhs is our target variable *)
    | CTm.Cut (CTy.Ext _, lhs, CTm.Var cns_var) when Ident.equal cns_var target_cns ->
        (* Instead of CutInt(lhs', target), call k with lhs' *)
        bind_term ctx lhs h (fun i v -> k i v)
        
    (* For Add/Sub, check if the continuation IS the target *)
    | CTm.Add (m, n, CTm.Var cns_var) when Ident.equal cns_var target_cns ->
        (* The result of this add should flow to k, not to cns_var *)
        bind_term ctx m h (fun i m' ->
          bind_term ctx n (Sub.compose h i) (fun j n' ->
            let r = Ident.fresh () in
            Target.Add (m', Sub.apply j n', r, k (Sub.compose i j) r)))
            
    | CTm.Sub (m, n, CTm.Var cns_var) when Ident.equal cns_var target_cns ->
        bind_term ctx m h (fun i m' ->
          bind_term ctx n (Sub.compose h i) (fun j n' ->
            let r = Ident.fresh () in
            Target.Sub (m', Sub.apply j n', r, k (Sub.compose i j) r)))
              
    (* General Add/Sub - the continuation is NOT our target, recurse normally *)
    | CTm.Add (m, n, cns) ->
        bind_term ctx m h (fun i m' ->
          bind_term ctx n (Sub.compose h i) (fun j n' ->
            bind_term ctx cns (Sub.compose (Sub.compose h i) j) (fun _l k' ->
              let r = Ident.fresh () in
              Target.Add (m', Sub.apply j n', r, Target.CutInt (r, k')))))
              
    | CTm.Sub (m, n, cns) ->
        bind_term ctx m h (fun i m' ->
          bind_term ctx n (Sub.compose h i) (fun j n' ->
            bind_term ctx cns (Sub.compose (Sub.compose h i) j) (fun _l k' ->
              let r = Ident.fresh () in
              Target.Sub (m', Sub.apply j n', r, Target.CutInt (r, k')))))

    | CTm.Ifz (cond, s1, s2) ->
        bind_term ctx cond h (fun _i v ->
          Target.Ifz (v,
            transform_command_with_cont ctx s1 h target_cns k,
            transform_command_with_cont ctx s2 h target_cns k))

    (* Fall back to regular transformation for other cases *)
    | _ -> transform_command ctx cmd h

  (* Transform command for MuCns at primitive type.
    When we hit a cut where the producer is our target variable,
    we inline the continuation k. *)
  and transform_command_with_prd_cont (ctx: focus_ctx) (cmd: CTm.command) (h: Sub.t) 
      (target_prd: Ident.t) (k: Sub.t -> Ident.t -> Target.command) : Target.command =
    match cmd with
    (* The key case: Cut at Ext type where lhs is our target variable *)
    | CTm.Cut (CTy.Ext _, CTm.Var prd_var, rhs) when Ident.equal prd_var target_prd ->
        bind_term ctx rhs h (fun i v -> k i v)
        
    (* Fall back to regular transformation *)
    | _ -> transform_command ctx cmd h

  and transform_command (ctx: focus_ctx) (cmd: CTm.command) (h: Sub.t) : Target.command =
    match cmd with
    | CTm.End -> Target.End

    | CTm.Ret (ty, term) ->
        bind_term ctx term h (fun _i v -> Target.Ret (ty, v))

    | CTm.Call (path, tys, args) ->
        bind_terms ctx args h (fun _i vs -> Target.Call (path, tys, vs))

    | CTm.Add (m, n, k) ->
        bind_term ctx m h (fun i m' ->
          bind_term ctx n (Sub.compose h i) (fun j n' ->
            bind_term ctx k (Sub.compose (Sub.compose h i) j) (fun _l k' ->
              let r = Ident.fresh () in
              Target.Add (m', Sub.apply j n', r, Target.CutInt (r, k')))))

    | CTm.Sub (m, n, k) ->
        bind_term ctx m h (fun i m' ->
          bind_term ctx n (Sub.compose h i) (fun j n' ->
            bind_term ctx k (Sub.compose (Sub.compose h i) j) (fun _l k' ->
              let r = Ident.fresh () in
              Target.Sub (m', Sub.apply j n', r, Target.CutInt (r, k')))))

    | CTm.Ifz (cond, s1, s2) ->
        bind_term ctx cond h (fun _i v ->
          Target.Ifz (v, transform_command ctx s1 h, transform_command ctx s2 h))

    (* === CUT TRANSFORMATIONS === *)

    (* CutPos (Variable x) (Variable y) - eta expand *)
    | CTm.Cut (CTy.Sgn _ as ty, CTm.Var x, CTm.Var y) ->
        (match get_dec_from_type ctx.decs ty with
        | Some dec when dec.data_sort = Data ->
            (* Positive: CutMatch x [branches: CutCtor n freshNames y] *)
            Target.CutMatch (dec, Sub.apply h x,
              List.map (fun (xtor: CTy.xtor) ->
                let ps = fresh_params xtor.argument_types in
                let ty_vars = List.map fst (xtor.quantified @ xtor.existentials) in
                (xtor.name, ty_vars, ps, Target.CutCtor (dec, xtor.name, ps, Sub.apply h y))
              ) dec.xtors)
        | Some dec ->
            (* Negative: CutComatch [branches: CutDtor x n freshNames] y *)
            Target.CutComatch (dec,
              List.map (fun (xtor: CTy.xtor) ->
                let ps = fresh_params xtor.argument_types in
                let ty_vars = List.map fst (xtor.quantified @ xtor.existentials) in
                (xtor.name, ty_vars, ps, Target.CutDtor (dec, xtor.name, Sub.apply h x, ps))
              ) dec.xtors,
              Sub.apply h y)
        | None ->
            (match ty with
            | CTy.TVar tvar -> Target.CutTyped (tvar, Sub.apply h x, Sub.apply h y)
            | CTy.Ext _ -> Target.CutInt (Sub.apply h x, Sub.apply h y)
            | _ -> failwith "Var/Var cut at unexpected non-declared, non-tvar, non-ext type"))

    (* CutPos (Variable x) (Match bs) *)
    | CTm.Cut (CTy.Sgn _, CTm.Var x, CTm.Match (dec, bs)) ->
        Target.CutMatch (dec, Sub.apply h x, transform_branches ctx bs h)

    (* CutPos (Variable x) (MuRhsPos r) => transform r with x substituted *)
    | CTm.Cut (_, CTm.Var x, CTm.MuCns (_, a, r)) ->
        transform_command ctx r (Sub.add a (Sub.apply h x) h)

    (* CutPos (Constructor n as) (Variable y) *)
    | CTm.Cut (_, CTm.Ctor (dec, c, args), CTm.Var y) ->
        bind_terms ctx args h (fun i vs ->
          Target.CutCtor (dec, c, vs, Sub.apply (Sub.compose h i) y))

    (* CutPos (Constructor n as) (Match bs) - lookup and inline *)
    | CTm.Cut (_, CTm.Ctor (_, c, args), CTm.Match (_, bs)) ->
        bind_terms ctx args h (fun i vs ->
          Target.lookup_branch (transform_branches ctx bs (Sub.compose h i)) c vs)

    (* CutPos (Constructor n as) (MuRhsPos r) *)
    | CTm.Cut (_, CTm.Ctor (dec, c, args), CTm.MuCns (_, a, r)) ->
        bind_terms ctx args h (fun i vs ->
          let z = Ident.fresh () in
          Target.LetCtor (dec, c, vs, z,
            transform_command ctx r (Sub.add a z (Sub.compose h i))))

    (* CutPos (MuLhsPos s) (Variable y) => transform s with y substituted *)
    | CTm.Cut (_, CTm.MuPrd (_, x, s), CTm.Var y) ->
        transform_command ctx s (Sub.add x (Sub.apply h y) h)

    (* CutPos (MuLhsPos s) (Match bs) *)
    | CTm.Cut (_, CTm.MuPrd (_, x, s), CTm.Match (dec, bs)) ->
        let x' = Ident.fresh () in
        Target.LetMatch (dec, transform_branches ctx bs h, x',
          transform_command ctx s (Sub.add x x' h))

    (* CutPos (MuLhsPos s) (MuRhsPos r) - THE KEY CASE
      For data (positive): LetMatch with branches containing r, continuation is s
      For codata (negative): LetComatch with branches containing s, continuation is r *)
    | CTm.Cut (ty, CTm.MuPrd (_, x, s), CTm.MuCns (_, a, r)) ->
        (match get_dec_from_type ctx.decs ty with
        | Some dec when dec.data_sort = Data ->
            (* Positive: LetMatch (branches: LetCtor ps z (transform r [a->z])) (transform s [x->fresh]) *)
            let x' = Ident.fresh () in
            let branches = List.map (fun (xtor: CTy.xtor) ->
              let ps = fresh_params xtor.argument_types in
              let z = Ident.fresh () in
              let ty_vars = List.map fst (xtor.quantified @ xtor.existentials) in
              (xtor.name, ty_vars, ps, 
                Target.LetCtor (dec, xtor.name, ps, z, 
                  transform_command ctx r (Sub.add a z h)))
            ) dec.xtors in
            Target.LetMatch (dec, branches, x', transform_command ctx s (Sub.add x x' h))
        | Some dec ->
            (* Negative: LetComatch (branches: LetDtor ps z (transform s [x->z])) (transform r [a->fresh]) *)
            let a' = Ident.fresh () in
            let branches = List.map (fun (xtor: CTy.xtor) ->
              let ps = fresh_params xtor.argument_types in
              let z = Ident.fresh () in
              let ty_vars = List.map fst (xtor.quantified @ xtor.existentials) in
              (xtor.name, ty_vars, ps,
                Target.LetDtor (dec, xtor.name, ps, z,
                  transform_command ctx s (Sub.add x z h)))
            ) dec.xtors in
            Target.LetComatch (dec, branches, a', transform_command ctx r (Sub.add a a' h))
        | None ->
            (* Not a data/codata type - could be a type variable or external type *)
            (match ty with
            | CTy.TVar tvar ->
                (* Type variable - can't eta expand.
                  Use AdministrativeTyped to represent ⟨µα.s | µ~x.r⟩_T *)
                let x' = Ident.fresh () in
                let a' = Ident.fresh () in
                let s' = transform_command ctx s (Sub.add x x' h) in
                let r' = transform_command ctx r (Sub.add a a' h) in
                Target.AdministrativeTyped (tvar, x', s', a', r')
            | CTy.Ext Int ->
                (* External Int type - for ⟨μ+x.s | μ-a.r⟩ at Int, we need to 
                   create an int continuation. Use LetNewInt to handle this.
                   LetNewInt(k, v, branch, cont) represents:
                     new k = { v => branch }; cont
                   where k is an int continuation (Cns Int) and v is the 
                   value received (Prd Int).
                   
                   For ⟨μ+x.s | μ-a.r⟩:
                   - x is the continuation (Cns Int in Core)
                   - a is the value (Prd Int in Core)
                   - s runs with x available
                   - r runs when x is invoked, with a bound to the received value
                   
                   So we create: new x = { a => r }; s  *)
                let x' = Ident.fresh () in
                let a' = Ident.fresh () in
                let s' = transform_command ctx s (Sub.add x x' h) in
                let r' = transform_command ctx r (Sub.add a a' h) in
                Target.LetNewInt (x', a', r', s')
            | _ ->
                (* Other external/unknown types - shouldn't happen after monomorphization *)
                failwith (Printf.sprintf "Double-mu cut at unsupported type")))

    (* CutNeg (Variable x) (Destructor n as) *)
    | CTm.Cut (_, CTm.Var x, CTm.Dtor (dec, c, _exist_tys, args)) ->
        bind_terms ctx args h (fun i vs ->
          Target.CutDtor (dec, c, Sub.apply (Sub.compose h i) x, vs))

    (* CutNeg (Comatch bs) (Variable y) *)
    | CTm.Cut (_, CTm.Comatch (dec, bs), CTm.Var y) ->
        Target.CutComatch (dec, transform_branches ctx bs h, Sub.apply h y)

    (* CutNeg (Comatch bs) (Destructor n as) - lookup and inline *)
    | CTm.Cut (_, CTm.Comatch (_, bs), CTm.Dtor (_, c, _exist_tys, args)) ->
        bind_terms ctx args h (fun i vs ->
          Target.lookup_branch (transform_branches ctx bs (Sub.compose h i)) c vs)

    (* CutNeg (Comatch bs) (MuRhsNeg r) *)
    | CTm.Cut (_, CTm.Comatch (dec, bs), CTm.MuCns (_, a, r)) ->
        let a' = Ident.fresh () in
        Target.LetComatch (dec, transform_branches ctx bs h, a',
          transform_command ctx r (Sub.add a a' h))

    (* CutNeg (MuLhsNeg s) (Destructor n as) *)
    | CTm.Cut (_, CTm.MuPrd (_, x, s), CTm.Dtor (dec, c, _exist_tys, args)) ->
        bind_terms ctx args h (fun i vs ->
          let z = Ident.fresh () in
          Target.LetDtor (dec, c, vs, z, transform_command ctx s (Sub.add x z (Sub.compose h i))))

    (* Cut at Ext type (Int) *)
    | CTm.Cut (CTy.Ext _, lhs, rhs) ->
        bind_term ctx lhs h (fun i lhs_v ->
          bind_term ctx rhs (Sub.compose h i) (fun _j rhs_v ->
            Target.CutInt (lhs_v, rhs_v)))

    (* Cut at Forall type - special handling *)
    | CTm.Cut (CTy.Forall (a, k_ty, body_ty), lhs, rhs) ->
        transform_cut_forall ctx a k_ty body_ty lhs rhs h

    (* Generic fallback - must be at a type variable *)
    | CTm.Cut (ty, lhs, rhs) ->
        (match ty with
        | CTy.TVar tvar ->
            bind_term ctx lhs h (fun i lhs_v ->
              bind_term ctx rhs (Sub.compose h i) (fun _j rhs_v ->
                Target.CutTyped (tvar, lhs_v, rhs_v)))
        | _ ->
            failwith "Generic Cut fallback: expected TVar type")

  and transform_cut_forall (ctx: focus_ctx) (_a: Ident.t) (k_ty: CTy.typ) (body_ty: CTy.typ)
      (lhs: CTm.term) (rhs: CTm.term) (h: Sub.t) : Target.command =
    match lhs, rhs with
    | CTm.Var x, CTm.Var y ->
        let a' = Ident.fresh () in
        Target.CutNewForall (a', k_ty, body_ty,
          Target.CutInstantiate (a', k_ty, body_ty, Sub.apply h x),
          Sub.apply h y)
    | CTm.Var x, CTm.InstantiateDtor ty_arg ->
        let a' = Ident.fresh () in
        Target.CutInstantiate (a', ty_arg, body_ty, Sub.apply h x)
    | CTm.Var x, CTm.MuCns (_, av, r) ->
        transform_command ctx r (Sub.add av (Sub.apply h x) h)
    | CTm.NewForall (av, _, _, cont, cmd), CTm.InstantiateDtor ty_arg ->
        let ts = TySub.add av ty_arg TySub.empty in
        transform_command ctx (subst_command ts cmd) (Sub.add cont (Ident.fresh ()) h)
    | CTm.NewForall (av, _, _, cont, cmd), CTm.MuCns (_, bv, r) ->
        let v = Ident.fresh () in
        let av' = Ident.fresh () in
        Target.LetNewForall (av', k_ty, body_ty,
          transform_command ctx cmd (Sub.add cont v (Sub.add av av' h)),
          v,
          transform_command ctx r (Sub.add bv v h))
    | CTm.MuPrd (_, x, s), CTm.Var y ->
        transform_command ctx s (Sub.add x (Sub.apply h y) h)
    | _ ->
        bind_term ctx lhs h (fun i lhs_v ->
          bind_term ctx rhs (Sub.compose h i) (fun _j rhs_v ->
            let a' = Ident.fresh () in
            Target.CutNewForall (a', k_ty, body_ty,
              Target.CutInstantiate (a', k_ty, body_ty, lhs_v),
              rhs_v)))

  let transform (decs: CTy.dec Path.tbl) (cmd: CTm.command) : Target.command =
    let ctx = make_focus_ctx decs in
    transform_command ctx cmd Sub.empty
end

(* ========================================================================= *)
(* Collapse: Target → Focused                                                *)
(* ========================================================================= *)

module Collapse = struct
  let rec collapse_branch (ctx: focus_ctx) (parity: bool) ((xtor, ty_vars, tm_vars, body): Target.branch)
      : FTm.branch =
    (xtor, ty_vars, tm_vars, collapse_command ctx parity body)

  and collapse_command (ctx: focus_ctx) (parity: bool) : Target.command -> FTm.command = function
    | Target.LetCtor (dec, c, args, x, cont) ->
        FTm.Let (x, collapse_dec ctx dec, c, args, collapse_command ctx parity cont)
    | Target.LetDtor (dec, c, args, a, cont) ->
        FTm.Let (a, collapse_dec ctx dec, c, args, collapse_command ctx parity cont)
    | Target.LetMatch (dec, branches, x, cont) ->
        FTm.New (x, collapse_dec ctx dec, List.map (collapse_branch ctx parity) branches, 
          collapse_command ctx parity cont)
    | Target.LetComatch (dec, branches, a, cont) ->
        FTm.New (a, collapse_dec ctx dec, List.map (collapse_branch ctx parity) branches, 
          collapse_command ctx parity cont)
    | Target.CutCtor (dec, c, args, a) ->
        FTm.Invoke (a, collapse_dec ctx dec, c, args)
    | Target.CutDtor (dec, c, x, args) ->
        FTm.Invoke (x, collapse_dec ctx dec, c, args)
    | Target.CutMatch (dec, x, branches) ->
        FTm.Switch (x, collapse_dec ctx dec, List.map (collapse_branch ctx parity) branches)
    | Target.CutComatch (dec, branches, a) ->
        FTm.Switch (a, collapse_dec ctx dec, List.map (collapse_branch ctx parity) branches)
    | Target.LetInstantiate _ -> failwith "Unexpected LetInstantiate -- not monomorphic"
    | Target.LetNewForall _ -> failwith "Unexpected LetNewForall -- not monomorphic"
    | Target.CutInstantiate _ -> failwith "Unexpected CutInstantiate -- not monomorphic"
    | Target.CutNewForall _ -> failwith "Unexpected CutNewForall -- not monomorphic"
    | Target.LetInt (n, x, cont) -> FTm.Lit (n, x, collapse_command ctx parity cont)
    | Target.LetNewInt (k, v, branch, cont) -> 
        FTm.NewInt (k, v, collapse_command ctx parity branch, collapse_command ctx parity cont)
    | Target.CutInt (x, k) -> FTm.Axiom (Int, x, k)
    | Target.CutTyped _ -> failwith "Unexpected CutTyped -- type variable not eliminated by monomorphization"
    | Target.AdministrativeTyped _ -> failwith "Unexpected AdministrativeTyped -- type variable not eliminated by monomorphization"
    | Target.Add (x, y, k, cont) -> FTm.Add (x, y, k, collapse_command ctx parity cont)
    | Target.Sub (x, y, k, cont) -> FTm.Sub (x, y, k, collapse_command ctx parity cont)
    | Target.Ifz (v, s1, s2) -> FTm.Ifz (v, collapse_command ctx parity s1, collapse_command ctx parity s2)
    | Target.Call (path, [], args) -> FTm.Jump (path, args)
    | Target.Call _ -> failwith "Unexpected type args in Call -- not monomorphic"
    | Target.Ret (ty, x) -> FTm.Ret (focus_type ty, x)
    | Target.End -> FTm.End

  let focus_command (decs: CTy.dec Path.tbl) (cmd: CTm.command) : FTm.command =
    let ctx = make_focus_ctx decs in
    collapse_command ctx false (Transform.transform decs cmd)
end

(* ========================================================================= *)
(* Entry Points                                                              *)
(* ========================================================================= *)

let focus_command = Collapse.focus_command

let focus_def (decs: CTy.dec Path.tbl) (def: CTm.definition) : FTm.definition =
  let ctx = make_focus_ctx decs in
  { path = def.path
  ; term_params = List.map (fun (a, k_ty) -> (a, collapse_chiral ctx k_ty)) def.term_params
  ; body = focus_command decs def.body
  }

let focus_decs (decs: CTy.dec Path.tbl) : FTy.dec Path.tbl =
  let ctx = make_focus_ctx decs in
  Path.map_tbl (fun dec -> collapse_dec ctx dec) decs
