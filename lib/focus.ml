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

(** Context for transformation - holds type declarations *)
type focus_ctx = { decs: CTy.dec Path.tbl }

(* ========================================================================= *)
(* Type Substitution                                                         *)
(* ========================================================================= *)

(** Type substitution: maps type variables to types *)
module TySub = struct
  type t = CTy.typ Ident.tbl
  let empty : t = Ident.emptytbl
  let add (v: Ident.t) (ty: CTy.typ) (s: t) : t = Ident.add v ty s
  let find_opt (v: Ident.t) (s: t) : CTy.typ option = Ident.find_opt v s
  let apply (s: t) (v: Ident.t) : CTy.typ = 
    match find_opt v s with Some ty -> ty | None -> CTy.TVar v
end

(** Apply type substitution to a Core type *)
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
  match ct with
  | CB.Prd t -> CB.Prd (subst_type ts t)
  | CB.Cns t -> CB.Cns (subst_type ts t)

(** Apply type substitution to an xtor *)
let subst_xtor (ts: TySub.t) (x: CTy.xtor) : CTy.xtor =
  { name = x.name
  ; quantified = List.map (fun (v, k) -> (v, subst_type ts k)) x.quantified
  ; existentials = List.map (fun (v, k) -> (v, subst_type ts k)) x.existentials
  ; argument_types = List.map (subst_chiral_type ts) x.argument_types
  ; main = subst_type ts x.main
  }

(** Apply type substitution to a declaration *)
let subst_dec (ts: TySub.t) (d: CTy.dec) : CTy.dec =
  { name = d.name
  ; polarity = d.polarity
  ; param_kinds = List.map (subst_type ts) d.param_kinds
  ; type_args = List.map (subst_type ts) d.type_args
  ; xtors = List.map (subst_xtor ts) d.xtors
  }

(** Apply type substitution to a Core term *)
let rec subst_term (ts: TySub.t) (t: CTm.term) : CTm.term =
  match t with
  | CTm.Var v -> CTm.Var v
  | CTm.Ctor (dec, c, args) -> CTm.Ctor (subst_dec ts dec, c, List.map (subst_term ts) args)
  | CTm.Dtor (dec, c, args) -> CTm.Dtor (subst_dec ts dec, c, List.map (subst_term ts) args)
  | CTm.Match (dec, bs) -> CTm.Match (subst_dec ts dec, List.map (subst_branch ts) bs)
  | CTm.Comatch (dec, bs) -> CTm.Comatch (subst_dec ts dec, List.map (subst_branch ts) bs)
  | CTm.MuPrd (ty, v, cmd) -> CTm.MuPrd (subst_type ts ty, v, subst_command ts cmd)
  | CTm.MuCns (ty, v, cmd) -> CTm.MuCns (subst_type ts ty, v, subst_command ts cmd)
  | CTm.NewForall (v, k, body_ty, cmd) -> 
      CTm.NewForall (v, subst_type ts k, subst_type ts body_ty, subst_command ts cmd)
  | CTm.InstantiateDtor ty -> CTm.InstantiateDtor (subst_type ts ty)
  | CTm.Lit n -> CTm.Lit n

and subst_branch (ts: TySub.t) (xtor, ty_vars, tm_vars, cmd) : CTm.branch =
  (xtor, ty_vars, tm_vars, subst_command ts cmd)

and subst_command (ts: TySub.t) (cmd: CTm.command) : CTm.command =
  match cmd with
  | CTm.Cut (ty, lhs, rhs) -> CTm.Cut (subst_type ts ty, subst_term ts lhs, subst_term ts rhs)
  | CTm.Add (m, n, k) -> CTm.Add (subst_term ts m, subst_term ts n, subst_term ts k)
  | CTm.Ifz (cond, s1, s2) -> CTm.Ifz (subst_term ts cond, subst_command ts s1, subst_command ts s2)
  | CTm.Ret (ty, t) -> CTm.Ret (subst_type ts ty, subst_term ts t)
  | CTm.Call (p, tys, args) -> CTm.Call (p, List.map (subst_type ts) tys, List.map (subst_term ts) args)
  | CTm.End -> CTm.End

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

(** Get an instantiated dec from a signature type.
    This is needed for transform_mu_cns/transform_mu_prd when building branches. *)
let get_instantiated_dec_from_type (ty: CTy.typ) : CTy.dec option =
  match ty with
  | CTy.Sgn (s, type_args) ->
      let base_dec = 
        if Path.equal s Prim.fun_sym then Some CTy.fun_dec
        else if Path.equal s Prim.raise_sym then Some CTy.raise_dec
        else if Path.equal s Prim.lower_sym then Some CTy.lower_dec
        else None (* TODO: could lookup user-defined decs *)
      in
      Option.map (fun d -> CTy.instantiate_dec d type_args) base_dec
  | _ -> None

(* ========================================================================= *)
(* Type Encoding (Core → Focused)                                            *)
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

(** Collapse chirality: flip based on the INNER TYPE's polarity.
    Like simple.ml: Lhs (Neg _) → Rhs, Rhs (Neg _) → Lhs.
    This is the key insight: chirality flips when the wrapped type is negative. *)
let collapse_chiral (ct: CTy.chiral_typ) : FTy.chiral_typ =
  match ct with
  | CB.Prd t -> 
      if is_negative t then FB.Cns (focus_type t) else FB.Prd (focus_type t)
  | CB.Cns t -> 
      if is_negative t then FB.Prd (focus_type t) else FB.Cns (focus_type t)

(** Collapse an xtor - chirality flip is determined per-argument by argument type *)
let collapse_xtor (_is_neg: bool) (x: CTy.xtor) : FTy.xtor =
  { name = x.name
  ; quantified = List.map (fun (v, k) -> (v, focus_type k)) x.quantified
  ; existentials = List.map (fun (v, k) -> (v, focus_type k)) x.existentials
  ; argument_types = List.map collapse_chiral x.argument_types
  ; main = focus_type x.main
  }

(** Collapse a declaration: convert Core dec to Focused dec with chirality flipping.
    This is analogous to simple.ml's collapse_sig applied to each xtor. *)
let collapse_dec (d: CTy.dec) : FTy.dec =
  let is_neg = (d.polarity = CB.Neg) in
  { name = d.name
  ; polarity = FB.Typ
  ; param_kinds = List.map focus_type d.param_kinds
  ; type_args = List.map focus_type d.type_args
  ; xtors = List.map (collapse_xtor is_neg) d.xtors
  }

(** Get an instantiated Core declaration *)
let get_instantiated_dec (ctx: focus_ctx) (dec_name: Path.t) (type_args: CTy.typ list) : CTy.dec =
  match Path.find_opt dec_name ctx.decs with
  | Some dec -> CTy.instantiate_dec dec type_args
  | None -> failwith ("Unknown declaration: " ^ Path.name dec_name)

(** Get an instantiated and collapsed declaration *)
let get_collapsed_dec (ctx: focus_ctx) (dec_name: Path.t) (type_args: CTy.typ list) : FTy.dec =
  collapse_dec (get_instantiated_dec ctx dec_name type_args)

(* Deprecated - kept for compatibility but unused *)
let focus_xtor (x: CTy.xtor) : FTy.xtor =
  { name = x.name
  ; quantified = List.map (fun (v, k) -> (v, focus_type k)) x.quantified
  ; existentials = List.map (fun (v, k) -> (v, focus_type k)) x.existentials
  ; argument_types = List.map (function
      | CB.Prd t -> FB.Prd (focus_type t)
      | CB.Cns t -> FB.Cns (focus_type t)) x.argument_types
  ; main = focus_type x.main
  }

let focus_dec (d: CTy.dec) : FTy.dec =
  { name = d.name
  ; polarity = FB.Typ
  ; param_kinds = List.map focus_type d.param_kinds
  ; type_args = List.map focus_type d.type_args
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
  
  This is analogous to simple.ml's Target module. The Target language holds
  instantiated Core declarations (CTy.dec) so we can apply collapse_dec during
  the Collapse phase.
  
  Key forms:
  - LetCtor/LetDtor: bind a producer/consumer from an xtor application
  - LetMatch/LetComatch: bind a result from building a pattern/copattern
  - CutCtor/CutDtor: invoke an xtor against a continuation
  - CutMatch/CutComatch: invoke a pattern/copattern against a value
  
  Forall is handled specially because it has type-level binding.
*)
module Target = struct

  type command =
    (* User-defined and primitive xtors - now hold instantiated dec *)
    | LetCtor of CTy.dec * Path.t * Ident.t list * Ident.t * command
    | LetDtor of CTy.dec * Path.t * Ident.t list * Ident.t * command
    | LetMatch of CTy.dec * branch list * Ident.t * command
    | LetComatch of CTy.dec * branch list * Ident.t * command
    | CutCtor of CTy.dec * Path.t * Ident.t list * Ident.t
    | CutDtor of CTy.dec * Path.t * Ident.t * Ident.t list
    | CutMatch of CTy.dec * Ident.t * branch list
    | CutComatch of CTy.dec * branch list * Ident.t
    (* Built-in Forall type - needs special handling *)
    | LetInstantiate of Ident.t * CTy.typ * CTy.typ * Ident.t * command
    | LetNewForall of Ident.t * CTy.typ * CTy.typ * command * Ident.t * command
    | CutInstantiate of Ident.t * CTy.typ * CTy.typ * Ident.t
    | CutNewForall of Ident.t * CTy.typ * CTy.typ * command * Ident.t
    (* Primitives *)
    | LetInt of int * Ident.t * command
    | CutInt of Ident.t * Ident.t
    | CutTyped of CTy.typ * Ident.t * Ident.t  (* Generic cut with type annotation *)
    | LetIntCns of Ident.t * Ident.t * command * command  (* new k = { v => s1 }; s2 - Int consumer binding *)
    | Add of Ident.t * Ident.t * Ident.t * command
    | Ifz of Ident.t * command * command
    | Call of Path.t * CTy.typ list * Ident.t list
    (* Terminals *)
    | Ret of CTy.typ * Ident.t
    | End

  and branch = Path.t * Ident.t list * Ident.t list * command

  (** Int consumer declaration - following simple.ml's int_sig = [[Lhs Int]].
      A "data type" with one constructor taking one Int argument.
      Used when we need to create an Int consumer via LetMatch. *)
  let int_xtor_sym = Path.of_primitive 998 "int_val"
  let int_dec : CTy.dec = 
    { name = Path.of_primitive 999 "int_consumer"
    ; polarity = CB.Pos  (* positive/data - consumers receive values *)
    ; param_kinds = []
    ; type_args = []
    ; xtors = [{ name = int_xtor_sym
               ; quantified = []
               ; existentials = []
               ; argument_types = [CB.Prd (CTy.Ext Common.Types.Int)]  (* Producer of Int *)
               ; main = CTy.Ext Common.Types.Int }]
    }

  (** Apply renaming to a command *)
  let rec rename_command (h: Sub.t) : command -> command = function
    | LetCtor (dec, c, args, x, cont) ->
        let x' = Ident.fresh () in
        LetCtor (dec, c, List.map (Sub.apply h) args, x',
          rename_command (Sub.add x x' h) cont)
    | LetDtor (dec, c, args, a, cont) ->
        let a' = Ident.fresh () in
        LetDtor (dec, c, List.map (Sub.apply h) args, a',
          rename_command (Sub.add a a' h) cont)
    | LetMatch (dec, branches, x, cont) ->
        let x' = Ident.fresh () in
        LetMatch (dec, List.map (rename_branch h) branches, x',
          rename_command (Sub.add x x' h) cont)
    | LetComatch (dec, branches, a, cont) ->
        let a' = Ident.fresh () in
        LetComatch (dec, List.map (rename_branch h) branches, a',
          rename_command (Sub.add a a' h) cont)
    | CutCtor (dec, c, args, a) ->
        CutCtor (dec, c, List.map (Sub.apply h) args, Sub.apply h a)
    | CutDtor (dec, c, x, args) ->
        CutDtor (dec, c, Sub.apply h x, List.map (Sub.apply h) args)
    | CutMatch (dec, x, branches) ->
        CutMatch (dec, Sub.apply h x, List.map (rename_branch h) branches)
    | CutComatch (dec, branches, a) ->
        CutComatch (dec, List.map (rename_branch h) branches, Sub.apply h a)
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
    | CutTyped (ty, x, a) ->
        CutTyped (ty, Sub.apply h x, Sub.apply h a)
    | LetIntCns (k, v, branch_body, cont) ->
        let k' = Ident.fresh () in
        let v' = Ident.fresh () in
        LetIntCns (k', v', rename_command (Sub.add v v' h) branch_body,
          rename_command (Sub.add k k' h) cont)
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

(**
  Transform Core to Target.
  
  Core AST now holds instantiated declarations directly in Ctor, Dtor, Match, Comatch.
  We pass these through to Target, and Collapse will apply collapse_dec.
*)
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

  (** Bind a single term, calling continuation with the resulting variable.
      Core AST holds instantiated dec directly. *)
  and bind_term (term: CTm.term) (h: Sub.t)
      (k: Ident.t -> Target.command) : Target.command =
    match term with
    | CTm.Var x ->
        k (Sub.apply h x)

    | CTm.Ctor (dec, c, args) ->
        bind_terms args h (fun arg_vars ->
          let x = Ident.fresh () in
          Target.LetCtor (dec, c, arg_vars, x, k x))

    | CTm.Dtor (dec, c, args) ->
        bind_terms args h (fun arg_vars ->
          let a = Ident.fresh () in
          Target.LetDtor (dec, c, arg_vars, a, k a))

    | CTm.Match (dec, bs) ->
        let x = Ident.fresh () in
        Target.LetMatch (dec, transform_branches bs h, x, k x)

    | CTm.Comatch (dec, bs) ->
        let a = Ident.fresh () in
        Target.LetComatch (dec, transform_branches bs h, a, k a)

    | CTm.MuPrd (ty, x, s) ->
        transform_mu_prd ty x s h k

    | CTm.MuCns (ty, a, s) ->
        transform_mu_cns ty a s h k

    | CTm.NewForall (a, k_ty, body_ty, body) ->
        (* The body is typically Cut[ty](producer, Var alpha) where alpha is the
           return continuation for the polymorphic value.
           
           We need to bind alpha in the transformed code. The strategy:
           1. Extract alpha from the body pattern Cut(_, _, Var alpha)
           2. Use substitution to map alpha to a bound variable
           3. Create appropriate structure to handle the result *)
        let v = Ident.fresh () in
        let a' = Ident.fresh () in
        (match body with
        | CTm.Cut (ty, _producer, CTm.Var alpha) ->
            (* Create a result consumer that will receive the produced value *)
            let result_k = Ident.fresh () in
            (* Map the type variable and the continuation variable alpha -> result_k *)
            let h' = Sub.add a a' (Sub.add alpha result_k h) in
            (* For signature types, we need to create a proper eta-expanded structure.
               The key insight: we create LetComatch/LetMatch that BINDS result_k,
               then in the body, alpha gets substituted to result_k by h'. *)
            (match get_instantiated_dec_from_type ty with
            | Some dec when dec.polarity = CB.Neg ->
                (* Negative type (like fun): create comatch that receives codata *)
                Target.LetNewForall (a', k_ty, body_ty,
                  Target.LetComatch (dec, 
                    List.map (fun (xtor: CTy.xtor) ->
                      let params = List.map (fun _ -> Ident.fresh ()) xtor.argument_types in
                      (xtor.name, [], params, Target.CutDtor (dec, xtor.name, result_k, params))
                    ) dec.xtors,
                    result_k,
                    (* Pass the ORIGINAL body - substitution h' maps alpha to result_k *)
                    transform_command body h'),
                  v, k v)
            | Some dec ->
                (* Positive type: create match that receives data *)
                Target.LetNewForall (a', k_ty, body_ty,
                  Target.LetMatch (dec,
                    List.map (fun (xtor: CTy.xtor) ->
                      let params = List.map (fun _ -> Ident.fresh ()) xtor.argument_types in
                      (xtor.name, [], params, Target.CutCtor (dec, xtor.name, params, result_k))
                    ) dec.xtors,
                    result_k,
                    (* Pass the ORIGINAL body - substitution h' maps alpha to result_k *)
                    transform_command body h'),
                  v, k v)
            | None ->
                (* Non-signature type - just use substitution *)
                Target.LetNewForall (a', k_ty, body_ty,
                  transform_command body h',
                  v, k v))
        | _ ->
            (* Fallback to generic transformation *)
            Target.LetNewForall (a', k_ty, body_ty,
              transform_command body (Sub.add a a' h),
              v, k v))

    | CTm.InstantiateDtor ty_arg ->
        let a = Ident.fresh () in
        Target.LetInstantiate (a, ty_arg, ty_arg, a, k a)

    | CTm.Lit n ->
        let x = Ident.fresh () in
        Target.LetInt (n, x, k x)

  (** Transform MuPrd: producer binding.
      Following simple.ml's MuLhsPos pattern - creates LetMatch with η-expanded branches. *)
  and transform_mu_prd (ty: CTy.typ) (x: Ident.t) (s: CTm.command) (h: Sub.t)
      (k: Ident.t -> Target.command) : Target.command =
    match ty with
    | CTy.Sgn (_, _) ->
        (* For signature types, create LetMatch following simple.ml's MuLhsPos pattern.
           Each branch: when constructor n with params, let bound = Cn(params); k bound *)
        (match get_instantiated_dec_from_type ty with
        | Some dec ->
            let bound = Ident.fresh () in
            let branches = List.map (fun (xtor: CTy.xtor) ->
              let params = List.map (fun _ -> Ident.fresh ()) xtor.argument_types in
              (xtor.name, [], params, Target.LetCtor (dec, xtor.name, params, bound, k bound))
            ) dec.xtors in
            Target.LetMatch (dec, branches, x, transform_command s (Sub.add x x h))
        | None ->
            (* Fallback - just transform inner command *)
            transform_command s (Sub.add x x h))

    | CTy.Forall (_a, k_ty, body_ty) ->
        let bound = Ident.fresh () in
        let a' = Ident.fresh () in
        let inner = Target.LetInstantiate (a', k_ty, body_ty, bound, k bound) in
        Target.LetNewForall (a', k_ty, body_ty, inner, x,
          transform_command s (Sub.add x x h))

    | CTy.Ext _ ->
        (* For external types like Int, following simple.ml's MuInt pattern:
           Transform s, then replace CutInt(v, x') with k(v).
           This mirrors simple.ml's CutInt(MuInt(x,s), MuInt(a,r)) handling. *)
        let x' = Ident.fresh () in
        let transformed_s = transform_command s (Sub.add x x' h) in
        (* Replace CutInt(v, x') with k(v), and create Int consumers where x' is passed *)
        let rec replace_cutint cmd =
          match cmd with
          | Target.CutInt (v, a) when Ident.equal a x' -> k v
          | Target.CutInt (v, a) -> Target.CutInt (v, a)
          | Target.CutTyped (ty, v, a) -> Target.CutTyped (ty, v, a)
          (* CutDtor where x' is an argument - x' is being passed as an Int consumer.
             Create an Int consumer binding via LetIntCns that has type Cns Int. *)
          | Target.CutDtor (dec, xtor, v, args) ->
              if List.exists (Ident.equal x') args then
                (* Replace x' with a fresh Int consumer that calls k *)
                let int_consumer = Ident.fresh () in
                let result_v = Ident.fresh () in
                let new_args = List.map (fun a -> if Ident.equal a x' then int_consumer else a) args in
                (* LetIntCns(k, v, branch_body, cont) binds k : Cns Int, v is the received Int *)
                Target.LetIntCns (int_consumer, result_v, k result_v,
                  Target.CutDtor (dec, xtor, v, new_args))
              else
                Target.CutDtor (dec, xtor, v, args)
          | Target.LetCtor (dec, c, args, y, cont) ->
              Target.LetCtor (dec, c, args, y, replace_cutint cont)
          | Target.LetDtor (dec, c, args, y, cont) ->
              Target.LetDtor (dec, c, args, y, replace_cutint cont)
          | Target.LetMatch (dec, bs, y, cont) ->
              Target.LetMatch (dec, List.map replace_cutint_branch bs, y, replace_cutint cont)
          | Target.LetComatch (dec, bs, y, cont) ->
              Target.LetComatch (dec, List.map replace_cutint_branch bs, y, replace_cutint cont)
          | Target.LetInt (n, y, cont) ->
              Target.LetInt (n, y, replace_cutint cont)
          | Target.LetIntCns (k, v, branch, cont) ->
              Target.LetIntCns (k, v, replace_cutint branch, replace_cutint cont)
          | Target.Add (m, n, r, cont) ->
              Target.Add (m, n, r, replace_cutint cont)
          | Target.LetInstantiate (a, kty, body_ty, y, cont) ->
              Target.LetInstantiate (a, kty, body_ty, y, replace_cutint cont)
          | Target.LetNewForall (a, kty, body_ty, body, y, cont) ->
              Target.LetNewForall (a, kty, body_ty, replace_cutint body, y, replace_cutint cont)
          | Target.CutInstantiate (a, ty, body_ty, v) ->
              Target.CutInstantiate (a, ty, body_ty, v)
          | Target.CutNewForall (a, kty, body_ty, body, y) ->
              Target.CutNewForall (a, kty, body_ty, replace_cutint body, y)
          | Target.Call (path, tys, args) ->
              Target.Call (path, tys, args)
          | Target.Ifz (cond, s1, s2) ->
              Target.Ifz (cond, replace_cutint s1, replace_cutint s2)
          | Target.Ret (dec, v) -> Target.Ret (dec, v)
          | Target.CutCtor _ | Target.CutMatch _ 
          | Target.CutComatch _ | Target.End -> cmd
        and replace_cutint_branch (xtor, ty_vars, tm_vars, body) =
          (xtor, ty_vars, tm_vars, replace_cutint body)
        in
        replace_cutint transformed_s

    | _ ->
        transform_command s (Sub.add x x h)

  (** Transform MuCns: consumer binding.
      When used as a term to bind (not at top level of cut), we need to create
      a LetComatch that responds to destructor calls.
      Following simple.ml's MuRhsNeg pattern. *)
  and transform_mu_cns (ty: CTy.typ) (a: Ident.t) (s: CTm.command) (h: Sub.t)
      (k: Ident.t -> Target.command) : Target.command =
    match ty with
    | CTy.Sgn (_, _) ->
        (* For signature types, create a LetComatch following simple.ml's pattern.
           Each branch responds to a destructor by binding result and calling k. *)
        (match get_instantiated_dec_from_type ty with
        | Some dec ->
            let bound = Ident.fresh () in
            let branches = List.map (fun (xtor: CTy.xtor) ->
              let params = List.map (fun _ -> Ident.fresh ()) xtor.argument_types in
              (xtor.name, [], params, Target.LetDtor (dec, xtor.name, params, bound, k bound))
            ) dec.xtors in
            Target.LetComatch (dec, branches, a, transform_command s (Sub.add a a h))
        | None ->
            (* Fallback for non-primitive types - just transform inner command *)
            transform_command s (Sub.add a a h))

    | CTy.Forall (_tv, k_ty, body_ty) ->
        let bound = Ident.fresh () in
        let tv' = Ident.fresh () in
        let a' = Ident.fresh () in
        let inner_body = Target.LetInstantiate (tv', k_ty, body_ty, a',
          transform_command s (Sub.add a a' h)) in
        Target.LetNewForall (tv', k_ty, body_ty, inner_body, bound, k bound)

    | CTy.Ext _ ->
        (* For external types like Int, just transform the inner command.
           MuCns(Int, a, s) means "bind a to received Int and run s" *)
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
    (* Cut at a signature type - pass the type for eta-expansion *)
    | CTm.Cut ((CTy.Sgn (_, _) as ty), lhs, rhs) ->
        transform_cut_sgn ty lhs rhs h

    (* Cut at Forall type *)
    | CTm.Cut (CTy.Forall (a, k_ty, body_ty), lhs, rhs) ->
        transform_cut_forall a k_ty body_ty lhs rhs h

    (* Cut at Ext type (e.g., Int) - handle MuPrd/MuCns specially *)
    | CTm.Cut (CTy.Ext _, CTm.MuPrd (_, x, s), CTm.Var y) ->
        transform_command s (Sub.add x (Sub.apply h y) h)
    | CTm.Cut (CTy.Ext _, CTm.Var x, CTm.MuCns (_, a, s)) ->
        transform_command s (Sub.add a (Sub.apply h x) h)
    (* General case: any producer LHS against MuCns consumer - bind LHS and substitute *)
    | CTm.Cut (CTy.Ext _, lhs, CTm.MuCns (_, a, s)) ->
        bind_term lhs h (fun lhs_var ->
          transform_command s (Sub.add a lhs_var h))
    | CTm.Cut (CTy.Ext _, lhs, rhs) ->
        bind_term lhs h (fun lhs_var ->
          bind_term rhs h (fun rhs_var ->
            Target.CutInt (lhs_var, rhs_var)))

    (* Other cuts - fallback, also handle MuPrd/MuCns *)
    | CTm.Cut (_, CTm.MuPrd (_, x, s), CTm.Var y) ->
        transform_command s (Sub.add x (Sub.apply h y) h)
    | CTm.Cut (_, CTm.Var x, CTm.MuCns (_, a, s)) ->
        transform_command s (Sub.add a (Sub.apply h x) h)
    (* General case: any producer LHS against MuCns consumer *)
    | CTm.Cut (_, lhs, CTm.MuCns (_, a, s)) ->
        bind_term lhs h (fun lhs_var ->
          transform_command s (Sub.add a lhs_var h))
    | CTm.Cut (ty, lhs, rhs) ->
        bind_term lhs h (fun lhs_var ->
          bind_term rhs h (fun rhs_var ->
            Target.CutTyped (ty, lhs_var, rhs_var)))

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

    (* Explicit return - transform to Target.Ret *)
    | CTm.Ret (ty, term) ->
        bind_term term h (fun v ->
          Target.Ret (ty, v))

    | CTm.End -> Target.End

  (** Transform cut at signature type - extract dec from terms or eta-expand *)
  and transform_cut_sgn (ty: CTy.typ) (lhs: CTm.term) (rhs: CTm.term) (h: Sub.t) : Target.command =
    match lhs, rhs with
    | CTm.Var x, CTm.Var y ->
        (* Both variables - need to eta-expand based on polarity.
           Like simple.ml: Var-Var at positive type creates CutMatch,
           at negative type creates CutComatch. *)
        (match get_instantiated_dec_from_type ty with
        | Some dec ->
            if dec.polarity = CB.Neg then
              (* Negative (codata): create CutComatch with eta-expanded branches *)
              Target.CutComatch (dec,
                List.map (fun (xtor: CTy.xtor) ->
                  let params = List.map (fun _ -> Ident.fresh ()) xtor.argument_types in
                  (xtor.name, [], params, Target.CutDtor (dec, xtor.name, Sub.apply h x, params))
                ) dec.xtors,
                Sub.apply h y)
            else
              (* Positive (data): create CutMatch with eta-expanded branches *)
              Target.CutMatch (dec, Sub.apply h x,
                List.map (fun (xtor: CTy.xtor) ->
                  let params = List.map (fun _ -> Ident.fresh ()) xtor.argument_types in
                  (xtor.name, [], params, Target.CutCtor (dec, xtor.name, params, Sub.apply h y))
                ) dec.xtors)
        | None ->
            (* Fallback: just substitute (shouldn't happen for primitive types) *)
            Target.CutInt (Sub.apply h x, Sub.apply h y))

    | CTm.Var x, CTm.Match (dec, bs) ->
        Target.CutMatch (dec, Sub.apply h x, transform_branches bs h)

    | CTm.Var x, CTm.MuCns (_, a, r) ->
        transform_command r (Sub.add a (Sub.apply h x) h)

    | CTm.Ctor (dec, c, args), CTm.Var y ->
        bind_terms args h (fun arg_vars ->
          Target.CutCtor (dec, c, arg_vars, Sub.apply h y))

    | CTm.Ctor (_, c, args), CTm.Match (_dec, bs) ->
        bind_terms args h (fun arg_vars ->
          let branches = transform_branches bs h in
          Target.lookup_branch_body branches c arg_vars)

    | CTm.Ctor (dec, c, args), CTm.MuCns (_, a, r) ->
        bind_terms args h (fun arg_vars ->
          let a' = Ident.fresh () in
          Target.LetCtor (dec, c, arg_vars, a',
            transform_command r (Sub.add a a' h)))

    | CTm.MuPrd (_, x, s), CTm.Var y ->
        transform_command s (Sub.add x (Sub.apply h y) h)

    | CTm.MuPrd (_, x, s), CTm.Match (dec, bs) ->
        let x' = Ident.fresh () in
        Target.LetMatch (dec, transform_branches bs h, x',
          transform_command s (Sub.add x x' h))

    | CTm.MuPrd (_, x, s), CTm.MuCns (_, _a, _r) ->
        (* No dec available - this should be simplified *)
        transform_command s (Sub.add x x h)

    | CTm.Comatch (dec, bs), CTm.Var y ->
        Target.CutComatch (dec, transform_branches bs h, Sub.apply h y)

    | CTm.Comatch (_, bs), CTm.Dtor (_dec, c, args) ->
        bind_terms args h (fun arg_vars ->
          Target.lookup_branch_body (transform_branches bs h) c arg_vars)

    | CTm.Comatch (dec, bs), CTm.MuCns (_, a, r) ->
        let a' = Ident.fresh () in
        Target.LetComatch (dec, transform_branches bs h, a',
          transform_command r (Sub.add a a' h))

    | CTm.MuPrd (_, x, s), CTm.Dtor (dec, c, args) ->
        bind_terms args h (fun arg_vars ->
          let x' = Ident.fresh () in
          (* Special case: if s is Cut[Forall](NewForall(..., Cut(_, _, Var alpha)), InstantiateDtor),
             we need to add alpha -> x' to the substitution so the inner result goes to x' *)
          let h' = match s with
            | CTm.Cut (CTy.Forall _, CTm.NewForall (_, _, _, inner_cmd), CTm.InstantiateDtor _) ->
                (match inner_cmd with
                | CTm.Cut (_, _, CTm.Var alpha) ->
                    Sub.add alpha x' (Sub.add x x' h)
                | _ -> Sub.add x x' h)
            | _ -> Sub.add x x' h
          in
          Target.LetDtor (dec, c, arg_vars, x',
            transform_command s h'))

    | CTm.Var x, CTm.Dtor (dec, c, args) ->
        bind_terms args h (fun arg_vars ->
          Target.CutDtor (dec, c, Sub.apply h x, arg_vars))

    | _ ->
        bind_term lhs h (fun lhs_var ->
          bind_term rhs h (fun rhs_var ->
            Target.CutTyped (ty, lhs_var, rhs_var)))

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

    | CTm.NewForall (av, _, _, cmd), CTm.InstantiateDtor ty_arg ->
        (* When instantiating a NewForall at ty_arg, the inner cmd is Cut[body_ty](producer, Var alpha).
           We need to:
           1. Substitute ty_arg for av in all types within cmd
           2. The alpha should be in the substitution (added by outer MuPrd,Dtor handling)
           3. Transform the substituted cmd *)
        let ts = TySub.add av ty_arg TySub.empty in
        let cmd' = subst_command ts cmd in
        transform_command cmd' h

    | CTm.NewForall (av, _, _, cmd), CTm.MuCns (_, bv, r) ->
        (* The cmd is typically Cut[body_ty](producer, Var alpha) where alpha is the
           implicit return continuation. For polymorphic functions, the producer IS
           the result value. We need to build it and bind it to the output. 
           
           Strategy: Create LetComatch/LetMatch that builds the value, then End.
           The Forall machinery will capture this value. *)
        let v = Ident.fresh () in
        let av' = Ident.fresh () in
        let h' = Sub.add av av' h in
        let body_cmd = 
          match cmd with
          | CTm.Cut (ty, producer, CTm.Var _alpha) ->
              (* Build the producer value and bind it *)
              (match producer with
              | CTm.Comatch (dec, bs) ->
                  (* Codata producer: build it with LetComatch, then End *)
                  let inner_v = Ident.fresh () in
                  Target.LetComatch (dec, transform_branches bs h', inner_v, 
                    Target.End)
              | CTm.Ctor (dec, c, args) ->
                  bind_terms args h' (fun arg_vars ->
                    let inner_v = Ident.fresh () in
                    Target.LetCtor (dec, c, arg_vars, inner_v, Target.End))
              | CTm.Match (dec, bs) ->
                  let inner_v = Ident.fresh () in
                  Target.LetMatch (dec, transform_branches bs h', inner_v, Target.End)
              | CTm.Var x ->
                  (* Variable: eta-expand based on type *)
                  (match get_instantiated_dec_from_type ty with
                  | Some dec when dec.polarity = CB.Neg ->
                      let inner_v = Ident.fresh () in
                      Target.LetComatch (dec,
                        List.map (fun (xtor: CTy.xtor) ->
                          let params = List.map (fun _ -> Ident.fresh ()) xtor.argument_types in
                          (xtor.name, [], params, Target.CutDtor (dec, xtor.name, Sub.apply h' x, params))
                        ) dec.xtors,
                        inner_v, Target.End)
                  | Some dec ->
                      let inner_v = Ident.fresh () in
                      Target.LetMatch (dec,
                        List.map (fun (xtor: CTy.xtor) ->
                          let params = List.map (fun _ -> Ident.fresh ()) xtor.argument_types in
                          (xtor.name, [], params, Target.CutCtor (dec, xtor.name, params, Sub.apply h' x))
                        ) dec.xtors,
                        inner_v, Target.End)
                  | None ->
                      Target.End)
              | _ ->
                  (* Generic case: just End *)
                  Target.End)
          | _ ->
              (* Fallback *)
              transform_command cmd h'
        in
        Target.LetNewForall (av', k_ty, body_ty,
          body_cmd,
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
    
    Target holds CTy.dec (Core instantiated declarations).
    Collapse applies collapse_dec to convert CTy.dec → FTy.dec with chirality flipping.
  *)

  (** Collapse a Target branch to a Focused branch *)
  let rec collapse_branch (parity: bool) ((xtor, ty_vars, tm_vars, body): Target.branch)
      : FTm.branch =
    (xtor, ty_vars, tm_vars, collapse_command parity body)

  (** Main collapse transformation.
      parity: true if we're inside an odd number of negative type bindings *)
  and collapse_command (parity: bool) : Target.command -> FTm.command = function
    (* LetCtor and LetDtor both become Let - apply collapse_dec to the Core dec *)
    | Target.LetCtor (dec, c, args, x, cont) ->
        FTm.Let (x, collapse_dec dec, c, args, collapse_command parity cont)
    | Target.LetDtor (dec, c, args, a, cont) ->
        FTm.Let (a, collapse_dec dec, c, args, collapse_command parity cont)

    (* LetMatch and LetComatch both become New *)
    | Target.LetMatch (dec, branches, x, cont) ->
        FTm.New (x, collapse_dec dec, List.map (collapse_branch parity) branches, 
          collapse_command parity cont)
    | Target.LetComatch (dec, branches, a, cont) ->
        FTm.New (a, collapse_dec dec, List.map (collapse_branch parity) branches, 
          collapse_command parity cont)

    (* CutCtor and CutDtor both become Invoke *)
    | Target.CutCtor (dec, c, args, a) ->
        FTm.Invoke (a, collapse_dec dec, c, args)
    | Target.CutDtor (dec, c, x, args) ->
        FTm.Invoke (x, collapse_dec dec, c, args)

    (* CutMatch and CutComatch both become Switch *)
    | Target.CutMatch (dec, x, branches) ->
        FTm.Switch (x, collapse_dec dec, List.map (collapse_branch parity) branches)
    | Target.CutComatch (dec, branches, a) ->
        FTm.Switch (a, collapse_dec dec, List.map (collapse_branch parity) branches)

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
    | Target.CutTyped (ty, x, k) ->
        FTm.Axiom (focus_type ty, x, k)
    | Target.LetIntCns (k, v, branch_body, cont) ->
        (* NewInt(k, v, branch_body, cont) binds k : Cns Int, v is received Int in branch *)
        FTm.NewInt (k, v, collapse_command parity branch_body, collapse_command parity cont)
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
