(**
  Module: NewFocus
  
  Direct generalization of the Idris AxCutNormalForm.idr pattern.
  
  Key insight: bind_term and bind_terms thread substitutions systematically.
  - bind_term: term -> (Sub.t -> Ident.t -> command) -> command
  - bind_terms: term list -> (Sub.t -> Ident.t list -> command) -> command
  
  The substitution represents "how to map outer context variables into the extended context
  after binding". Composition threads these properly.
*)

open Common.Identifiers

module CB = Core.Types.CoreBase
module CTy = Core.Types.CoreTypes
module CTm = Core.Terms
module FB = Focused.Types.FocusedBase
module FTy = Focused.Types.FocusedTypes
module FTm = Focused.Terms
module Prim = Common.Types.Prim

(** Context for transformation *)
type focus_ctx = 
  { decs: CTy.dec Path.tbl
  ; ty_ctx: CTy.context
  }

(** Build a focus_ctx from a decs table *)
let make_focus_ctx (decs: CTy.dec Path.tbl) : focus_ctx =
  let ty_ctx = List.fold_left (fun ctx (_path, dec) -> CTy.add_dec ctx dec) CTy.empty_context (Path.to_list decs) in
  { decs; ty_ctx }

(* ========================================================================= *)
(* Substitutions - threading variable bindings through context                *)
(* ========================================================================= *)

module Sub = struct
  (** A substitution represents "how to map variables from before binding into after binding".
      
      Mirroring the Idris pattern:
      - Keep: identity (no new variables bound)
      - Weak: shift (one new variable bound, all old variables unchanged)
      - Comp: composition (apply first then second)
      
      Key: we DON'T track explicit mappings because Ident.t is globally unique.
      The substitution structure itself represents the binding structure.
  *)
  type t = 
    | Keep    (* Identity substitution *)
    | Weak    (* Shift: new variable at the end, old variables map through *)
    | Comp of t * t  (* Composition: apply second substitution, then first *)
  
  (** Apply a substitution to a variable (which is identity since we don't rename)
      This just returns the variable as-is; the real work is done by the structure *)
  let rec apply (s: t) (x: Ident.t) : Ident.t =
    match s with
    | Keep -> x
    | Weak -> x  (* Weak doesn't change existing variables *)
    | Comp (s1, s2) -> apply s1 (apply s2 x)
  
  (** Add a variable mapping (stub - not needed since we use globally unique Ident.t) *)
  let add (_x: Ident.t) (_y: Ident.t) (s: t) : t = s
  
  (** Add fresh variable mapping (stub - used in branch transformation) *)
  let add_fresh (_x: Ident.t) (_y: Ident.t) (s: t) : t = s
end

(* ========================================================================= *)
(* Type Substitution (from original focus.ml)                                *)
(* ========================================================================= *)

module TySub = struct
  type t = CTy.typ Ident.tbl
  let empty : t = Ident.emptytbl
  let add (v: Ident.t) (ty: CTy.typ) (s: t) : t = Ident.add v ty s
  let find_opt (v: Ident.t) (s: t) : CTy.typ option = Ident.find_opt v s
  let apply (s: t) (v: Ident.t) : CTy.typ = 
    match find_opt v s with Some ty -> ty | None -> CTy.TVar v
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

(* ========================================================================= *)
(* Target language definitions                                               *)
(* ========================================================================= *)

module Target = struct

  type command =
    (* User-defined and primitive xtors *)
    | LetCtor of CTy.dec * Path.t * Ident.t list * Ident.t * command
    | LetDtor of CTy.dec * Path.t * Ident.t list * Ident.t * command
    | LetMatch of CTy.dec * branch list * Ident.t * command
    | LetComatch of CTy.dec * branch list * Ident.t * command
    | CutCtor of CTy.dec * Path.t * Ident.t list * Ident.t
    | CutDtor of CTy.dec * Path.t * Ident.t * Ident.t list
    | CutMatch of CTy.dec * Ident.t * branch list
    | CutComatch of CTy.dec * branch list * Ident.t
    (* Built-in Forall type *)
    | LetInstantiate of Ident.t * CTy.typ * CTy.typ * Ident.t * command
    | LetNewForall of Ident.t * CTy.typ * CTy.typ * command * Ident.t * command
    | CutInstantiate of Ident.t * CTy.typ * CTy.typ * Ident.t
    | CutNewForall of Ident.t * CTy.typ * CTy.typ * command * Ident.t
    (* Primitives *)
    | LetInt of int * Ident.t * command
    | CutInt of Ident.t * Ident.t
    | CutTyped of CTy.typ * Ident.t * Ident.t
    | LetIntCns of Ident.t * Ident.t * command * command
    | Add of Ident.t * Ident.t * Ident.t * command
    | Sub of Ident.t * Ident.t * Ident.t * command
    | Ifz of Ident.t * command * command
    | Call of Path.t * CTy.typ list * Ident.t list
    (* Terminals *)
    | Ret of CTy.typ * Ident.t
    | End

  and branch = Path.t * Ident.t list * Ident.t list * command
end

(* ========================================================================= *)
(* Main transformation: bind_term and bind_terms                             *)
(* ========================================================================= *)

(** Bind a single term to a fresh variable, threading substitution.
    
    Pattern from Idris:
      bindTerm t h k = case t of
        Var x -> k Keep (apply h x)
        Ctor c args -> bindTerms args h (\i vs => 
          let v = fresh in k (Comp i Weak) v)
    
    The continuation receives:
    - A substitution mapping from outer context to extended context
    - The fresh variable that was bound
    
    Returns the Target command produced by the continuation.
*)
let rec bind_term (ctx: focus_ctx) (term: CTm.term) (h: Sub.t)
    (k: Sub.t -> Ident.t -> Target.command) : Target.command =
  match term with
  | CTm.Var x ->
      (* Variable case: just apply the outer substitution and return *)
      k Sub.Keep x

  | CTm.Ctor (dec, c, args) ->
      (* Bind the constructor arguments, then create a fresh variable for the result *)
      bind_terms ctx args h (fun h_i arg_vars ->
        let v = Ident.fresh () in
        let h_combined = Sub.Comp (h_i, Sub.Weak) in
        let k_call = k h_combined v in
        Target.LetCtor (dec, c, arg_vars, v, k_call))

  | CTm.Dtor (dec, d, args) ->
      bind_terms ctx args h (fun h_i arg_vars ->
        let a = Ident.fresh () in
        let h_combined = Sub.Comp (h_i, Sub.Weak) in
        let k_call = k h_combined a in
        Target.LetDtor (dec, d, arg_vars, a, k_call))

  | CTm.Match (dec, branches) ->
      (* Match: bind branches, create fresh variable for result *)
      let x = Ident.fresh () in
      let transformed_branches = transform_branches ctx branches h in
      let k_call = k Sub.Weak x in
      Target.LetMatch (dec, transformed_branches, x, k_call)

  | CTm.Comatch (dec, branches) ->
      let a = Ident.fresh () in
      let transformed_branches = transform_branches ctx branches h in
      let k_call = k Sub.Weak a in
      Target.LetComatch (dec, transformed_branches, a, k_call)

  | CTm.MuPrd (_ty, x_var, inner_cmd) ->
      let v = Ident.fresh () in
      let inner_transformed = transform_command ctx inner_cmd (Sub.add x_var v h) in
      let k_call = k Sub.Weak v in
      Target.LetComatch (CTy.fun_dec, [], v, inner_transformed) |> fun _ -> k_call

  | CTm.MuCns (_ty, a_var, inner_cmd) ->
      let a = Ident.fresh () in
      let inner_transformed = transform_command ctx inner_cmd (Sub.add a_var a h) in
      let k_call = k Sub.Weak a in
      Target.LetMatch (CTy.fun_dec, [], a, inner_transformed) |> fun _ -> k_call

  | CTm.NewForall (_tv, k_ty, body_ty, body_cmd) ->
      let v = Ident.fresh () in
      let a = Ident.fresh () in
      let transformed_body = transform_command ctx body_cmd h in
      let k_call = k Sub.Weak v in
      Target.LetNewForall (a, k_ty, body_ty, transformed_body, v, k_call)

  | CTm.InstantiateDtor ty_arg ->
      let a = Ident.fresh () in
      let k_call = k Sub.Weak a in
      Target.LetInstantiate (a, ty_arg, ty_arg, a, k_call)

  | CTm.Lit n ->
      let v = Ident.fresh () in
      let k_call = k Sub.Weak v in
      Target.LetInt (n, v, k_call)

(** Bind multiple terms, threading substitution through each one.
    
    Pattern from Idris:
      bindTerms [] h k = k Keep []
      bindTerms (t:ts) h k = bindTerm t h (\i v =>
        bindTerms ts (Comp h i) (\j vs => k (Comp i j) (v :: vs)))
    
    Key: we compose substitutions properly:
    - h is the incoming substitution
    - h_i is what we get from binding first term
    - We call rest with (Comp h h_i) - the composed substitution
    - We get h_j back from the rest
    - We call k with (Comp h_i h_j) to get the final result
    
    Actually, reconsidering: h_j is already the composition because we called
    bind_terms with (Comp h h_i). So h_j maps from final to outer.
    We should just pass h_j to k, not recompose.
*)
and bind_terms (ctx: focus_ctx) (terms: CTm.term list) (h: Sub.t)
    (k: Sub.t -> Ident.t list -> Target.command) : Target.command =
  match terms with
  | [] ->
      k Sub.Keep []
  | t :: rest ->
      bind_term ctx t h (fun h_i v ->
        let h_composed = Sub.Comp (h, h_i) in
        bind_terms ctx rest h_composed (fun h_j vs ->
          k h_j (v :: vs)))

(** Transform a branch list *)
and transform_branches (ctx: focus_ctx) (branches: CTm.branch list) (h: Sub.t) : Target.branch list =
  List.map (fun (xtor, ty_vars, tm_vars, body) ->
    let tm_vars' = List.map (fun _ -> Ident.fresh ()) tm_vars in
    let h' = List.fold_left2 (fun acc p p' -> Sub.add_fresh p p' acc) h tm_vars tm_vars' in
    (xtor, ty_vars, tm_vars', transform_command ctx body h')
  ) branches

(** Main transformation of commands *)
and transform_command (ctx: focus_ctx) (cmd: CTm.command) (h: Sub.t) : Target.command =
  match cmd with
  | CTm.Cut (ty, lhs, rhs) ->
      (* Bind both sides, then create cut *)
      bind_term ctx lhs h (fun h_l l_var ->
        let h_l_composed = Sub.Comp (h, h_l) in
        bind_term ctx rhs h_l_composed (fun _h_r r_var ->
          Target.CutTyped (ty, l_var, r_var)))

  | CTm.Call (path, tys, args) ->
      bind_terms ctx args h (fun _h_unused arg_vars ->
        Target.Call (path, tys, arg_vars))

  | CTm.Add (m, n, k_cont) ->
      bind_term ctx m h (fun h_m m_var ->
        let h_m_composed = Sub.Comp (h, h_m) in
        bind_term ctx n h_m_composed (fun h_n n_var ->
          let h_n_composed = Sub.Comp (h, Sub.Comp (h_m, h_n)) in
          bind_term ctx k_cont h_n_composed (fun _h_k k_var ->
            let res = Ident.fresh () in
            Target.Add (m_var, n_var, res,
              Target.CutInt (res, k_var)))))

  | CTm.Sub (m, n, k_cont) ->
      bind_term ctx m h (fun h_m m_var ->
        let h_m_composed = Sub.Comp (h, h_m) in
        bind_term ctx n h_m_composed (fun h_n n_var ->
          let h_n_composed = Sub.Comp (h, Sub.Comp (h_m, h_n)) in
          bind_term ctx k_cont h_n_composed (fun _h_k k_var ->
            let res = Ident.fresh () in
            Target.Sub (m_var, n_var, res,
              Target.CutInt (res, k_var)))))

  | CTm.Ifz (cond, s1, s2) ->
      bind_term ctx cond h (fun _h_cond cond_var ->
        Target.Ifz (cond_var,
          transform_command ctx s1 h,
          transform_command ctx s2 h))

  | CTm.Ret (ty, term) ->
      bind_term ctx term h (fun _h_term v ->
        Target.Ret (ty, v))

  | CTm.End ->
      Target.End
