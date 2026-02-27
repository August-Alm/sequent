(**
  module: Core.Mono_types
  description: Types and utilities for the monomorphization transformation.
  
  This module provides the shared type definitions, error types, and utility
  functions used throughout the monomorphization process.
*)

open Common.Identifiers
open Common.Types
open Types.CoreTypes

module T = Terms
(* Counter for generating fresh inline For-codata names *)
let inline_for_counter = ref 0
let fresh_inline_for_name () =
  let n = !inline_for_counter in
  inline_for_counter := n + 1;
  Path.of_string ("inline.For" ^ string_of_int n)
(* ========================================================================= *)
(* Types for monomorphization                                                *)
(* ========================================================================= *)

(** A specific instantiation of type parameters *)
type instantiation = Mono_spec.ground_arg list

(** Information about a higher-rank parameter's instantiation uses *)
type higher_rank_info =
  { param_var: Ident.t                  (* The parameter variable name, e.g., f *)
  ; param_type: chiral_typ              (* The full parameter type *)
  ; forall_var: Ident.t                 (* The forall-bound type var, e.g., c *)
  ; instantiation_types: typ list       (* Types used with InstantiateDtor, e.g., [a; b] *)
  }

(** Information about a polymorphic definition's monomorphization *)
type mono_info = 
  { original_path: Path.t
  ; type_params: (Ident.t * typ) list   (* Original type parameters *)
  ; term_params: (Ident.t * chiral_typ) list  (* Original term parameters *)
  ; instantiations: instantiation list  (* All discovered instantiations *)
  ; generated_codata: dec               (* The generated For_X codata type *)
  ; mono_path: Path.t                   (* Path of monomorphized definition *)
  ; higher_rank_params: higher_rank_info list  (* Higher-rank param info *)
  }

(** Result of monomorphization *)
type mono_result =
  { main: Terms.definition
  ; definitions: Terms.definition list
  ; new_declarations: dec list
  ; mono_infos: mono_info Path.tbl      (* keyed by original definition path *)
  }

(* ========================================================================= *)
(* Error Types                                                               *)
(* ========================================================================= *)

(** Errors that can occur during monomorphization *)
type mono_error =
    GrowingCycle of (Path.t * int) list
  | NoMatchingInstantiation of
      { def_path: Path.t; instantiation: Mono_spec.ground_arg list }

type 'a mono_check = ('a, mono_error) result

let ( let* ) = Result.bind

(* ========================================================================= *)
(* Instantiation Utilities                                                   *)
(* ========================================================================= *)

(** Convert ground_arg to a Core typ *)
let rec ground_arg_to_typ (arg: Mono_spec.ground_arg): typ =
  match arg with
    Mono_spec.GroundExt Int -> Ext Int
  | Mono_spec.GroundSgn (name, args) ->
      Sgn (name, List.map ground_arg_to_typ args)

(** Generate destructor name for an instantiation *)
let dtor_name_for_inst (base_path: Path.t) (idx: int): Path.t =
  Path.access base_path ("inst_" ^ string_of_int idx)

(** Apply type substitution to a chiral type *)
let apply_subst_chiral (subst: typ Ident.tbl) (ct: chiral_typ): chiral_typ =
  chiral_map (apply_fresh_subst subst) ct

(* ========================================================================= *)
(* Higher-Rank Parameter Analysis                                            *)
(* ========================================================================= *)

(** Check if a type contains a Forall - indicates higher-rank *)
let rec contains_forall (t: typ): bool =
  match t with
    Forall _ -> true
  | Sgn (_, args) -> List.exists contains_forall args
  | Arrow (t1, t2) -> contains_forall t1 || contains_forall t2
  | TVar _ | TMeta _ | Ext _ | Base _ | PromotedCtor _ -> false

(** Extract the forall-bound variable from a higher-rank type.
    For raise(∀c:k. body), returns Some c *)
let extract_forall_var (t: typ): Ident.t option =
  match t with
    Sgn (_, [Forall (v, _, _)]) -> Some v  (* raise(∀v. body) *)
  | Forall (v, _, _) -> Some v
  | _ -> None

(** Collect all InstantiateDtor types used in a term/command.
    Returns list of types that are used with InstantiateDtor. *)
let rec collect_instantiations_term (tm: T.term): typ list =
  match tm with
    T.Var _ | T.Lit _ -> []
  | T.Ctor (_, _, args) -> List.concat_map collect_instantiations_term args
  | T.Dtor (_, _, _, args) -> List.concat_map collect_instantiations_term args
  | T.Match (_, branches) | T.Comatch (_, branches) ->
      List.concat_map (fun (_, _, _, cmd) -> collect_instantiations_cmd cmd) branches
  | T.MuPrd (_, _, cmd) | T.MuCns (_, _, cmd) -> collect_instantiations_cmd cmd
  | T.NewForall (_, _, _, _, cmd) -> collect_instantiations_cmd cmd
  | T.InstantiateDtor ty -> [ty]

and collect_instantiations_cmd (cmd: T.command): typ list =
  match cmd with
    T.Cut (_, p, c) -> 
      collect_instantiations_term p @ collect_instantiations_term c
  | T.Call (_, _, args) -> List.concat_map collect_instantiations_term args
  | T.Add (t1, t2, t3) | T.Sub (t1, t2, t3) ->
      List.concat_map collect_instantiations_term [t1; t2; t3]
  | T.Ifz (c, then_cmd, else_cmd) ->
      collect_instantiations_term c @ 
      collect_instantiations_cmd then_cmd @ 
      collect_instantiations_cmd else_cmd
  | T.Ret (_, tm) -> collect_instantiations_term tm
  | T.End -> []

(** Analyze a definition to find higher-rank parameters and their instantiation uses.
    Returns list of higher_rank_info for each higher-rank parameter. *)
let analyze_higher_rank_params (def: T.definition): higher_rank_info list =
  (* Find parameters with forall types *)
  let hr_params = List.filter_map (fun (var, ct) ->
    let ty = strip_chirality ct in
    if contains_forall ty then
      match extract_forall_var ty with
        Some forall_var -> Some (var, ct, forall_var) | None -> None
    else None
  ) def.term_params in
  
  if hr_params = [] then [] else
  
  (* Collect all InstantiateDtor types in the body *)
  let instantiation_types = collect_instantiations_cmd def.body in
  
  (* For each higher-rank param, record the instantiation types *)
  (* Note: This is simplified - we assume all instantiations apply to any HR param.
     A more precise analysis would track which param each instantiation belongs to. *)
  List.map (fun (var, ct, forall_var) ->
    { param_var = var
    ; param_type = ct
    ; forall_var
    ; instantiation_types
    }
  ) hr_params

(* ========================================================================= *)
(* Codata Generation                                                         *)
(* ========================================================================= *)

(** Generate the codata declaration for a polymorphic definition.
    
    For a definition like:
      def foo{a, b}(x: T1[a], y: T2[b], k: R[a,b]) = body
    
    With instantiations [(int, bool), (string, char)], generates:
    
    codata foo.For where
      inst_0(x: T1[int], y: T2[bool], k: R[int,bool]) : foo.For
      inst_1(x: T1[string], y: T2[char], k: R[string,char]) : foo.For
    
    Note: The destructor arguments are the specialized term parameters,
    preserving their chirality (Prd/Cns).
    
    The types_ctx is used to identify which type params have inhabitable kinds.
    Only inhabitable-kind type params are monomorphized; data-kind params
    (like `k: nat`) pass through unchanged.
*)
let generate_codata_for_def
    (types_ctx: Types.CoreTypes.context)
    (def: T.definition)
    (instantiations: instantiation list)
    : dec * Path.t =
  let codata_path = Path.access def.path "For" in
  let codata_typ = Sgn (codata_path, []) in
  
  (* Filter type params to only inhabitable-kind ones *)
  let inhabitable_type_params = List.filter (fun (_v, kind) ->
    Mono_spec.is_inhabitable_kind types_ctx kind
  ) def.type_params in
  
  (* Data-kind type params are kept as quantified params on the For codata *)
  let data_kind_params = List.filter (fun (_v, kind) ->
    not (Mono_spec.is_inhabitable_kind types_ctx kind)
  ) def.type_params in
  
  (* Generate one destructor per instantiation *)
  let xtors = List.mapi (fun idx inst ->
    (* Build substitution for this instantiation (only inhabitable-kind params) *)
    let subst = List.fold_left2 (fun acc (tvar, _kind) arg ->
      Ident.add tvar (ground_arg_to_typ arg) acc
    ) Ident.emptytbl inhabitable_type_params inst in
    
    (* Specialize the parameter types *)
    let specialized_params = List.map (fun (_var, ct) ->
      apply_subst_chiral subst ct
    ) def.term_params in
    
    let dtor_path = dtor_name_for_inst codata_path idx in
    { name = dtor_path
    ; quantified = data_kind_params  (* Data-kind params become quantified *)
    ; existentials = []
    ; argument_types = specialized_params
    ; main = codata_typ
    }
  ) instantiations in
  
  let dec = 
    { name = codata_path
    ; data_sort = Codata
    ; param_kinds = []
    ; type_args = []
    ; xtors
    } in
  (dec, codata_path)

(* ========================================================================= *)
(* Type Substitution in Terms and Commands                                   *)
(* ========================================================================= *)

(** Apply type substitution throughout a term *)
let rec subst_term (subst: typ Ident.tbl) (tm: T.term): T.term =
  match tm with
    T.Var _ | T.Lit _ -> tm
  | T.Ctor (dec, xtor, args) ->
      let dec' = subst_dec subst dec in
      T.Ctor (dec', xtor, List.map (subst_term subst) args)
  | T.Dtor (dec, xtor, exist_tys, args) ->
      let dec' = subst_dec subst dec in
      let exist_tys' = List.map (apply_fresh_subst subst) exist_tys in
      T.Dtor (dec', xtor, exist_tys', List.map (subst_term subst) args)
  | T.Match (dec, branches) ->
      let dec' = subst_dec subst dec in
      T.Match (dec', List.map (subst_branch subst) branches)
  | T.Comatch (dec, branches) ->
      let dec' = subst_dec subst dec in
      T.Comatch (dec', List.map (subst_branch subst) branches)
  | T.MuPrd (typ, var, cmd) ->
      T.MuPrd (apply_fresh_subst subst typ, var, subst_command subst cmd)
  | T.MuCns (typ, var, cmd) ->
      T.MuCns (apply_fresh_subst subst typ, var, subst_command subst cmd)
  | T.NewForall (tvar, kind, body_typ, cont, cmd) ->
      (* Remove tvar from substitution to avoid capture *)
      let subst' = Ident.filter (fun k _ -> not (Ident.equal k tvar)) subst in
      T.NewForall (tvar, apply_fresh_subst subst' kind, 
                   apply_fresh_subst subst' body_typ, cont,
                   subst_command subst' cmd)
  | T.InstantiateDtor typ ->
      T.InstantiateDtor (apply_fresh_subst subst typ)

and subst_branch (subst: typ Ident.tbl) ((xtor, tvars, tmvars, cmd): T.branch): T.branch =
  (* Remove bound type vars from substitution *)
  let subst' = List.fold_left (fun s tv ->
    Ident.filter (fun k _ -> not (Ident.equal k tv)) s
  ) subst tvars in
  (xtor, tvars, tmvars, subst_command subst' cmd)

and subst_command (sbs: typ Ident.tbl) (cmd: T.command): T.command =
  match cmd with
    T.Cut (typ, p, c) ->
      T.Cut (apply_fresh_subst sbs typ, subst_term sbs p, subst_term sbs c)
  | T.Call (path, typs, args) ->
      T.Call (path, List.map (apply_fresh_subst sbs) typs, List.map (subst_term sbs) args)
  | T.Add (t1, t2, t3) ->
      T.Add (subst_term sbs t1, subst_term sbs t2, subst_term sbs t3)
  | T.Sub (t1, t2, t3) ->
      T.Sub (subst_term sbs t1, subst_term sbs t2, subst_term sbs t3)
  | T.Ifz (cond, then_cmd, else_cmd) ->
      T.Ifz (subst_term sbs cond, subst_command sbs then_cmd, subst_command sbs else_cmd)
  | T.Ret (typ, tm) ->
      T.Ret (apply_fresh_subst sbs typ, subst_term sbs tm)
  | T.End -> T.End

and subst_dec (sbs: typ Ident.tbl) (dec: dec): dec =
  { dec with
    param_kinds = List.map (apply_fresh_subst sbs) dec.param_kinds
  ; type_args = List.map (apply_fresh_subst sbs) dec.type_args
  ; xtors = List.map (fun x -> 
      { x with 
        argument_types = List.map (apply_subst_chiral sbs) x.argument_types
      ; main = apply_fresh_subst sbs x.main
      }) dec.xtors
  }

(* ========================================================================= *)
(* Result Utilities                                                          *)
(* ========================================================================= *)

(** Traverse a list of results, collecting all successes or returning first error *)
let traverse_result (results: ('a, 'e) result list): ('a list, 'e) result =
  List.fold_right (fun r acc ->
    match r, acc with
      Ok a, Ok rest -> Ok (a :: rest)
    | Error e, _ | _, Error e -> Error e
  ) results (Ok [])

(** Convert a Core type to a ground argument for instantiation matching.
    This should never fail on well-typed terms - errors indicate earlier bugs. *)
let rec typ_to_ground_arg (t: typ): Mono_spec.ground_arg =
  match t with
    Ext Int -> Mono_spec.GroundExt Int
  | Sgn (name, args) -> Mono_spec.GroundSgn (name, List.map typ_to_ground_arg args)
  | PromotedCtor (data_name, ctor_name, args) ->
      (* Promoted constructors - preserve for type identity *)
      let promoted_path = Path.of_string ("'" ^ Path.name data_name ^ "." ^ Path.name ctor_name) in
      Mono_spec.GroundSgn (promoted_path, List.map typ_to_ground_arg args)
  | Base pol ->
      (* Base polarities *)
      let name = match pol with Types.CoreBase.Pos -> "+" | Types.CoreBase.Neg -> "-" in
      Mono_spec.GroundSgn (Path.of_string name, [])
  | TVar v -> failwith ("unexpected type variable in instantiation: " ^ Ident.name v)
  | TMeta v -> failwith ("unexpected meta variable in instantiation: " ^ Ident.name v)
  | Arrow _ -> failwith "unexpected arrow kind in instantiation"
  | Forall _ -> failwith "unexpected forall in instantiation"
