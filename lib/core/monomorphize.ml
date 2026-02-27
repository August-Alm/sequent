(**
  module: Core.Monomorphize
  description: Monomorphization transformation for the Core language.
  
  This module transforms polymorphic definitions into monomorphic ones by:
  1. Analyzing flow constraints to find all type instantiations
  2. For each polymorphic definition, generating a codata type where each
     destructor carries the specialized term parameters
  3. Transforming the polymorphic definition into a monomorphic one that
     takes a single consumer of the codata type
  4. Transforming call sites to use the appropriate destructor
  
  Example transformation:
  
    def id{a}(x: Prd a, k: Cns a) = ⟨x | k⟩
    
    with instantiations [int, bool] becomes:
    
    codata id.For where
      inst_0(x: Prd int, k: Cns int) : id.For
      inst_1(x: Prd bool, k: Cns bool) : id.For
    
    def id.mono(u: Cns id.For) =
      ⟨Comatch(id.For, [
          inst_0(x, k) => ⟨x | k⟩
          inst_1(x, k) => ⟨x | k⟩
        ]) | u⟩
    
    Call site id{int}(42, k) becomes:
      Call(id.mono, [], [Dtor(id.For, inst_0, [42, k])])
  
  Higher-rank polymorphism:
  
    When a definition has a higher-rank parameter like f: {c} c -> c,
    and that parameter's type variable c is instantiated multiple times
    (e.g., f{a}(x) and f{b}(y)), we create a dictionary codata type.
    
    For map_mk_tuple{a}{b}(f: {c} c->c) with f{a} and f{b} usages,
    monomorphized at [int, enum]:
    
    codata id.For where
      inst_0(k, x) : id.For    -- for int
      inst_1(k, x) : id.For    -- for enum
    
    map_mk_tuple.mono takes f: prd id.For
*)

open Common.Identifiers
open Common.Types
open Types.CoreBase
open Types.CoreTypes

(* Open Terms for direct access to term/command constructors *)
module T = Terms

(* ========================================================================= *)
(* Types for Monomorphization                                                *)
(* ========================================================================= *)

(** A specific instantiation of type parameters *)
type instantiation = Specialization.ground_arg list

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
  | GrowingCycle of (Path.t * int) list
  | NoMatchingInstantiation of
      { def_path: Path.t; instantiation: Specialization.ground_arg list }

type 'a mono_check = ('a, mono_error) result

let ( let* ) = Result.bind

(* ========================================================================= *)
(* Instantiation Utilities                                                   *)
(* ========================================================================= *)

(** Convert ground_arg to a Core typ *)
let rec ground_arg_to_typ (arg: Specialization.ground_arg): typ =
  match arg with
    Specialization.GroundExt Int -> Ext Int
  | Specialization.GroundSgn (name, args) ->
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
  | Forall _ -> true
  | Sgn (_, args) -> List.exists contains_forall args
  | Arrow (t1, t2) -> contains_forall t1 || contains_forall t2
  | TVar _ | TMeta _ | Ext _ | Base _ | PromotedCtor _ -> false

(** Extract the forall-bound variable from a higher-rank type.
    For raise(∀c:k. body), returns Some c *)
let extract_forall_var (t: typ): Ident.t option =
  match t with
  | Sgn (_, [Forall (v, _, _)]) -> Some v  (* raise(∀v. body) *)
  | Forall (v, _, _) -> Some v
  | _ -> None

(** Collect all InstantiateDtor types used in a term/command.
    Returns list of types that are used with InstantiateDtor. *)
let rec collect_instantiations_term (tm: T.term): typ list =
  match tm with
  | T.Var _ | T.Lit _ -> []
  | T.Ctor (_, _, args) -> List.concat_map collect_instantiations_term args
  | T.Dtor (_, _, _, args) -> List.concat_map collect_instantiations_term args
  | T.Match (_, branches) | T.Comatch (_, branches) ->
      List.concat_map (fun (_, _, _, cmd) -> collect_instantiations_cmd cmd) branches
  | T.MuPrd (_, _, cmd) | T.MuCns (_, _, cmd) -> collect_instantiations_cmd cmd
  | T.NewForall (_, _, _, _, cmd) -> collect_instantiations_cmd cmd
  | T.InstantiateDtor ty -> [ty]

and collect_instantiations_cmd (cmd: T.command): typ list =
  match cmd with
  | T.Cut (_, p, c) -> 
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
      | Some forall_var -> Some (var, ct, forall_var)
      | None -> None
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
    and the main type is the codata type itself.
*)
let generate_codata_for_def 
    (def: T.definition)
    (instantiations: instantiation list)
    : dec * Path.t =
  
  let codata_name = Path.access def.path "For" in
  let codata_typ = Sgn (codata_name, []) in
  
  let xtors = List.mapi (fun idx inst ->
    (* Create substitution: type_param_i -> inst_arg_i *)
    let subst = List.fold_left2 (fun acc (tvar, _kind) arg ->
      Ident.add tvar (ground_arg_to_typ arg) acc
    ) Ident.emptytbl def.type_params inst in
    
    (* Specialize the term parameter types *)
    let specialized_params = List.map (fun (_var, ct) ->
      apply_subst_chiral subst ct
    ) def.term_params in
    
    { name = dtor_name_for_inst codata_name idx
    ; quantified = []
    ; existentials = []
    ; argument_types = specialized_params  (* Destructor carries the args! *)
    ; main = codata_typ                    (* Main type is the codata itself *)
    }
  ) instantiations in
  
  let codata_dec = 
    { name = codata_name
    ; data_sort = Codata
    ; param_kinds = []
    ; type_args = []
    ; xtors
    } in
  
  (codata_dec, codata_name)

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
(* Call Site Transformation                                                  *)
(* ========================================================================= *)

(** Traverse a list of results, collecting all successes or returning first error *)
let traverse_result (results: ('a, 'e) result list): ('a list, 'e) result =
  List.fold_right (fun r acc ->
    match r, acc with
      Ok a, Ok rest -> Ok (a :: rest)
    | Error e, _ -> Error e
    | _, Error e -> Error e
  ) results (Ok [])

(** Convert a Core type to a ground argument for instantiation matching.
    This should never fail on well-typed terms - errors indicate earlier bugs. *)
let rec typ_to_ground_arg (t: typ): Specialization.ground_arg =
  match t with
    Ext Int -> Specialization.GroundExt Int
  | Sgn (name, args) -> Specialization.GroundSgn (name, List.map typ_to_ground_arg args)
  | TVar v -> failwith ("unexpected type variable in instantiation: " ^ Ident.name v)
  | TMeta v -> failwith ("unexpected meta variable in instantiation: " ^ Ident.name v)
  | Base _ -> failwith "unexpected base kind in instantiation"
  | Arrow _ -> failwith "unexpected arrow kind in instantiation"
  | Forall _ -> failwith "unexpected forall in instantiation"
  | PromotedCtor _ -> failwith "unexpected promoted ctor in instantiation"

(** Context for transformation *)
type transform_ctx =
  { mono_infos: mono_info Path.tbl
  ; dtor_flows: Specialization.ground_arg list Path.tbl  (* dtor_path -> instantiations *)
  ; forall_flows: Specialization.ground_arg list Path.tbl  (* forall_path -> instantiation types *)
  ; forall_bound: Ident.t list  (* Type vars bound by enclosing NewForall *)
  ; inline_forall_decs: dec list ref  (* Accumulator for inline NewForall codata declarations *)
  ; forall_to_for: (dec * instantiation list) Ident.tbl  (* Maps forall-typed var to (For-type codata, instantiations) *)
  }

(** Check if a type uses any of the given type variables *)
let rec typ_uses_vars (vars: Ident.t list) (ty: typ): bool =
  match ty with
  | TVar v -> List.mem v vars
  | TMeta _ | Base _ | Ext _ -> false
  | Sgn (_, args) -> List.exists (typ_uses_vars vars) args
  | Forall (_, k, b) -> typ_uses_vars vars k || typ_uses_vars vars b
  | Arrow (a, b) -> typ_uses_vars vars a || typ_uses_vars vars b
  | PromotedCtor (_, _, args) -> List.exists (typ_uses_vars vars) args

(** Find calls to monomorphized functions in a command.
    Returns list of (def_path, type_args) for each call found. *)
let rec find_mono_calls_in_cmd (mono_infos: mono_info Path.tbl) (cmd: T.command): (Path.t * typ list) list =
  match cmd with
  | T.Cut (_, producer, consumer) ->
      find_mono_calls_in_term mono_infos producer @ find_mono_calls_in_term mono_infos consumer
  | T.Call (def_path, type_args, term_args) ->
      let from_args = List.concat_map (find_mono_calls_in_term mono_infos) term_args in
      if Path.find_opt def_path mono_infos <> None then
        (def_path, type_args) :: from_args
      else
        from_args
  | T.Add (t1, t2, t3) | T.Sub (t1, t2, t3) ->
      find_mono_calls_in_term mono_infos t1 @ 
      find_mono_calls_in_term mono_infos t2 @ 
      find_mono_calls_in_term mono_infos t3
  | T.Ifz (cond, then_cmd, else_cmd) ->
      find_mono_calls_in_term mono_infos cond @ 
      find_mono_calls_in_cmd mono_infos then_cmd @ 
      find_mono_calls_in_cmd mono_infos else_cmd
  | T.Ret (_, tm) -> find_mono_calls_in_term mono_infos tm
  | T.End -> []

and find_mono_calls_in_term (mono_infos: mono_info Path.tbl) (tm: T.term): (Path.t * typ list) list =
  match tm with
  | T.Var _ | T.Lit _ | T.InstantiateDtor _ -> []
  | T.Ctor (_, _, args) | T.Dtor (_, _, _, args) ->
      List.concat_map (find_mono_calls_in_term mono_infos) args
  | T.Match (_, branches) | T.Comatch (_, branches) ->
      List.concat_map (fun (_, _, _, cmd) -> find_mono_calls_in_cmd mono_infos cmd) branches
  | T.MuPrd (_, _, cmd) | T.MuCns (_, _, cmd) ->
      find_mono_calls_in_cmd mono_infos cmd
  | T.NewForall (_, _, _, _, cmd) ->
      find_mono_calls_in_cmd mono_infos cmd

(** Try to find an InstantiateDtor type within a Match on raise.
    Pattern: Match(raise_dec, [raise.thunk(u) => Cut(Var u, InstantiateDtor(T))])
    Returns Some T if the pattern matches, None otherwise. *)
let find_instantiate_in_raise_match (consumer: T.term): (typ * Ident.t) option =
  match consumer with
  | T.Match (_dec, [(xtor, [], [u], cmd)]) ->
      (* Check if this is a match on raise.thunk *)
      if Path.equal xtor Prim.thunk_sym then
        (* Look for Cut(Var u, InstantiateDtor T) in the command *)
        (match cmd with
        | T.Cut (_, T.Var v, T.InstantiateDtor inst_typ) 
          when Ident.equal v u -> Some (inst_typ, u)
        | _ -> None)
      else None
  | _ -> None

(** Try to match the full higher-rank application pattern:
    MuPrd(result_k, T, 
      Cut(_, 
        MuPrd(fun_k, raise(fun(T,T)),
          Cut(_, Var f, match raise{forall} {...InstantiateDtor(T)...})),
        match raise{fun(T,T)} { raise.thunk(body) => Cut(body, fun.apply(result_k, arg)) }))
    
    Returns Some (f, inst_type, arg, result_k) if pattern matches *)
let match_higher_rank_application (cmd: T.command): (Ident.t * typ * T.term * Ident.t) option =
  match cmd with
  | T.Cut (_, 
      T.MuPrd (_, _fun_k,
        T.Cut (_, T.Var f, forall_match)),
      T.Match (_fun_dec, [(fun_xtor, [], [body], 
        T.Cut (_, T.Var body', T.Dtor (_apply_dec, apply_xtor, _, [T.Var result_k; arg])))]))
    when Path.equal fun_xtor Prim.thunk_sym &&
         Path.equal apply_xtor Prim.apply_sym &&
         Ident.equal body body' ->
      (* Found the pattern! Now extract the instantiation type from the forall_match.
         Note: fun.apply(result_k, arg) has result_k first, then arg *)
      (match find_instantiate_in_raise_match forall_match with
      | Some (inst_typ, _) -> Some (f, inst_typ, arg, result_k)
      | None -> None)
  | _ -> None

(** Check if a NewForall calls a specific function polymorphically.
    Returns the function path if the body calls a function with the forall-bound type. *)
let find_called_function_in_newforall (tvar: Ident.t) (cmd: T.command): Path.t option =
  (* Look for a Call to a function that uses tvar *)
  let rec find_call cmd =
    match cmd with
    | T.Call (path, type_args, _term_args) ->
        (* Check if one of the type args is our bound tvar *)
        let uses_tvar = List.exists (fun ty ->
          match ty with
          | TVar v -> Ident.name v = Ident.name tvar
          | _ -> false
        ) type_args in
        if uses_tvar then Some path else None
    | T.Cut (_, producer, consumer) ->
        (* Look in both sides *)
        (match find_call_term producer with
        | Some p -> Some p
        | None -> find_call_consumer consumer)
    | T.Add _ | T.Sub _ | T.Ifz _ | T.Ret _ | T.End -> None
  and find_call_term tm =
    match tm with
    | T.Comatch (_, branches) | T.Match (_, branches) ->
        List.find_map (fun (_, _, _, cmd) -> find_call cmd) branches
    | T.NewForall (_, _, _, _, cmd) -> find_call cmd
    | T.MuCns (_, _, cmd) | T.MuPrd (_, _, cmd) -> find_call cmd
    | T.Ctor (_, _, args) | T.Dtor (_, _, _, args) ->
        List.find_map find_call_term args
    | _ -> None
  and find_call_consumer cns =
    match cns with
    | T.Match (_, branches) | T.Comatch (_, branches) ->
        List.find_map (fun (_, _, _, cmd) -> find_call cmd) branches
    | T.MuCns (_, _, cmd) | T.MuPrd (_, _, cmd) -> find_call cmd
    | T.Dtor (_, _, _, args) ->
        List.find_map find_call_term args
    | _ -> None
  in
  find_call cmd

(** Transform a term, handling call sites to monomorphized definitions *)
let rec transform_term (ctx: transform_ctx) (tm: T.term): T.term mono_check =
  match tm with
    T.Var _ | T.Lit _ -> Ok tm
  
  (* Special case: raise.thunk{∀...}(NewForall(a, k, body_ty, cont, cmd))
     When the cmd calls a monomorphized function foo with type var a,
     transform to: comatch foo.For { ... } *)
  | T.Ctor (dec, xtor, [T.NewForall (tvar, _kind, _body_ty, _cont, cmd)])
      when Path.equal xtor Prim.thunk_sym ->
      (match find_called_function_in_newforall tvar cmd with
      | Some called_path ->
          (match Path.find_opt called_path ctx.mono_infos with
          | Some info ->
              let for_dec = info.generated_codata in
              
              (* Create branches for the For-codata based on instantiations *)
              let* new_branches = traverse_result (List.mapi (fun idx inst ->
                let inst_typ = ground_arg_to_typ (List.hd inst) in
                let dtor_path = dtor_name_for_inst for_dec.name idx in
                
                (* Get the term params from the for_dec's xtor *)
                let for_xtor = List.find (fun (x: xtor) -> Path.equal x.name dtor_path) for_dec.xtors in
                let param_vars = List.mapi (fun i _ct -> Ident.mk ("p" ^ string_of_int i)) for_xtor.argument_types in
                
                (* Build: call foo.mono(Dtor(for_dec, inst_i, param_vars)) *)
                let dtor = T.Dtor (for_dec, dtor_path, [], List.map (fun v -> T.Var v) param_vars) in
                let call_mono = T.Call (info.mono_path, [], [dtor]) in
                
                Ok (dtor_path, [], param_vars, call_mono)
              ) info.instantiations) in
              
              Ok (T.Comatch (for_dec, new_branches))
          | None ->
              (* Not monomorphized, transform the NewForall normally *)
              let* inner' = transform_term ctx (T.NewForall (tvar, _kind, _body_ty, _cont, cmd)) in
              Ok (T.Ctor (dec, xtor, [inner'])))
      | None ->
          (* Couldn't identify called function, transform normally *)
          let* inner' = transform_term ctx (T.NewForall (tvar, _kind, _body_ty, _cont, cmd)) in
          Ok (T.Ctor (dec, xtor, [inner'])))
  
  | T.Ctor (dec, xtor, args) ->
      let* args' = traverse_result (List.map (transform_term ctx) args) in
      Ok (T.Ctor (dec, xtor, args'))
  | T.Dtor (dec, xtor, exist_tys, args) ->
      let* args' = traverse_result (List.map (transform_term ctx) args) in
      Ok (T.Dtor (dec, xtor, exist_tys, args'))
  | T.Match (dec, branches) ->
      let* branches' = traverse_result (List.map (transform_branch ctx) branches) in
      Ok (T.Match (dec, branches'))
  | T.Comatch (dec, branches) ->
      (* For comatch, we need to substitute existential type variables in branches
         based on the solved flow constraints for each destructor *)
      let* branches' = traverse_result (List.map (transform_comatch_branch ctx dec) branches) in
      Ok (T.Comatch (dec, branches'))
  | T.MuPrd (typ, var, cmd) ->
      (match match_higher_rank_application cmd with
      | Some (f_var, inst_typ, arg, result_k) 
        when Ident.find_opt f_var ctx.forall_to_for <> None ->
          let (for_dec, instantiations) = Ident.find f_var ctx.forall_to_for in
          let inst_garg = typ_to_ground_arg inst_typ in
          let idx_opt = List.find_index (fun inst ->
            match inst with
            | [garg] -> garg = inst_garg
            | _ -> false
          ) instantiations in
          (match idx_opt with
          | Some idx ->
              let dtor_path = dtor_name_for_inst for_dec.name idx in
              let for_typ = Sgn (for_dec.name, []) in
              let* arg' = transform_term ctx arg in
              let dtor = T.Dtor (for_dec, dtor_path, [], [arg'; T.Var var]) in
              let cut = T.Cut (for_typ, T.Var f_var, dtor) in
              Ok (T.MuPrd (typ, var, cut))
          | None ->
              let* cmd' = transform_command ctx cmd in
              Ok (T.MuPrd (typ, var, cmd')))
      | _ ->
          let* cmd' = transform_command ctx cmd in
          Ok (T.MuPrd (typ, var, cmd')))
  | T.MuCns (typ, var, cmd) ->
      let* cmd' = transform_command ctx cmd in
      Ok (T.MuCns (typ, var, cmd'))
  | T.NewForall (tvar, _kind, _body_typ, cont, cmd) ->
      (* A NewForall creates a polymorphic value. After monomorphization, this must
         become a Comatch over a For-type. We find the monomorphized function that
         the body calls and use its For-type.
         
         NewForall(a, k, body_typ, cont, cmd_with_call_f{a}(...))
         becomes:
         Comatch(f.For, [ inst_0(cont) => cmd[a:=T0], inst_1(cont) => cmd[a:=T1], ... ])
      *)
      let forall_path = Path.of_ident tvar in
      let inst_types = match Path.find_opt forall_path ctx.forall_flows with
        | Some types -> types
        | None -> []
      in
      
      (* Find which monomorphized function is called in the body *)
      let mono_calls = find_mono_calls_in_cmd ctx.mono_infos cmd in
      
      (match mono_calls with
      | [] ->
          (* No calls to monomorphized functions - keep as-is or fail *)
          if inst_types = [] then begin
            let* cmd' = transform_command ctx cmd in
            Ok (T.NewForall (tvar, _kind, _body_typ, cont, cmd'))
          end else
            failwith (Printf.sprintf "NewForall %s has instantiation types but no mono calls" 
              (Ident.name tvar))
      
      | (called_path, _type_args) :: _ ->
          (* Found a call to a monomorphized function. Use its For-type. *)
          (match Path.find_opt called_path ctx.mono_infos with
          | None -> 
              failwith (Printf.sprintf "NewForall calls %s but it's not in mono_infos" 
                (Path.name called_path))
          | Some info ->
              (* Generate a Comatch over the called function's For-type.
                 Each branch corresponds to an instantiation of that function. *)
              let for_dec = info.generated_codata in
              
              (* Create branches: for each instantiation, substitute tvar and transform *)
              let* branches = traverse_result (List.mapi (fun idx inst ->
                let inst_typ = ground_arg_to_typ (List.hd inst) in (* First type arg *)
                let subst = Ident.add tvar inst_typ Ident.emptytbl in
                let cmd_subst = subst_command subst cmd in
                let* cmd' = transform_command ctx cmd_subst in
                
                (* The destructor name for this instantiation *)
                let dtor_name = dtor_name_for_inst for_dec.name idx in
                
                (* Branch: dtor_name(cont) => cmd' *)
                Ok (dtor_name, [], [cont], cmd')
              ) info.instantiations) in
              
              Ok (T.Comatch (for_dec, branches))))
              
  | T.InstantiateDtor typ ->
      (* InstantiateDtor(T) should become Dtor(For, inst_T, []) when we know the For-type.
         But we need context about which For-type to use. For now, keep as-is;
         the cut will handle it. *)
      Ok (T.InstantiateDtor typ)

(** Transform a regular branch (for Match) *)
and transform_branch
    (ctx: transform_ctx) ((xtor, tvars, tmvars, cmd): T.branch): T.branch mono_check =
  let* cmd' = transform_command ctx cmd in
  Ok (xtor, tvars, tmvars, cmd')

(** Transform a comatch branch, substituting existential type variables *)
and transform_comatch_branch
    (ctx: transform_ctx) (dec: dec) ((xtor, tvars, tmvars, cmd): T.branch): T.branch mono_check =
  (* Build the destructor path to look up flow instantiations *)
  let dtor_path = Path.access dec.name (Path.name xtor) in
  
  (* Look up what types should be substituted for this destructor's existentials *)
  let subst = match Path.find_opt dtor_path ctx.dtor_flows with
    | Some ground_args when List.length ground_args = List.length tvars ->
        (* Build substitution: tvars[i] -> ground_args[i] *)
        List.fold_left2 (fun s tv garg ->
          Ident.add tv (ground_arg_to_typ garg) s
        ) Ident.emptytbl tvars ground_args
    | _ ->
        (* No flow found, or mismatched arity - no substitution *)
        Ident.emptytbl
  in
  
  (* Apply substitution to the command - this propagates concrete types into the body *)
  let cmd_subst = subst_command subst cmd in
  let* cmd' = transform_command ctx cmd_subst in
  
  (* Keep the type vars to match the xtor's expected arity.
     The type vars are still "bound" but their uses in the body have been substituted. *)
  Ok (xtor, tvars, tmvars, cmd')

(** Transform a command, replacing calls to polymorphic definitions *)
and transform_command (ctx: transform_ctx) (cmd: T.command): T.command mono_check =
  match cmd with
    T.Cut (typ, producer, consumer) ->
      (* Special case: Cut with Var and InstantiateDtor - transform to Dtor if forall_to_for mapping exists *)
      (match producer, consumer with
      | T.Var v, T.InstantiateDtor inst_typ when Ident.find_opt v ctx.forall_to_for <> None ->
          let (for_dec, instantiations) = Ident.find v ctx.forall_to_for in
          (* Find the index of this instantiation type in the instantiations list *)
          let inst_garg = typ_to_ground_arg inst_typ in
          let idx_opt = List.find_index (fun inst ->
            (* Each instantiation is a list of ground_args (type args) - compare first one *)
            match inst with
            | [garg] -> garg = inst_garg
            | _ -> false
          ) instantiations in
          (match idx_opt with
          | Some idx ->
              let dtor_path = dtor_name_for_inst for_dec.name idx in
              let for_typ = Sgn (for_dec.name, []) in
              Ok (T.Cut (for_typ, T.Var v, T.Dtor (for_dec, dtor_path, [], [])))
          | None ->
              (* Index not found - fall back to regular transformation *)
              let* producer' = transform_term ctx producer in
              let* consumer' = transform_term ctx consumer in
              Ok (T.Cut (typ, producer', consumer')))
      
      (* Special case: Cut(Var f, Match(raise, [thunk(u) => Cut(u, InstantiateDtor T)])) 
         when f is a forall-typed parameter. Transform to Cut(f, Dtor(For, inst_T, [])). *)
      | T.Var v, _ when Ident.find_opt v ctx.forall_to_for <> None ->
          (match find_instantiate_in_raise_match consumer with
          | Some (inst_typ, _u) ->
              let (for_dec, instantiations) = Ident.find v ctx.forall_to_for in
              let inst_garg = typ_to_ground_arg inst_typ in
              let idx_opt = List.find_index (fun inst ->
                match inst with
                | [garg] -> garg = inst_garg
                | _ -> false
              ) instantiations in
              (match idx_opt with
              | Some idx ->
                  let dtor_path = dtor_name_for_inst for_dec.name idx in
                  let for_typ = Sgn (for_dec.name, []) in
                  Ok (T.Cut (for_typ, T.Var v, T.Dtor (for_dec, dtor_path, [], [])))
              | None ->
                  let* producer' = transform_term ctx producer in
                  let* consumer' = transform_term ctx consumer in
                  Ok (T.Cut (typ, producer', consumer')))
          | None ->
              let* producer' = transform_term ctx producer in
              let* consumer' = transform_term ctx consumer in
              Ok (T.Cut (typ, producer', consumer')))
      
      | _ ->
          let* producer' = transform_term ctx producer in
          let* consumer' = transform_term ctx consumer in
          Ok (T.Cut (typ, producer', consumer')))
  
  | T.Call (def_path, type_args, term_args) ->
      (* Check if the called definition was monomorphized *)
      (match Path.find_opt def_path ctx.mono_infos with
        None ->
          (* Not monomorphized, keep as-is but transform args *)
          let* term_args' = traverse_result (List.map (transform_term ctx) term_args) in
          Ok (T.Call (def_path, type_args, term_args'))
      
      | Some info ->
          (* Check if any type argument uses forall-bound type variables.
             If so, we can't transform this call yet - it will be handled
             when the enclosing NewForall is instantiated with concrete types. *)
          if List.exists (typ_uses_vars ctx.forall_bound) type_args then begin
            (* Keep call as-is, but transform term arguments *)
            let* term_args' = traverse_result (List.map (transform_term ctx) term_args) in
            Ok (T.Call (def_path, type_args, term_args'))
          end
          else begin
            (* The definition was monomorphized and we have concrete types!
              Transform: Call(foo, [T], args) 
              becomes:   Call(foo.mono, [], [Dtor(For, inst_i, args)]) *)
            let* transformed_args = traverse_result (List.map (transform_term ctx) term_args) in
            
            (* Build the current instantiation from type_args *)
            let current_inst = List.map typ_to_ground_arg type_args in
            
            (* Find the matching instantiation index *)
            (match List.find_index (fun i -> i = current_inst) info.instantiations with
              None -> 
                Error (NoMatchingInstantiation { def_path; instantiation = current_inst })
            | Some idx ->
                let dtor_path = dtor_name_for_inst info.generated_codata.name idx in
                (* Build: Call(foo.mono, [], [Dtor(For, inst_i, [], args)]) *)
                let dtor = T.Dtor (info.generated_codata, dtor_path, [], transformed_args) in
                Ok (T.Call (info.mono_path, [], [dtor])))
          end)
  
  | T.Add (t1, t2, t3) ->
      let* t1' = transform_term ctx t1 in
      let* t2' = transform_term ctx t2 in
      let* t3' = transform_term ctx t3 in
      Ok (T.Add (t1', t2', t3'))
  
  | T.Sub (t1, t2, t3) ->
      let* t1' = transform_term ctx t1 in
      let* t2' = transform_term ctx t2 in
      let* t3' = transform_term ctx t3 in
      Ok (T.Sub (t1', t2', t3'))
  
  | T.Ifz (cond, then_cmd, else_cmd) ->
      let* cond' = transform_term ctx cond in
      let* then_cmd' = transform_command ctx then_cmd in
      let* else_cmd' = transform_command ctx else_cmd in
      Ok (T.Ifz (cond', then_cmd', else_cmd'))
  
  | T.Ret (typ, tm) ->
      let* tm' = transform_term ctx tm in
      Ok (T.Ret (typ, tm'))
  
  | T.End -> Ok T.End

(* ========================================================================= *)
(* Definition Transformation                                                 *)
(* ========================================================================= *)

(** Transform a polymorphic definition into a monomorphic one.
    
    Original:
      def foo{a}(x: T[a], k: R[a]) = body
    
    Becomes:
      def foo.mono(u: cns foo.For) =
        ⟨Comatch(foo.For, [
            inst_0(x, k) => body[t0/a]
            inst_1(x, k) => body[t1/a]
            ...
          ]) | u⟩
*)
let transform_definition 
    (ctx: transform_ctx)
    (def: T.definition)
    (info: mono_info)
    : T.definition mono_check =
  
  let codata = info.generated_codata in
  let codata_typ = Sgn (codata.name, []) in
  
  (* Fresh variable for the consumer parameter *)
  let u = Ident.mk "u" in
  
  (* Generate one branch per instantiation *)
  let* branches = traverse_result (List.mapi (fun idx inst ->
    (* Create substitution: type_param_i -> inst_arg_i *)
    let subst = List.fold_left2 (fun acc (tvar, _kind) arg ->
      Ident.add tvar (ground_arg_to_typ arg) acc
    ) Ident.emptytbl def.type_params inst in
    
    (* The branch binds the original term parameter names *)
    let param_vars = List.map fst def.term_params in
    
    (* Specialize the body by applying the type substitution *)
    let specialized_body = subst_command subst def.body in
    
    (* Also transform any nested calls in the specialized body *)
    let* transformed_body = transform_command ctx specialized_body in
    
    (* Branch: (dtor_name, [], param_vars, transformed_body) *)
    let dtor_path = dtor_name_for_inst codata.name idx in
    Ok (dtor_path, [], param_vars, transformed_body)
  ) info.instantiations) in
  
  (* Body: ⟨Comatch(For, branches) | u⟩ *)
  let comatch = T.Comatch (codata, branches) in
  let body = T.Cut (codata_typ, comatch, T.Var u) in
  
  Ok { T.path = info.mono_path
     ; type_params = []                          (* Monomorphic! *)
     ; term_params = [(u, Cns codata_typ)]       (* Single consumer param *)
     ; body = body
     }

(* ========================================================================= *)
(* Main Entry Point                                                          *)
(* ========================================================================= *)

(** Monomorphize an execution context *)
let monomorphize (exe: Specialization.exe_ctx): mono_result mono_check =
  (* First, run the flow analysis *)
  match Specialization.analyze exe with
    Specialization.HasGrowingCycle cycle ->
      Error (GrowingCycle cycle)
  
  | Specialization.Solvable flows ->
      (* Group flows by destination definition *)
      let flows_by_def = 
        List.fold_left (fun acc (flow: Specialization.ground_flow) ->
          let existing = 
            match Path.find_opt flow.dst acc with
              Some lst -> lst | None -> []
          in
          Path.add flow.dst (flow.src :: existing) acc
        ) Path.emptytbl flows
      in
      
      (* Generate mono_info for each polymorphic definition that has instantiations *)
      let poly_defs = Path.to_list exe.defs 
        |> List.filter (fun (_path, (def: T.definition)) -> def.type_params <> [])
      in
      let mono_infos = poly_defs
        |> List.filter_map (fun (path, (def: T.definition)) ->
            let instantiations = 
              match Path.find_opt path flows_by_def with
                Some insts -> List.sort_uniq compare insts | None -> []
            in
            (* Only monomorphize if there are actual instantiations *)
            if instantiations = [] then None
            else begin
              let (codata, _codata_path) = 
                generate_codata_for_def def instantiations in
              let higher_rank = analyze_higher_rank_params def in
              let info = 
                { original_path = path
                ; type_params = def.type_params
                ; term_params = def.term_params
                ; instantiations
                ; generated_codata = codata
                ; mono_path = Path.access path "mono"
                ; higher_rank_params = higher_rank
                } in
              Some (path, info)
            end
          )
        |> Path.of_list
      in
      
      (* Build dtor_flows: group flows by destructor path (contains '.') *)
      let dtor_flows = 
        List.fold_left (fun acc (flow: Specialization.ground_flow) ->
          (* Check if destination path looks like a destructor (dec.dtor) *)
          let path_str = Path.name flow.dst in
          if String.contains path_str '.' then
            let existing = 
              match Path.find_opt flow.dst acc with
                Some _lst -> flow.src  (* Take the first/most recent for now *)
              | None -> flow.src
            in
            Path.add flow.dst existing acc
          else
            acc
        ) Path.emptytbl flows
      in
      
      (* Build forall_flows: collect all types flowing to simple paths (forall type vars) *)
      let forall_flows = 
        List.fold_left (fun acc (flow: Specialization.ground_flow) ->
          let path_str = Path.name flow.dst in
          (* Simple paths without '.' are forall type variable paths *)
          if not (String.contains path_str '.') then
            let existing = 
              match Path.find_opt flow.dst acc with
              | Some lst -> 
                  (* Add each type from flow.src if not already present *)
                  List.fold_left (fun l garg ->
                    if List.mem garg l then l else garg :: l
                  ) lst flow.src
              | None -> flow.src
            in
            Path.add flow.dst existing acc
          else
            acc
        ) Path.emptytbl flows
      in
      
      (* Build forall_param_flows: for paths like "def.param.forall_param" -> types *)
      let forall_param_flows =
        List.fold_left (fun acc (flow: Specialization.ground_flow) ->
          let path_str = Path.name flow.dst in
          if String.length path_str > 13 && 
             String.sub path_str (String.length path_str - 13) 13 = ".forall_param" then
            let existing = 
              match Path.find_opt flow.dst acc with
              | Some lst -> 
                  List.fold_left (fun l garg ->
                    if List.mem garg l then l else garg :: l
                  ) lst flow.src
              | None -> flow.src
            in
            Path.add flow.dst existing acc
          else
            acc
        ) Path.emptytbl flows
      in
      
      
      (* Build forall_to_for mapping: for each higher-rank parameter of a definition,
         find which mono_info has matching instantiation types *)
      let build_forall_to_for (def: T.definition): (dec * instantiation list) Ident.tbl =
        (* For each term parameter, check if it has a forall type *)
        List.fold_left (fun acc (param_var, param_ty) ->
          let ty = strip_chirality param_ty in
          if contains_forall ty then
            (* Build the forall_param path for this parameter *)
            let param_path = Path.access def.path (Ident.name param_var ^ ".forall_param") in
            
            (* Look up what types flow to this forall param *)
            match Path.find_opt param_path forall_param_flows with
            | Some forall_types ->
                (* Convert types to single-element instantiations for comparison *)
                let forall_insts = List.sort compare (List.map (fun t -> [t]) forall_types) in
                
                (* Find a mono_info whose instantiations match *)
                let matching_info = Path.to_list mono_infos |> List.find_opt (fun (_path, info) ->
                  let mono_insts = List.sort compare info.instantiations in
                  mono_insts = forall_insts
                ) in
                
                (match matching_info with
                | Some (_path, info) ->
                    Ident.add param_var (info.generated_codata, info.instantiations) acc
                | None -> acc)
            | None -> acc
          else
            acc
        ) Ident.emptytbl def.term_params
      in
      
      (* Transform a declaration's parameter types from Forall to For types *)
      let transform_dec_param_types (def: T.definition) (dec: dec): dec =
        let forall_to_for = build_forall_to_for def in
        let transformed_xtors = List.map (fun (xtor: xtor) ->
          let transformed_args = List.mapi (fun i ct ->
            let (param_var, _orig_ct) = List.nth def.term_params i in
            match Ident.find_opt param_var forall_to_for with
            | Some (for_dec, _insts) ->
                let for_typ = Sgn (for_dec.name, []) in
                chiral_map (fun _ -> for_typ) ct
            | None -> ct
          ) xtor.argument_types in
          { xtor with argument_types = transformed_args }
        ) dec.xtors in
        { dec with xtors = transformed_xtors }
      in
      
      (* Transform mono_infos to have the correct For-type in generated_codata *)
      let transformed_mono_infos = Path.map_tbl (fun info ->
        let orig_def = List.assoc info.original_path (Path.to_list exe.defs) in
        let transformed_codata = transform_dec_param_types orig_def info.generated_codata in
        { info with generated_codata = transformed_codata }
      ) mono_infos in
      
      (* Also rebuild forall_to_for with transformed codata *)
      let build_transformed_forall_to_for (def: T.definition): (dec * instantiation list) Ident.tbl =
        List.fold_left (fun acc (param_var, param_ty) ->
          let ty = strip_chirality param_ty in
          if contains_forall ty then
            let param_path = Path.access def.path (Ident.name param_var ^ ".forall_param") in
            match Path.find_opt param_path forall_param_flows with
            | Some forall_types ->
                let forall_insts = List.sort compare (List.map (fun t -> [t]) forall_types) in
                let matching_info = Path.to_list transformed_mono_infos |> List.find_opt (fun (_path, info) ->
                  let mono_insts = List.sort compare info.instantiations in
                  mono_insts = forall_insts
                ) in
                (match matching_info with
                | Some (_path, info) ->
                    Ident.add param_var (info.generated_codata, info.instantiations) acc
                | None -> acc)
            | None -> acc
          else
            acc
        ) Ident.emptytbl def.term_params
      in
      
      let inline_forall_decs = ref [] in
      
      (* Transform all definitions using transformed_mono_infos *)
      let* transformed_defs = traverse_result (Path.to_list exe.defs |> List.map (fun (path, def) ->
        let forall_to_for = build_transformed_forall_to_for def in
        let ctx = { mono_infos = transformed_mono_infos; dtor_flows; forall_flows; forall_bound = []; inline_forall_decs; forall_to_for } in
        
        match Path.find_opt path transformed_mono_infos with
        | Some info -> transform_definition ctx def info
        | None -> 
            (* Non-polymorphic definition: just transform calls *)
            let* body' = transform_command ctx def.body in
            Ok { def with body = body' }
      )) in
      
      (* Also transform main (main is typically monomorphic) *)
      let main_forall_to_for = build_transformed_forall_to_for exe.main in
      let main_ctx = { mono_infos = transformed_mono_infos; dtor_flows; forall_flows; forall_bound = []; inline_forall_decs; forall_to_for = main_forall_to_for } in
      let* main_body' = transform_command main_ctx exe.main.body in
      let transformed_main = { exe.main with body = main_body' } in
      
      (* The declarations are already transformed in transformed_mono_infos *)
      let new_decs = Path.to_list transformed_mono_infos 
        |> List.map (fun (_, info) -> info.generated_codata) in
      
      Ok
        { main = transformed_main
        ; definitions = transformed_defs
        ; new_declarations = new_decs
        ; mono_infos = transformed_mono_infos
        }
