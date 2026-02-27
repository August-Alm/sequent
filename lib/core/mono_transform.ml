(**
  module: Core.Mono_transform
  description: Term and command transformation for monomorphization.
  
  This module handles the actual transformation of terms, commands, and
  definitions during monomorphization. It transforms polymorphic constructs
  into monomorphic equivalents using the codata types generated during analysis.
*)

open Common.Identifiers
open Common.Types
open Types.CoreBase
open Types.CoreTypes
open Mono_types

module T = Terms

(* ========================================================================= *)
(* Transformation Context                                                    *)
(* ========================================================================= *)

(** Context for transformation *)
type transform_ctx =
  { mono_infos: mono_info Path.tbl
  ; types_ctx: context  (* Type context for checking inhabitable kinds *)
  ; dtor_flows: Mono_spec.ground_arg list Path.tbl  (* dtor_path -> instantiations *)
  ; forall_flows: Mono_spec.ground_arg list Path.tbl  (* forall_path -> instantiation types *)
  ; forall_bound: Ident.t list  (* Type vars bound by enclosing NewForall *)
  ; inline_forall_decs: dec list ref  (* Accumulator for inline NewForall codata declarations *)
  ; forall_to_for: (dec * instantiation list * bool) Ident.tbl  (* Maps forall-typed var to (For-type codata, instantiations, is_inline) *)
  ; inline_for_by_insts: (dec * instantiation list) list  (* List of (codata, insts) for inline For-codatas *)
  }

(* ========================================================================= *)
(* Helper Functions                                                          *)
(* ========================================================================= *)

(** Check if a type uses any of the given type variables *)
let rec typ_uses_vars (vars: Ident.t list) (ty: typ): bool =
  match ty with
    TVar v -> List.mem v vars
  | TMeta _ | Base _ | Ext _ -> false
  | Sgn (_, args) -> List.exists (typ_uses_vars vars) args
  | Forall (_, k, b) -> typ_uses_vars vars k || typ_uses_vars vars b
  | Arrow (a, b) -> typ_uses_vars vars a || typ_uses_vars vars b
  | PromotedCtor (_, _, args) -> List.exists (typ_uses_vars vars) args

(** Check if a type contains ANY type variable (TVar) *)
let rec typ_has_tvar (ty: typ): bool =
  match ty with
    TVar _ -> true
  | TMeta _ | Base _ | Ext _ -> false
  | Sgn (_, args) -> List.exists typ_has_tvar args
  | Forall (_, k, b) -> typ_has_tvar k || typ_has_tvar b
  | Arrow (a, b) -> typ_has_tvar a || typ_has_tvar b
  | PromotedCtor (_, _, args) -> List.exists typ_has_tvar args

(** Find calls to monomorphized functions in a command.
    Returns list of (def_path, type_args) for each call found. *)
let rec find_mono_calls_in_cmd
    (mono_infos: mono_info Path.tbl) (cmd: T.command): (Path.t * typ list) list =
  match cmd with
    T.Cut (_, producer, consumer) ->
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
    T.Var _ | T.Lit _ | T.InstantiateDtor _ -> []
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
    T.Match (_dec, [(xtor, [], [u], cmd)]) ->
      (* Check if this is a match on raise.thunk *)
      if Path.equal xtor Prim.thunk_sym then
        (* Look for Cut(Var u, InstantiateDtor T) in the command *)
        (match cmd with
          T.Cut (_, T.Var v, T.InstantiateDtor inst_typ) 
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
    T.Cut (_, 
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
        Some (inst_typ, _) -> Some (f, inst_typ, arg, result_k)
      | None -> None)
  | _ -> None

(** Check if a NewForall calls a specific function polymorphically.
    Returns the function path if the body calls a function with the forall-bound type. *)
let find_called_function_in_newforall (tvar: Ident.t) (cmd: T.command): Path.t option =
  (* Look for a Call to a function that uses tvar *)
  let rec find_call cmd =
    match cmd with
      T.Call (path, type_args, _term_args) ->
        (* Check if one of the type args is our bound tvar *)
        let uses_tvar = List.exists (fun ty ->
          match ty with
            TVar v -> Ident.name v = Ident.name tvar | _ -> false
        ) type_args in
        if uses_tvar then Some path else None
    | T.Cut (_, producer, consumer) ->
        (* Look in both sides *)
        (match find_call_term producer with
          Some p -> Some p | None -> find_call_consumer consumer)
    | T.Add _ | T.Sub _ | T.Ifz _ | T.Ret _ | T.End -> None
  and find_call_term tm =
    match tm with
      T.Comatch (_, branches) | T.Match (_, branches) ->
        List.find_map (fun (_, _, _, cmd) -> find_call cmd) branches
    | T.NewForall (_, _, _, _, cmd) -> find_call cmd
    | T.MuCns (_, _, cmd) | T.MuPrd (_, _, cmd) -> find_call cmd
    | T.Ctor (_, _, args) | T.Dtor (_, _, _, args) ->
        List.find_map find_call_term args
    | _ -> None
  and find_call_consumer cns =
    match cns with
      T.Match (_, branches) | T.Comatch (_, branches) ->
        List.find_map (fun (_, _, _, cmd) -> find_call cmd) branches
    | T.MuCns (_, _, cmd) | T.MuPrd (_, _, cmd) -> find_call cmd
    | T.Dtor (_, _, _, args) ->
        List.find_map find_call_term args
    | _ -> None
  in
  find_call cmd

(** Generate an inline For-codata for a NewForall that doesn't reference a mono call.
    This is used for simple polymorphic lambdas like fun{c}(z: c) => z. *)
let generate_inline_for_codata
    (_tvar: Ident.t)
    (_body_typ: typ)
    (cont: Ident.t)
    (inst_types: Mono_spec.ground_arg list)
    : dec =
  ignore cont;  (* unused but kept for documentation *)
  let codata_path = Mono_types.fresh_inline_for_name () in
  let codata_typ = Sgn (codata_path, []) in
  
  let xtors = List.mapi (fun idx garg ->
    let inst_typ = ground_arg_to_typ garg in
    { name = dtor_name_for_inst codata_path idx
    ; quantified = []
    ; existentials = []
    ; argument_types = [Cns inst_typ]  (* Just the continuation *)
    ; main = codata_typ
    }
  ) inst_types in
  
  { name = codata_path
  ; data_sort = Codata
  ; param_kinds = []
  ; type_args = []
  ; xtors
  }

(* ========================================================================= *)
(* Term and Command Transformation                                           *)
(* ========================================================================= *)

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
        Some called_path ->
          (match Path.find_opt called_path ctx.mono_infos with
            Some info ->
              let for_dec = info.generated_codata in
              (* Create branches for the For-codata based on instantiations *)
              let* new_branches = traverse_result (List.mapi (fun idx _inst ->
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
      | Some (f_var, inst_typ, arg, _result_k) 
        when Ident.find_opt f_var ctx.forall_to_for <> None ->
          let (for_dec, instantiations, is_inline) = Ident.find f_var ctx.forall_to_for in
          let inst_garg = typ_to_ground_arg inst_typ in
          let idx_opt = List.find_index (fun inst ->
            match inst with
              [garg] -> garg = inst_garg | _ -> false
          ) instantiations in
          (match idx_opt with
            Some idx ->
              let dtor_path = dtor_name_for_inst for_dec.name idx in
              let for_typ = Sgn (for_dec.name, []) in
              let* arg' = transform_term ctx arg in
              let dtor = T.Dtor (for_dec, dtor_path, [], [arg'; T.Var var]) in
              if is_inline then begin
                (* Inline lambda case: f_var has type raise(For), need to unwrap before invoking destructor *)
                let raise_for_typ = Sgn (Prim.raise_sym, [for_typ]) in
                let g_var = Ident.mk "g" in
                let raise_dec =
                  { name = Prim.raise_sym
                  ; data_sort = Data
                  ; param_kinds = [for_typ]
                  ; type_args = [for_typ]
                  ; xtors =
                      [{ name = Prim.thunk_sym
                       ; quantified = []
                       ; existentials = []
                       ; argument_types = [Prd for_typ]
                       ; main = raise_for_typ
                       }]
                  } in
                let inner_cut = T.Cut (for_typ, T.Var g_var, dtor) in
                let raise_match = T.Match (raise_dec,
                  [(Prim.thunk_sym, [], [g_var], inner_cut)]) in
                let cut = T.Cut (raise_for_typ, T.Var f_var, raise_match) in
                Ok (T.MuPrd (typ, var, cut))
              end else begin
                (* Named function case: f_var has type For, invoke destructor directly *)
                let cut = T.Cut (for_typ, T.Var f_var, dtor) in
                Ok (T.MuPrd (typ, var, cut))
              end
          | None ->
              let* cmd' = transform_command ctx cmd in
              Ok (T.MuPrd (typ, var, cmd')))
      | _ ->
          let* cmd' = transform_command ctx cmd in
          Ok (T.MuPrd (typ, var, cmd')))
  | T.MuCns (typ, var, cmd) ->
      let* cmd' = transform_command ctx cmd in
      Ok (T.MuCns (typ, var, cmd'))
  | T.NewForall (tvar, _kind, body_typ, cont, cmd) ->
      (* A NewForall creates a polymorphic value. After monomorphization, this must
         become a Comatch over a For-type. We find the monomorphized function that
         the body calls and use its For-type.
         
         NewForall(a, k, body_typ, cont, cmd_with_call_f{a}(...))
         becomes:
         Comatch(f.For, [ inst_0(cont) => cmd[a:=T0], inst_1(cont) => cmd[a:=T1], ... ])
      *)
      let forall_path = Path.of_ident tvar in
      let inst_types = match Path.find_opt forall_path ctx.forall_flows with
          Some types -> types | None -> []
      in
      
      (* Find which monomorphized function is called in the body *)
      let mono_calls = find_mono_calls_in_cmd ctx.mono_infos cmd in
      
      (match mono_calls with
        [] ->
          (* No calls to monomorphized functions *)
          if inst_types = [] then begin
            (* No instantiations either - keep as-is *)
            let* cmd' = transform_command ctx cmd in
            Ok (T.NewForall (tvar, _kind, body_typ, cont, cmd'))
          end else begin
            (* Has instantiations but no mono calls - this is an inline polymorphic lambda.
               Look for a pre-generated inline For-codata with matching instantiations,
               or generate a fresh one. *)
            let inst_list = List.sort compare (List.map (fun t -> [t]) inst_types) in
            let matching_inline = List.find_opt (fun (_dec, insts) ->
              List.sort compare insts = inst_list
            ) ctx.inline_for_by_insts in
            
            let (inline_for, branch_inst_types) = match matching_inline with
              | Some (dec, insts) -> 
                  (* Use the declaration's instantiation order for branches *)
                  (dec, List.map (fun inst -> List.hd inst) insts)
              | None ->
                  (* No matching pre-generated codata - generate a fresh one *)
                  let fresh = generate_inline_for_codata tvar body_typ cont inst_types in
                  ctx.inline_forall_decs := fresh :: !(ctx.inline_forall_decs);
                  (fresh, inst_types)
            in
            
            (* Create branches for each instantiation.
               If using a pre-generated codata (for higher-rank param), it expects 2 args: (arg, cont).
               - The lambda body produces raise(fun(T, T)), we need to unwrap, apply to arg, send result to cont
               - Transform: ⟨raised_lambda | cont⟩ → ⟨raised_lambda | match raise { thunk(g) => ⟨g | apply(cont, arg)⟩ }⟩
               If using a freshly generated codata, it expects 1 arg: (cont). *)
            let uses_pregenerated = matching_inline <> None in
            let arg_var = Ident.mk "arg" in
            
            let* branches = traverse_result (List.mapi (fun idx garg ->
              let inst_typ = ground_arg_to_typ garg in
              let subst = Ident.add tvar inst_typ Ident.emptytbl in
              let cmd_subst = subst_command subst cmd in
              let* cmd' = transform_command ctx cmd_subst in
              let dtor_name = dtor_name_for_inst inline_for.name idx in
              if uses_pregenerated then begin
                (* For 2-arg case: wrap the command to apply the lambda to arg_var.
                   The original cmd' is ⟨raised_lambda | cont⟩ where raised_lambda produces raise(fun(T, T)).
                   We need to:
                   1. Unwrap the raise to get the raw function
                   2. Apply it to arg_var
                   3. Send result to cont
                   
                   Result: ⟨raised_lambda | match raise{fun(T,T)} { thunk(g) => ⟨g | apply(cont, arg)⟩ }⟩ *)
                let fun_typ = Sgn (Prim.fun_sym, [inst_typ; inst_typ]) in
                let raise_fun_typ = Sgn (Prim.raise_sym, [fun_typ]) in
                let fun_dec = 
                  { name = Prim.fun_sym
                  ; data_sort = Codata
                  ; param_kinds = [inst_typ; inst_typ]
                  ; type_args = [inst_typ; inst_typ]
                  ; xtors = 
                      [{ name = Prim.apply_sym
                       ; quantified = []
                       ; existentials = []
                       ; argument_types = [Cns inst_typ; Prd inst_typ]
                       ; main = fun_typ
                       }]
                  } in
                let raise_dec =
                  { name = Prim.raise_sym
                  ; data_sort = Data
                  ; param_kinds = [fun_typ]
                  ; type_args = [fun_typ]
                  ; xtors =
                      [{ name = Prim.thunk_sym
                       ; quantified = []
                       ; existentials = []
                       ; argument_types = [Prd fun_typ]
                       ; main = raise_fun_typ
                       }]
                  } in
                (* Extract the producer from cmd' (should be Cut(_, producer, Var cont)) *)
                let branch_cmd = match cmd' with
                  | T.Cut (_, producer, T.Var c) when Ident.equal c cont ->
                      (* Build: ⟨producer | match raise { thunk(g) => ⟨g | apply(cont, arg)⟩ }⟩ *)
                      let g_var = Ident.mk "g" in
                      let apply_dtor = T.Dtor (fun_dec, Prim.apply_sym, [], 
                        [T.Var cont; T.Var arg_var]) in
                      let inner_cut = T.Cut (fun_typ, T.Var g_var, apply_dtor) in
                      let raise_match = T.Match (raise_dec, 
                        [(Prim.thunk_sym, [], [g_var], inner_cut)]) in
                      T.Cut (raise_fun_typ, producer, raise_match)
                  | _ -> 
                      (* Can't restructure, use original *)
                      cmd'
                in
                Ok (dtor_name, [], [arg_var; cont], branch_cmd)
              end else
                Ok (dtor_name, [], [cont], cmd')
            ) branch_inst_types) in
            
            Ok (T.Comatch (inline_for, branches))
          end
      
      | (called_path, _type_args) :: _ ->
          (* Found a call to a monomorphized function. Use its For-type. *)
          (match Path.find_opt called_path ctx.mono_infos with
            None -> 
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
      Some ground_args when List.length ground_args = List.length tvars ->
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
      (* Special case: Cut with Var and InstantiateDtor - transform to Dtor if forall_to_for
        mapping exists *)
      (match producer, consumer with
        T.Var v, T.InstantiateDtor inst_typ when Ident.find_opt v ctx.forall_to_for <> None ->
          let (for_dec, instantiations, _is_inline) = Ident.find v ctx.forall_to_for in
          (* Find the index of this instantiation type in the instantiations list *)
          let inst_garg = typ_to_ground_arg inst_typ in
          let idx_opt = List.find_index (fun inst ->
            (* Each instantiation is a list of ground_args (type args) - compare first one *)
            match inst with [garg] -> garg = inst_garg | _ -> false
          ) instantiations in
          (match idx_opt with
            Some idx ->
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
            Some (inst_typ, _u) ->
              let (for_dec, instantiations, _is_inline) = Ident.find v ctx.forall_to_for in
              let inst_garg = typ_to_ground_arg inst_typ in
              let idx_opt = List.find_index (fun inst ->
                match inst with [garg] -> garg = inst_garg | _ -> false
              ) instantiations in
              (match idx_opt with
                Some idx ->
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
          (* Separate type args into inhabitable-kind (need concrete types for monomorphization)
             and data-kind (pass through as existentials, TVars are OK) *)
          let paired = List.combine type_args info.type_params in
          let inhabitable_type_args = List.filter_map (fun (ty_arg, (_var, kind)) ->
            if Mono_spec.is_inhabitable_kind ctx.types_ctx kind then Some ty_arg else None
          ) paired in
          let data_kind_type_args = List.filter_map (fun (ty_arg, (_var, kind)) ->
            if Mono_spec.is_inhabitable_kind ctx.types_ctx kind then None else Some ty_arg
          ) paired in
          
          (* Check if any INHABITABLE-kind type argument uses forall-bound type variables
             or has ANY type variable. Data-kind type args with TVars are fine - they
             pass through as existentials on the destructor. *)
          if List.exists (typ_uses_vars ctx.forall_bound) inhabitable_type_args 
             || List.exists typ_has_tvar inhabitable_type_args then begin
            (* Keep call as-is, but transform term arguments *)
            let* term_args' = traverse_result (List.map (transform_term ctx) term_args) in
            Ok (T.Call (def_path, type_args, term_args'))
          end
          else begin
            (* The definition was monomorphized and we have concrete types for inhabitable params!
              Transform: Call(foo, [T, k], args) where T is inhabitable, k is data-kind
              becomes:   Call(foo.mono, [], [Dtor(For, inst_i, [k], args)]) *)
            let* transformed_args = traverse_result (List.map (transform_term ctx) term_args) in
            
            (* Build the current instantiation from inhabitable type_args only *)
            let current_inst = List.map typ_to_ground_arg inhabitable_type_args in
            
            (* Find the matching instantiation index *)
            (match List.find_index (fun i -> i = current_inst) info.instantiations with
              None -> 
                Error (NoMatchingInstantiation { def_path; instantiation = current_inst })
            | Some idx ->
                let dtor_path = dtor_name_for_inst info.generated_codata.name idx in
                (* Build: Call(foo.mono, [], [Dtor(For, inst_i, [data_kind_args], term_args)]) *)
                let dtor = T.Dtor (info.generated_codata, dtor_path, data_kind_type_args, transformed_args) in
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
    
    Note: Only inhabitable-kind type params are monomorphized.
    Data-kind params (like `k: nat`) are kept as type params on foo.mono.
*)
let transform_definition 
    (ctx: transform_ctx)
    (def: T.definition)
    (info: mono_info)
    : T.definition mono_check =
  
  let codata = info.generated_codata in
  let codata_typ = Sgn (codata.name, []) in
  
  (* Filter type params to only inhabitable-kind ones (these get monomorphized) *)
  let inhabitable_type_params = List.filter (fun (_v, kind) ->
    Mono_spec.is_inhabitable_kind ctx.types_ctx kind
  ) def.type_params in
  
  (* Data-kind type params are kept on the mono definition *)
  let data_kind_params = List.filter (fun (_v, kind) ->
    not (Mono_spec.is_inhabitable_kind ctx.types_ctx kind)
  ) def.type_params in
  
  (* Fresh variable for the consumer parameter *)
  let u = Ident.mk "u" in
  
  (* Generate one branch per instantiation *)
  let* branches = traverse_result (List.mapi (fun idx inst ->
    (* Create substitution: inhabitable type_param_i -> inst_arg_i *)
    let subst = List.fold_left2 (fun acc (tvar, _kind) arg ->
      Ident.add tvar (ground_arg_to_typ arg) acc
    ) Ident.emptytbl inhabitable_type_params inst in
    
    (* The branch binds the original term parameter names *)
    let param_vars = List.map fst def.term_params in
    
    (* Data-kind type vars for this branch (quantified on the dtor) *)
    let data_kind_tvars = List.map fst data_kind_params in
    
    (* Specialize the body by applying the type substitution *)
    let specialized_body = subst_command subst def.body in
    
    (* Also transform any nested calls in the specialized body *)
    let* transformed_body = transform_command ctx specialized_body in
    
    (* Branch: (dtor_name, data_kind_tvars, param_vars, transformed_body) *)
    let dtor_path = dtor_name_for_inst codata.name idx in
    Ok (dtor_path, data_kind_tvars, param_vars, transformed_body)
  ) info.instantiations) in
  
  (* Body: ⟨Comatch(For, branches) | u⟩ *)
  let comatch = T.Comatch (codata, branches) in
  let body = T.Cut (codata_typ, comatch, T.Var u) in
  
  Ok { T.path = info.mono_path
     ; type_params = data_kind_params            (* Keep data-kind params *)
     ; term_params = [(u, Cns codata_typ)]       (* Single consumer param *)
     ; body = body
     }
