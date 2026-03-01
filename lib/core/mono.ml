(**
  module: Core.Mono
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

(* Re-export types from Mono_types *)
include Mono_types

(* Re-export transform_ctx and transformation functions from Mono_transform *)
type transform_ctx = Mono_transform.transform_ctx

module T = Terms

(* ========================================================================= *)
(* Main Entry Point                                                          *)
(* ========================================================================= *)

(** Monomorphize an execution context *)
let monomorphize (exe: Mono_spec.exe_ctx): mono_result mono_check =
  (* First, run the flow analysis *)
  match Mono_spec.analyze exe with
    Mono_spec.HasGrowingCycle cycle ->
      Error (GrowingCycle cycle)
  
  | Mono_spec.Solvable flows ->
      (* Group flows by destination definition *)
      let flows_by_def = 
        List.fold_left (fun acc (flow: Mono_spec.ground_flow) ->
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
            (* Check if this definition has any inhabitable-kind type params *)
            let has_inhabitable_params = List.exists (fun (_v, kind) ->
              Mono_spec.is_inhabitable_kind exe.types kind
            ) def.type_params in
            (* Monomorphize if:
               1. There are actual instantiations from flow analysis, OR
               2. All type params are data-kind only (need trivial monomorphization
                  to produce the For-type wrapper) *)
            let final_instantiations = 
              if instantiations <> [] then instantiations
              else if not has_inhabitable_params then [[]]  (* Single trivial instantiation *)
              else []  (* No instantiations and has inhabitable params - skip *)
            in
            if final_instantiations = [] then None
            else begin
              let (codata, _codata_path) = 
                generate_codata_for_def exe.types def final_instantiations in
              let higher_rank = analyze_higher_rank_params def in
              let info = 
                { original_path = path
                ; type_params = def.type_params
                ; term_params = def.term_params
                ; instantiations = final_instantiations
                ; generated_codata = codata
                ; mono_path = Path.access path "mono"
                ; higher_rank_params = higher_rank
                } in
              Some (path, info)
            end
          )
        |> Path.of_list
      in
      
      (* Helper to group flows by a path predicate, accumulating source types *)
      let group_flows_by pred (flows: Mono_spec.ground_flow list) =
        List.fold_left (fun acc (flow: Mono_spec.ground_flow) ->
          if pred (Path.name flow.dst) then
            let existing = match Path.find_opt flow.dst acc with
                Some lst -> List.fold_left (fun l g -> if List.mem g l then l else g :: l) lst flow.src
              | None -> flow.src
            in
            Path.add flow.dst existing acc
          else acc
        ) Path.emptytbl flows
      in
      
      (* Build dtor_flows: group flows by destructor path (contains '.') *)
      let dtor_flows = group_flows_by (fun s -> String.contains s '.') flows in
      
      (* Build forall_flows: collect all types flowing to simple paths (forall type vars) *)
      let forall_flows = group_flows_by (fun s -> not (String.contains s '.')) flows in
      
      (* Build forall_param_flows: for paths like "def.param.forall_param" -> types *)
      let forall_param_flows = group_flows_by (String.ends_with ~suffix:".forall_param") flows in
      
      (* For each forall_param flow, check if there's a matching mono_info.
         If not, generate an inline For-codata for that higher-rank parameter. *)
      let inline_for_codatas: (dec * instantiation list) Path.tbl =
        Path.to_list forall_param_flows |> List.filter_map (fun (param_path, forall_types) ->
          let forall_insts = List.sort compare (List.map (fun t -> [t]) forall_types) in
          (* Check if any mono_info has matching instantiations *)
          let has_matching_mono = Path.to_list mono_infos |> List.exists (fun (_path, info) ->
            List.sort compare info.instantiations = forall_insts
          ) in
          if has_matching_mono then None
          else begin
            (* Generate an inline For-codata for this higher-rank parameter.
               
               For a higher-rank param like f: {c} c -> c, the destructor needs:
               - arg: Prd inst_typ (the argument being passed)
               - cont: Cns inst_typ (the continuation for the result)
               
               This matches the transform pattern:
               f{T}(x) → ⟨f | inst_T(x, k)⟩ where k is the result continuation *)
            let codata_name = fresh_inline_for_name () in
            let codata_typ = Sgn (codata_name, []) in
            (* Sort the types to ensure consistent ordering between declaration and usage *)
            let sorted_types = List.sort compare forall_types in
            let xtors = List.mapi (fun idx garg ->
              let inst_typ = ground_arg_to_typ garg in
              { name = dtor_name_for_inst codata_name idx
              ; quantified = []
              ; existentials = []
              ; argument_types = [Prd inst_typ; Cns inst_typ]  (* arg and continuation *)
              ; main = codata_typ
              }
            ) sorted_types in
            let inline_dec = 
              { name = codata_name
              ; data_sort = Codata
              ; param_kinds = []
              ; type_args = []
              ; xtors
              } in
            Some (param_path, (inline_dec, forall_insts))
          end
        ) |> Path.of_list
      in
      
      (* Build forall_to_for mapping: for each higher-rank parameter of a definition,
        find which mono_info or inline For-codata has matching instantiation types.
        Returns (dec, insts, is_inline) where is_inline=true means it came from inline_for_codatas. *)
      let build_forall_to_for mono_infos_tbl (def: T.definition): (dec * instantiation list * bool) Ident.tbl =
        List.fold_left (fun acc (param_var, param_ty) ->
          let ty = strip_chirality param_ty in
          if contains_forall ty then
            let param_path = Path.access def.path (Ident.name param_var ^ ".forall_param") in
            match Path.find_opt param_path forall_param_flows with
              Some forall_types ->
                let forall_insts = List.sort compare (List.map (fun t -> [t]) forall_types) in
                (* First check mono_infos *)
                let matching_info = Path.to_list mono_infos_tbl |> List.find_opt (fun (_path, info) ->
                  List.sort compare info.instantiations = forall_insts
                ) in
                (match matching_info with
                  Some (_path, info) ->
                    (* Named function case: is_inline=false *)
                    Ident.add param_var (info.generated_codata, info.instantiations, false) acc
                | None -> 
                    (* Check inline_for_codatas *)
                    (match Path.find_opt param_path inline_for_codatas with
                      Some (inline_dec, insts) ->
                        (* Inline lambda case: is_inline=true *)
                        Ident.add param_var (inline_dec, insts, true) acc
                    | None -> acc))
            | None -> acc
          else
            acc
        ) Ident.emptytbl def.term_params
      in
      
      (* Transform a declaration's parameter types from Forall to For types *)
      let transform_dec_param_types (def: T.definition) (dec: dec): dec =
        let forall_to_for = build_forall_to_for mono_infos def in
        let transformed_xtors = List.map (fun (xtor: xtor) ->
          let transformed_args = List.mapi (fun i ct ->
            let (param_var, _orig_ct) = List.nth def.term_params i in
            match Ident.find_opt param_var forall_to_for with
              Some (for_dec, _insts, is_inline) ->
                let for_typ = Sgn (for_dec.name, []) in
                if is_inline then begin
                  (* Inline lambda case: type is raise(For) *)
                  let raise_for_typ = Sgn (Prim.raise_sym, [for_typ]) in
                  chiral_map (fun _ -> raise_for_typ) ct
                end else
                  (* Named function case: type is just For *)
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
      
      let inline_forall_decs = ref [] in
      
      (* Build list of inline For-codatas with their instantiations for lookup during transformation *)
      let inline_for_by_insts = Path.to_list inline_for_codatas |> List.map snd in
      
      (* Transform all definitions using transformed_mono_infos *)
      let* transformed_defs = traverse_result (Path.to_list exe.defs |> List.map (fun (path, def) ->
        let forall_to_for = build_forall_to_for transformed_mono_infos def in
        let ctx: Mono_transform.transform_ctx = 
          { mono_infos = transformed_mono_infos
          ; types_ctx = exe.types
          ; dtor_flows
          ; forall_flows
          ; forall_bound = []
          ; inline_forall_decs
          ; forall_to_for
          ; inline_for_by_insts 
          } in
        
        match Path.find_opt path transformed_mono_infos with
          Some info -> Mono_transform.transform_definition ctx def info
        | None -> 
            (* Non-polymorphic definition: just transform calls *)
            let* body' = Mono_transform.transform_command ctx def.body in
            Ok { def with body = body' }
      )) in
      
      (* Also transform main (main is typically monomorphic) *)
      let main_forall_to_for = build_forall_to_for transformed_mono_infos exe.main in
      let main_ctx: Mono_transform.transform_ctx = 
        { mono_infos = transformed_mono_infos
        ; types_ctx = exe.types
        ; dtor_flows
        ; forall_flows
        ; forall_bound = []
        ; inline_forall_decs
        ; forall_to_for = main_forall_to_for
        ; inline_for_by_insts 
        } in
      let* main_body' = Mono_transform.transform_command main_ctx exe.main.body in
      let transformed_main = { exe.main with body = main_body' } in
      
      (* The declarations are already transformed in transformed_mono_infos *)
      let new_decs = Path.to_list transformed_mono_infos 
        |> List.map (fun (_, info) -> info.generated_codata) in
      
      (* Include inline For-codata declarations: both pre-generated ones and those from transformation *)
      let pregenerated_inline_decs = Path.to_list inline_for_codatas
        |> List.map (fun (_, (dec, _)) -> dec) in
      let all_new_decs = new_decs @ pregenerated_inline_decs @ !inline_forall_decs in
      
      Ok
        { main = transformed_main
        ; definitions = transformed_defs
        ; new_declarations = all_new_decs
        ; mono_infos = transformed_mono_infos
        }
