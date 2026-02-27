(**
  module: Core.Mono_spec
  description: Type specialization analysis for the Core language.
  
  This module implements flow-based type specialization analysis to determine
  all concrete type instantiations needed for a program, and to detect
  non-terminating (growing) cycles that would cause infinite specialization.
*)

open Common.Identifiers
open Common.Types
open Types.CoreTypes

(* ========================================================================= *)
(* Types                                                                     *)
(* ========================================================================= *)

(** Execution context: main function + top-level definitions *)
type exe_ctx = 
  { main: Terms.definition
  ; defs: Terms.definition Path.tbl
  ; types: Types.CoreTypes.context  (* Type context with data_kinds, promoted_ctors *)
  }

(** Monomorphic type argument - represents a type that may contain variables *)
type mono_arg = 
    MonoExt of ext_type                     (* External types like Int *)
  | MonoVar of Path.t * int                 (* Type variable: (definition path, param index) *)
  | MonoSgn of Path.t * mono_arg list       (* Applied type constructor *)

(** Flow constraint input *)
type flow_input = 
    Vector of mono_arg list   (* Concrete type arguments *)
  | Forward of Path.t         (* Forward all instantiations from another definition *)

(** A flow constraint: type arguments flow to a definition's type parameters *)
type flow =
  { input: flow_input
  ; dst: Path.t               (* Destination definition path *)
  }

(* ========================================================================= *)
(* Constraint Generation Monad                                               *)
(* ========================================================================= *)

(** Context for constraint generation *)
type gen_context =
  { defs: Terms.definition Path.tbl           (* All definitions *)
  ; types: Types.CoreTypes.context            (* Type context with data_kinds *)
  ; current_def: Path.t                       (* Current definition being analyzed *)
  ; tparam_map: (Path.t * int) Ident.tbl      (* Type var -> (definition, index) *)
  ; forall_param_map: Path.t Ident.tbl        (* Term var (of forall type) -> param path for flows *)
  }

(** Constraint generation monad: context -> (result, flows) *)
type 'a gen = gen_context -> ('a * flow list)

let return (a: 'a): 'a gen = fun _ -> (a, [])

let ( let+ ) (m: 'a gen) (f: 'a -> 'b gen): 'b gen =
  fun ctx ->
    let (a, flows1) = m ctx in
    let (b, flows2) = f a ctx in
    (b, flows1 @ flows2)

let map (f: 'a -> 'b) (m: 'a gen): 'b gen =
  fun ctx -> let (a, flows) = m ctx in (f a, flows)

let emit (flows: flow list): unit gen = fun _ -> ((), flows)

let get_context: gen_context gen = fun ctx -> (ctx, [])

let with_tparams (params: (Ident.t * int) list) (m: 'a gen): 'a gen =
  fun ctx ->
    let tparam_map = List.fold_left (fun tbl (v, i) ->
      Ident.add v (ctx.current_def, i) tbl
    ) ctx.tparam_map params in
    m { ctx with tparam_map }

let with_current_def (path: Path.t) (m: 'a gen): 'a gen =
  fun ctx -> m { ctx with current_def = path }

let sequence (lst: 'a gen list): 'a list gen =
  let rec go acc = function
      [] -> return (List.rev acc)
    | m :: rest -> let+ a = m in go (a :: acc) rest
  in go [] lst

let traverse (lst: 'a list) (f: 'a -> 'b gen): 'b list gen =
  sequence (List.map f lst)

let iter (lst: 'a list) (f: 'a -> unit gen): unit gen =
  traverse lst f |> map (fun _ -> ())

(* ========================================================================= *)
(* Type to mono_arg conversion                                                *)
(* ========================================================================= *)

(** Convert a Core type to a mono_arg, resolving type variables *)
let typ_to_mono_arg (t: typ): mono_arg gen =
  fun ctx ->
    let rec convert t =
      match t with
        Ext ext -> MonoExt ext
      | TVar v ->
          (match Ident.find_opt v ctx.tparam_map with
          | Some (def_path, idx) -> MonoVar (def_path, idx)
          | None -> 
              (* Free type variable - convert to a MonoSgn representing the variable *)
              MonoSgn (Path.of_ident v, []))
      | TMeta _ ->
          (* Metavariables shouldn't appear in well-typed programs *)
          failwith "Unexpected metavariable in monomorphization"
      | Sgn (name, args) ->
          MonoSgn (name, List.map convert args)
      | Arrow (t1, t2) ->
          (* Function types: encode as a special signature *)
          MonoSgn (Path.of_string "->", [convert t1; convert t2])
      | Forall (_v, _k, body) ->
          (* Polymorphic types - just convert the body, ignore the kind *)
          MonoSgn (Path.of_string "forall", [convert body])
      | Base pol ->
          (* Base polarities - convert to a MonoSgn for type identity *)
          let name = match pol with
            | Types.CoreBase.Pos -> "+"
            | Types.CoreBase.Neg -> "-"
          in
          MonoSgn (Path.of_string name, [])
      | PromotedCtor (data_name, ctor_name, args) ->
          (* Promoted constructors - preserve for type-checking.
             Convert to MonoSgn with a path like "'nat.zero" *)
          let promoted_path = Path.of_string ("'" ^ Path.name data_name ^ "." ^ Path.name ctor_name) in
          MonoSgn (promoted_path, List.map convert args)
    in
    (convert t, [])

(** Check if a type has a free TVar (not in tparam_map).
    Free TVars indicate GADT existentials that can't be tracked. *)
let typ_has_free_tvar (t: typ): bool gen =
  fun ctx ->
    let rec has_free t =
      match t with
        Ext _ | TMeta _ | Base _ -> false
      | TVar v -> Ident.find_opt v ctx.tparam_map = None
      | Sgn (_, args) -> List.exists has_free args
      | Arrow (a, b) -> has_free a || has_free b
      | Forall (_, k, b) -> has_free k || has_free b
      | PromotedCtor (_, _, args) -> List.exists has_free args
    in
    (has_free t, [])

(** Check if a kind is inhabitable (i.e., can have values cut against it).
    Only `type` (Base _) and type constructors (Arrow ending in Base) are inhabitable.
    Data kinds like `nat` (Sgn where name is in data_kinds) are NOT inhabitable. *)
let rec is_inhabitable_kind (types_ctx: Types.CoreTypes.context) (k: typ): bool =
  match k with
  | Base _ -> true                        (* type is inhabitable *)
  | Arrow (_, result) -> is_inhabitable_kind types_ctx result  (* T -> type is inhabitable *)
  | Sgn (name, _) ->                      (* Check if this is a data kind *)
      (* If name is in data_kinds table, it's a promoted data type = uninhabitable *)
      Path.find_opt name types_ctx.data_kinds = None
  | PromotedCtor _ -> false               (* promoted constructors are not inhabitable *)
  | _ -> false                            (* conservative: treat unknown as not inhabitable *)

(* ========================================================================= *)
(* Constraint Generation for Terms and Commands                              *)
(* ========================================================================= *)

(** Check if a type is a forall type (wrapped in raise) *)
let rec is_forall_type (t: typ): bool =
  match t with
  | Forall _ -> true
  | Sgn (_, [arg]) -> is_forall_type arg  (* Check through raise wrapper *)
  | _ -> false

(** Generate constraints for a type (when it's used) *)
let generate_for_typ (t: typ): unit gen =
  let+ _marg = typ_to_mono_arg t in
  (* Just converting is enough - the constraints come from Call sites *)
  return ()

(** Generate constraints for a term *)
let rec generate_for_term (tm: Terms.term): unit gen =
  match tm with
    Var _ | Lit _ -> return ()
  
  | Ctor (dec, _xtor, args) ->
      (* Constructor: check if the declaration has type args *)
      let+ () = iter dec.type_args generate_for_typ in
      iter args generate_for_term
  
  | Dtor (dec, xtor, exist_tys, args) ->
      (* Process declaration type args *)
      let+ () = iter dec.type_args generate_for_typ in
      
      (* KEY: Emit flow constraint for existential type args!
         When we have Dtor(fold, [int], ...), emit [int] → fold_path
         so that comatch branches bound to fold_path get instantiated. *)
      let dtor_path = Path.access dec.name (Path.name xtor) in
      let+ mono_args = traverse exist_tys typ_to_mono_arg in
      let+ () = 
        if List.length mono_args > 0 then
          emit [{ input = Vector mono_args; dst = dtor_path }]
        else
          return ()
      in
      iter args generate_for_term
  
  | Match (dec, branches) ->
      let+ () = iter dec.type_args generate_for_typ in
      iter branches generate_for_branch
  
  | Comatch (dec, branches) ->
      let+ () = iter dec.type_args generate_for_typ in
      (* For each branch, emit a Forward from destructor path to current def,
         and bind branch type vars to the destructor's path so destructor
         existential instantiations flow to the branch. *)
      iter branches (generate_for_comatch_branch dec)
  
  | MuPrd (_typ, _var, cmd) ->
      generate_for_command cmd
  
  | MuCns (_typ, _var, cmd) ->
      generate_for_command cmd
  
  | NewForall (var, _kind, _typ, _cont, cmd) ->
      (* NewForall introduces a type variable that needs to be bound.
        Use Path.of_ident var as the path - the type variable identifier
        serves as its own identity for flow tracking.
        
        NOTE: Currently, flows to this path only come from `call id{a}(...)`
        inside the body. Without inter-procedural analysis, we can't connect
        InstantiateDtor sites to this forall's type variable. *)
      let forall_path = Path.of_ident var in
      fun ctx ->
        let tparam_map = Ident.add var (forall_path, 0) ctx.tparam_map in
        generate_for_command cmd { ctx with tparam_map }
  
  | InstantiateDtor _typ ->
      (* InstantiateDtor: for now, don't emit flows.
        The connection between instantiation sites and inline foralls
        requires more sophisticated inter-procedural analysis. *)
      return ()

(** Generate constraints for a branch (used for Match) *)
and generate_for_branch ((_xtor, _tyvars, _tmvars, cmd): Terms.branch): unit gen =
  generate_for_command cmd

(** Generate constraints for a comatch branch.
    
    This is the key to destructor existential specialization:
    When we have a Comatch like:
      comatch { fold[t](x) => ... }
    and a destructor call like:
      Dtor(fold, [int], ...)
    
    We need the [int] to flow to the branch's type variable t.
    
    We achieve this by:
    1. Binding the branch's type vars to the DESTRUCTOR's path (not the enclosing def)
    2. Emitting a Forward constraint from destructor path to current def
       (so that instantiations propagate transitively)
*)
and generate_for_comatch_branch (dec: dec) ((xtor, tyvars, _tmvars, cmd): Terms.branch): unit gen =
  (* Build the destructor's path: declaration path + destructor name *)
  let dtor_path = Path.access dec.name (Path.name xtor) in
  
  (* Bind branch type variables to the destructor's path, not the current def.
    This way, when Dtor(fold, [int], ...) emits [int] → fold_path,
    the branch's type var t (bound to fold_path index 0) will get int. *)
  let tparams_indexed = List.mapi (fun i v -> (v, i)) tyvars in
  
  (* Generate body with type vars bound to destructor path *)
  let+ _ctx = get_context in
  fun ctx ->
    let tparam_map = List.fold_left (fun tbl (v, i) ->
      Ident.add v (dtor_path, i) tbl
    ) ctx.tparam_map tparams_indexed in
    let ((), flows) = generate_for_command cmd { ctx with tparam_map } in
    (* Also emit a Forward from destructor path to current def for transitive flow *)
    let forward_flow = { input = Forward dtor_path; dst = ctx.current_def } in
    ((), forward_flow :: flows)

(** Find the definition path if this term contains a Call returning a forall type.
    This handles patterns like: MuPrd(∀a.T, k, Call(f, [], [Var k])) *)
and find_forall_call (tm: Terms.term): Path.t option =
  match tm with
    Terms.MuPrd (_typ, _var, Terms.Call (def_path, [], _args)) ->
      (* A MuPrd wrapping a Call with no type args - likely polymorphic call *)
      Some def_path
  | Terms.MuPrd (_typ, _var, cmd) ->
      (* Check for Call inside the command *)
      find_forall_call_in_cmd cmd
  | _ -> None

and find_forall_call_in_cmd (cmd: Terms.command): Path.t option =
  match cmd with
    Terms.Call (def_path, [], _args) -> Some def_path
  | Terms.Cut (_typ, producer, _consumer) -> find_forall_call producer
  | _ -> None

(** Find InstantiateDtor inside a term, including nested in Match branches.
    This handles patterns like: Match { ... ⟨var | InstantiateDtor(T)⟩ } *)
and find_instantiate_dtor (tm: Terms.term): typ option =
  match tm with
    Terms.InstantiateDtor ty -> Some ty
  | Terms.Match (_, branches) ->
      (* Look inside Match branches for InstantiateDtor *)
      List.find_map (fun (_, _, _, cmd) ->
        find_instantiate_dtor_cmd cmd
      ) branches
  | _ -> None

and find_instantiate_dtor_cmd (cmd: Terms.command): typ option =
  match cmd with
    Terms.Cut (_, _, consumer) -> find_instantiate_dtor consumer
  | _ -> None

(** Find NewForall type variable path in a term.
    This handles patterns like: Ctor(raise, thunk, [NewForall(a, ...)]) *)
and find_newforall_path (tm: Terms.term): Path.t option =
  match tm with
    Terms.NewForall (var, _, _, _, _) -> Some (Path.of_ident var)
  | Terms.Ctor (_, _, args) -> List.find_map find_newforall_path args
  | Terms.MuPrd (_, _, cmd) | Terms.MuCns (_, _, cmd) ->
      find_newforall_path_cmd cmd
  | _ -> None

and find_newforall_path_cmd (cmd: Terms.command): Path.t option =
  match cmd with
    Terms.Cut (_, producer, _) -> find_newforall_path producer
  | _ -> None

(** Generate constraints for a command *)
and generate_for_command (cmd: Terms.command): unit gen =
  match cmd with
    Cut (_typ, producer, consumer) ->
      (* Check for instantiation patterns:
        1. Direct: ⟨... Call(f, [], ...) ... | InstantiateDtor(T)⟩
        2. Via Match: ⟨MuPrd(_, _, Call(f, [], ...)) | Match { ... InstantiateDtor(T) }⟩ *)
      let+ () = 
        (match find_forall_call producer with
          Some def_path ->
            (* Producer calls a polymorphic function. Look for InstantiateDtor *)
            (match find_instantiate_dtor consumer with
              Some ty_arg ->
                let+ mono_arg = typ_to_mono_arg ty_arg in
                emit [{ input = Vector [mono_arg]; dst = def_path }]
            | None -> return ())
        | None -> return ())
      in
      (* Check for NewForall being instantiated:
         ⟨ Ctor(raise.thunk, [NewForall(a, ...)]) | ... InstantiateDtor(T) ... ⟩ *)
      let+ () =
        (match find_newforall_path producer with
          Some forall_path ->
            (* Producer has a NewForall. Look for InstantiateDtor in consumer *)
            (match find_instantiate_dtor consumer with
              Some ty_arg ->
                let+ mono_arg = typ_to_mono_arg ty_arg in
                emit [{ input = Vector [mono_arg]; dst = forall_path }]
            | None -> return ())
        | None -> return ())
      in
      (* Check for forall parameter being instantiated:
         ⟨Var f | Match { ... InstantiateDtor(T) }⟩ where f is forall param *)
      let+ () =
        (match producer with
          Terms.Var v ->
            let+ ctx = get_context in
            (match Ident.find_opt v ctx.forall_param_map with
              Some param_path ->
                (match find_instantiate_dtor consumer with
                  Some ty_arg ->
                    let+ mono_arg = typ_to_mono_arg ty_arg in
                    emit [{ input = Vector [mono_arg]; dst = param_path }]
                | None -> return ())
            | None -> return ())
        | _ -> return ())
      in
      let+ () = generate_for_term producer in
      generate_for_term consumer
  
  | Call (def_path, type_args, term_args) ->
      (* This is the key constraint generation site! *)
      (* Emit a flow: the type_args flow to the called definition,
         but ONLY for type params with inhabitable kinds (e.g., `type`).
         Data-kind params (like `k: nat`) don't need monomorphization. *)
      let+ ctx = get_context in
      (* Get the called definition to check parameter kinds *)
      let inhabitable_type_args = 
        match Path.find_opt def_path ctx.defs with
        | Some called_def ->
            (* Pair type_args with their kinds, filter to inhabitable ones *)
            let paired = List.combine type_args called_def.type_params in
            List.filter_map (fun (ty_arg, (_param_var, kind)) ->
              if is_inhabitable_kind ctx.types kind then Some ty_arg else None
            ) paired
        | None -> type_args  (* Conservative: include all if def not found *)
      in
      let+ mono_args = traverse inhabitable_type_args typ_to_mono_arg in
      let+ () = 
        if List.length mono_args > 0 then
          emit [{ input = Vector mono_args; dst = def_path }]
        else
          return ()
      in
      (* For each term argument that's a NewForall, emit Forward from param path *)
      let+ () =
        match Path.find_opt def_path ctx.defs with
          Some called_def ->
            let param_arg_pairs = List.combine called_def.term_params term_args in
            let forwards = List.filter_map (fun ((param_var, param_ty), arg) ->
              let ty = Types.CoreTypes.strip_chirality param_ty in
              if is_forall_type ty then
                (* This parameter has forall type. Check if arg contains NewForall *)
                match find_newforall_path arg with
                  Some forall_path ->
                    let param_path = Path.access def_path (Ident.name param_var ^ ".forall_param") in
                    Some { input = Forward param_path; dst = forall_path }
                | None -> None
              else None
            ) param_arg_pairs in
            emit forwards
        | None -> return ()
      in
      iter term_args generate_for_term
  
  | Add (t1, t2, t3) ->
      let+ () = generate_for_term t1 in
      let+ () = generate_for_term t2 in
      generate_for_term t3
  
  | Sub (t1, t2, t3) ->
      let+ () = generate_for_term t1 in
      let+ () = generate_for_term t2 in
      generate_for_term t3
  
  | Ifz (cond, then_cmd, else_cmd) ->
      let+ () = generate_for_term cond in
      let+ () = generate_for_command then_cmd in
      generate_for_command else_cmd
  
  | Ret (_typ, tm) ->
      generate_for_term tm
  
  | End -> return ()

(** Generate constraints for a definition *)
let generate_for_definition (def: Terms.definition): unit gen =
  (* Bind type parameters for this definition *)
  let tparams_indexed = List.mapi (fun i (v, _k) -> (v, i)) def.type_params in
  
  (* Build forall_param_map: for each term param of forall type, create a path *)
  let forall_params = List.filter_map (fun (v, chiral_ty) ->
    let ty = Types.CoreTypes.strip_chirality chiral_ty in
    if is_forall_type ty then
      let param_path = Path.access def.path (Ident.name v ^ ".forall_param") in
      Some (v, param_path)
    else None
  ) def.term_params in
  
  with_current_def def.path (
    with_tparams tparams_indexed (
      fun ctx ->
        let forall_param_map = List.fold_left (fun tbl (v, path) ->
          Ident.add v path tbl
        ) ctx.forall_param_map forall_params in
        generate_for_command def.body { ctx with forall_param_map }
    )
  )

(* ========================================================================= *)
(* Main entry point for constraint generation                                *)
(* ========================================================================= *)

(** Generate all flow constraints from an execution context *)
let generate_constraints (exe: exe_ctx): flow list =
  let initial_ctx = 
    { defs = exe.defs
    ; types = exe.types
    ; current_def = exe.main.path
    ; tparam_map = Ident.emptytbl
    ; forall_param_map = Ident.emptytbl
    }
  in
  (* Generate constraints for main (which should be monomorphic) *)
  let ((), main_flows) = generate_for_definition exe.main initial_ctx in
  
  (* Generate constraints for all other definitions *)
  let def_flows = Path.to_list exe.defs |> List.concat_map (fun (_path, def) ->
    let ((), flows) = generate_for_definition def initial_ctx in
    flows
  ) in
  
  let all_flows = main_flows @ def_flows in
  all_flows

(* ========================================================================= *)
(* Cycle detection - Finding growing cycles                                  *)
(* ========================================================================= *)

type index = int
type node = Path.t * index

type edge_type = Growing | Stable
type mono_edge = { edge_src: node; edge_dst: node; edge_type: edge_type }
type forward_edge = { fwd_src: Path.t; fwd_dst: Path.t }

module NodeMap = Map.Make(struct
  type t = node
  let compare (n, i) (m, j) =
    let k = Path.compare n m in
    if k <> 0 then k else Int.compare i j
end)

(** BFS to find a path from start to target *)
let bfs (start: node) (target: node) (graph: node -> node list option): node list option =
  let rec go visited queue =
    match queue with
      [] -> None
    | node :: _ when node = target -> 
        Some (List.rev (target :: visited))
    | (path, idx) :: rest ->
        match graph (path, idx) with
        | None -> go visited rest
        | Some neighbors ->
            let unvisited = List.filter (fun (p, i) ->
              not (List.exists (fun (v, j) -> Path.equal v p && i = j) visited)
            ) neighbors in
            go ((path, idx) :: visited) (rest @ unvisited)
  in
  go [] [start]

(** Convert edges to adjacency graph *)
let edges_to_graph (edges: mono_edge list): node list NodeMap.t =
  List.fold_left (fun acc edge ->
    let neighbors = 
      try NodeMap.find edge.edge_src acc 
      with Not_found -> []
    in
    NodeMap.add edge.edge_src (edge.edge_dst :: neighbors) acc
  ) NodeMap.empty edges

(** Convert meta-edges (forwards) to a lookup function *)
let metas_to_fun (metas: forward_edge list): node -> node list option =
  let map: (Path.t, Path.t list) Hashtbl.t = Hashtbl.create (List.length metas) in
  List.iter (fun meta ->
    let neighbors = 
      try Hashtbl.find map meta.fwd_src 
      with Not_found -> []
    in
    Hashtbl.replace map meta.fwd_src (meta.fwd_dst :: neighbors)
  ) metas;
  
  fun (path, index) ->
    match Hashtbl.find_opt map path with
      Some dst_paths -> Some (List.map (fun p -> (p, index)) dst_paths)
    | None -> None

(** Extract edges from a mono argument at top level (stable edges) *)
let rec arg_to_edges (src: mono_arg) (dst: Path.t) (index: index): mono_edge list =
  match src with
    MonoExt _ -> []
  | MonoVar (src_path, src_index) -> 
      [{ edge_src = (src_path, src_index); edge_dst = (dst, index); edge_type = Stable }]
  | MonoSgn (_, targs) -> 
      List.concat_map (fun arg -> inner_arg_to_edges arg dst index) targs

(** Extract edges from nested arguments (growing edges) *)
and inner_arg_to_edges (src: mono_arg) (dst: Path.t) (index: index): mono_edge list =
  match src with
    MonoSgn (_, targs) ->
      List.concat_map (fun arg -> inner_arg_to_edges arg dst index) targs
  | MonoExt _ -> []
  | MonoVar (src_path, src_index) ->
      [{ edge_src = (src_path, src_index); edge_dst = (dst, index); edge_type = Growing }]

(** Convert a flow to edges and/or a meta-edge *)
let flow_to_edges (flow: flow): mono_edge list option * forward_edge option =
  match flow.input with
    Vector args ->
      let edges = List.mapi (fun index arg ->
        arg_to_edges arg flow.dst index
      ) args |> List.concat in
      (Some edges, None)
  | Forward src ->
      (None, Some { fwd_src = src; fwd_dst = flow.dst })

(** Find the smallest growing cycle in the flow constraints *)
let find_growing_cycle (flows: flow list): node list option =
  let edges_and_metas = List.map flow_to_edges flows in
  let edges = List.concat (List.filter_map fst edges_and_metas) in
  let metas = List.filter_map snd edges_and_metas in
  
  let growing_edges = List.filter (fun e -> e.edge_type = Growing) edges in
  
  let graph_map = edges_to_graph edges in
  let meta_fun = metas_to_fun metas in
  
  let full_fun node =
    match NodeMap.find_opt node graph_map with
      Some neighbors -> Some neighbors | None -> meta_fun node
  in
  
  let cycles = List.concat_map (fun edge ->
    match bfs edge.edge_dst edge.edge_src full_fun with
      Some cycle -> [cycle] | None -> []
  ) growing_edges in
  
  match cycles with
    [] -> None
  | cycles -> Some (List.fold_left (fun acc c ->
      if List.length c < List.length acc then c else acc
    ) (List.hd cycles) (List.tl cycles))

(* ========================================================================= *)
(* Flow solver - Fixpoint computation                                        *)
(* ========================================================================= *)

(** Ground (fully instantiated) type argument *)
type ground_arg =
    GroundExt of ext_type
  | GroundSgn of Path.t * ground_arg list

(** A ground instantiation: specific type args for a definition *)
type ground_flow = 
  { src: ground_arg list
  ; dst: Path.t 
  }

(** Get all type variable references in a mono arg *)
let rec get_type_vars (arg: mono_arg): (Path.t * int) list =
  match arg with
    MonoExt _ -> []
  | MonoVar (path, idx) -> [(path, idx)]
  | MonoSgn (_, targs) -> List.concat_map get_type_vars targs

(** Convert mono arg to ground arg if possible *)
let rec mono_arg_as_ground (arg: mono_arg): ground_arg option =
  match arg with
    MonoExt ext -> Some (GroundExt ext)
  | MonoVar _ -> None
  | MonoSgn (name, targs) ->
      let rec collect_grounds acc = function
          [] -> Some (List.rev acc)
        | t :: rest ->
            match mono_arg_as_ground t with
              Some g -> collect_grounds (g :: acc) rest
            | None -> None
      in
      match collect_grounds [] targs with
        Some gs -> Some (GroundSgn (name, gs)) | None -> None

(** Convert ground arg back to mono arg *)
let rec ground_arg_as_mono (arg: ground_arg): mono_arg =
  match arg with
    GroundExt ext -> MonoExt ext
  | GroundSgn (name, args) -> MonoSgn (name, List.map ground_arg_as_mono args)

(** Convert flow input to ground if all args are ground *)
let flow_input_as_ground (input: flow_input): ground_arg list option =
  match input with
    Vector args ->
      let rec collect acc = function
          [] -> Some (List.rev acc)
        | t :: rest ->
            match mono_arg_as_ground t with
              Some g -> collect (g :: acc) rest | None -> None
      in
      collect [] args
  | Forward _ -> None

(** Partially instantiate a mono arg using a ground flow *)
let rec partially_instantiate (arg: mono_arg) (fact: ground_flow): mono_arg =
  match arg with
    MonoExt ext -> MonoExt ext
  | MonoVar (path, index) ->
      if Path.equal path fact.dst then
        match List.nth_opt fact.src index with
          Some g -> ground_arg_as_mono g
        | None -> MonoVar (path, index)
      else
        MonoVar (path, index)
  | MonoSgn (name, targs) -> 
      MonoSgn (name, List.map (fun t -> partially_instantiate t fact) targs)

(** Instantiate a flow rule using known ground facts *)
let rec instantiate_rule (rule: flow) (facts: ground_flow list): ground_flow list =
  match rule.input with
    Vector args ->
      let vars = List.concat_map get_type_vars args in
      (match vars with
        [] ->
          (* Already ground *)
          (match flow_input_as_ground rule.input with
            Some src -> [{ src; dst = rule.dst }] | None -> [])
      | (tvar_path, _) :: _ ->
          (* Instantiate the first type variable *)
          List.concat_map (fun fact ->
            if Path.equal tvar_path fact.dst then
              let new_args = List.map (fun a -> partially_instantiate a fact) args in
              let new_rule = { input = Vector new_args; dst = rule.dst } in
              instantiate_rule new_rule facts
            else
              []
          ) facts)
  | Forward src ->
      (* Forward all facts from src to dst *)
      List.filter_map (fun fact ->
        if Path.equal fact.dst src then Some { fact with dst = rule.dst }
        else None
      ) facts

(** One step of fixpoint iteration *)
let solve_step (facts: ground_flow list) (rules: flow list): ground_flow list =
  let more_facts = List.concat_map (fun rule ->
    instantiate_rule rule facts
  ) rules in
  List.fold_left (fun acc fact ->
    if List.mem fact acc then acc else fact :: acc
  ) facts more_facts

(** Fixpoint operator *)
let rec fix_point (f: 'a -> 'a) (x: 'a): 'a =
  let x' = f x in
  if x' = x then x else fix_point f x'

(** Solve flow constraints, returning all ground instantiations *)
let solve (constraints: flow list): ground_flow list =
  let facts = ref [] in
  let rules = ref [] in
  
  List.iter (fun flow ->
    match flow_input_as_ground flow.input with
      Some ground_src -> facts := { src = ground_src; dst = flow.dst } :: !facts
    | None -> rules := flow :: !rules
  ) constraints;
  
  fix_point (fun fs -> solve_step fs !rules) !facts

(* ========================================================================= *)
(* Main analysis interface                                                   *)
(* ========================================================================= *)

(** Result of monomorphization analysis *)
type analysis_result =
    Solvable of ground_flow list
  | HasGrowingCycle of node list

(** Analyze an execution context for monomorphization *)
let analyze (exe: exe_ctx): analysis_result =
  let constraints = generate_constraints exe in
  match find_growing_cycle constraints with
    Some cycle -> HasGrowingCycle cycle
  | None -> Solvable (solve constraints)

(** Check if constraints can be solved (no growing cycles) *)
let can_solve (exe: exe_ctx): bool =
  let constraints = generate_constraints exe in
  match find_growing_cycle constraints with
    Some _ -> false | None -> true
