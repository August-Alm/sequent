open Common.Identifiers

type name = Ident.t

type context =
  { decl_map: name Ident.tbl (* (name * name) list *)
  ; tparam_map: (name * int) Ident.tbl (* (name * (name * int)) list *)
  }

type mono_arg = 
    MonoBase of name
  | MonoIndex of name * int
  | MonoEnum of name * mono_arg list

type flow_input = 
    Vector of mono_arg list
  | Var of name

type flow =
  { input: flow_input
  ; dst: name
  }

(* Infer monad *)
type 'a infer = context -> ('a * context * flow list)

let ( let+ ) (m: 'a infer) (f: 'a -> 'b infer): 'b infer =
  fun ctx ->
    let (a, ctx1, flows1) = m ctx in
    let (b, ctx2, flows2) = f a ctx1 in
    (b, ctx2, flows1 @ flows2)

let return (a: 'a): 'a infer =
  fun ctx -> (a, ctx, [])

let map (f: 'a -> 'b) (m: 'a infer): 'b infer =
  fun ctx ->
    let (a, ctx1, flows) = m ctx in
    (f a, ctx1, flows)

let emit (flows: flow list): unit infer =
  fun ctx -> ((), ctx, flows)

let record_decl (name: name) (mvar: name): unit infer =
  fun ctx ->
    ((), { ctx with decl_map = Ident.add name mvar ctx.decl_map }, [])

let lookup_decl (name: name): name infer =
  fun ctx ->
    (Ident.find name ctx.decl_map, ctx, [])

let record_type_param (name: name) (mvar: name * int): unit infer =
  fun ctx ->
    ((), { ctx with tparam_map = Ident.add name mvar ctx.tparam_map }, [])

let sequence (lst: 'a infer list): 'a list infer =
  let rec go acc = function
    | [] -> return (List.rev acc)
    | m :: rest -> let+ a = m in go (a :: acc) rest
  in
  go [] lst

let traverse (lst: 'a list) (f: 'a -> 'b infer): 'b list infer =
  sequence (List.map f lst)

(* AST (simplified). Can we modularize? *)
type type_ = Base of name | Var of name | Enum of name * type_ list
type param = { name: name; tpe: type_ }

(* Lookup type recursively, translating to mono args *)
let rec lookup_type_direct (tpe: type_) (ctx: context): mono_arg =
  match tpe with
  | Base name -> MonoBase name
  | Var name -> 
      let (mvar, idx) = Ident.find name ctx.tparam_map in
      MonoIndex (mvar, idx)
  | Enum (name, targs) ->
      MonoEnum (name, List.map (fun t -> lookup_type_direct t ctx) targs)

let lookup_type (tpe: type_): mono_arg infer =
  fun ctx -> (lookup_type_direct tpe ctx, ctx, [])

(* Constraint generation *)
let rec generate_for_type (tpe: type_): unit infer =
  match tpe with
  | Base _ | Var _ -> return ()
  | Enum (name, targs) ->
      let+ dst = lookup_decl name in
      let+ margs = traverse targs lookup_type in
      let+ () = emit [{ input = Vector margs; dst }] in
      traverse targs generate_for_type |> map (fun _ -> ())

type term =
  | Block of decl list * term
  | App of name * type_ list * term list
  | Match of term * rule list
  | Var of name | Lit of string | Let of name * term * term
  | BinOp of term * string * term
  | If of term * term * term
  | Magic of type_

and rule = {
  case: name;
  mvar: name;
  tparams: name list;
  body: term;
}

and decl = {
  name: name;
  mvar: name;
  tparams: name list;
  body: decl_body;
}

and decl_body =
  | DeclEnum of decl list
  | DeclDef of param list * type_ * term
  | DeclSig of param list * type_

let rec generate_for_decl (decl: decl): unit infer =
  let+ _ = traverse 
    (List.mapi (fun i tp -> (tp, i)) decl.tparams)
    (fun (tp, i) -> record_type_param tp (decl.mvar, i)) in
  match decl.body with
  | DeclEnum members ->
      traverse members generate_for_decl |> map (fun _ -> ())
  | DeclDef (params, ret_type, body) ->
      let+ _ = traverse params (fun p -> generate_for_type p.tpe) in
      let+ _ = generate_for_type ret_type in
      generate_for_term body
  | DeclSig (params, ret_type) ->
      let+ _ = traverse params (fun p -> generate_for_type p.tpe) in
      generate_for_type ret_type

and generate_for_term (term: term): unit infer =
  match term with
  | Block (decls, rest) ->
      let+ _ = traverse decls (fun d -> record_decl d.name d.mvar) in
      let+ _ = traverse decls generate_for_decl in
      generate_for_term rest
  | App (fun_name, targs, args) ->
      let+ mvar = lookup_decl fun_name in
      let+ margs = traverse targs lookup_type in
      let+ _ = emit [{ input = Vector margs; dst = mvar }] in
      traverse args generate_for_term |> map (fun _ -> ())
  | Match (scrut, rules) ->
      let+ () = generate_for_term scrut in
      traverse rules (fun rule ->
        let+ _ = traverse (List.mapi (fun i tp -> (tp, i)) rule.tparams)
          (fun (tp, i) -> record_type_param tp (rule.mvar, i)) in
        let+ case_mvar = lookup_decl rule.case in
        let+ _ = emit [{ input = Var case_mvar; dst = rule.mvar }] in
        generate_for_term rule.body
      ) |> map (fun _ -> ())
  | Var _ | Lit _ | Magic _ -> return ()
  | Let (_, binding, body) ->
      let+ _ = generate_for_term binding in
      generate_for_term body
  | BinOp (left, _, right) ->
      let+ _ = generate_for_term left in
      generate_for_term right
  | If (cond, thn, els) ->
      let+ _ = generate_for_term cond in
      let+ _ = generate_for_term thn in
      generate_for_term els

(* Run *)
let run (m: unit infer): flow list =
  let (_, _, flows) = m { decl_map = Ident.emptytbl; tparam_map = Ident.emptytbl } in
  flows
(* CycleChecker - finds growing cycles in monomorphization constraints *)

type index = int
type node = name * index

type edge_type = Growing | Stable
type edge = { src: node; dst: node; tpe: edge_type }
type meta_edge = { src: name; dst: name }

exception CycleException of node list

(* Map module for nodes *)
module NodeMap = Map.Make(struct
  type t = node
  let compare = compare
end)

(* BFS implementation *)
let bfs (start: node) (target: node) (graph: node -> node list option): node list option =
  let rec go visited queue =
    match queue with
    | [] -> None
    | node :: _ when node = target -> 
        Some (List.rev (target :: visited))
    | (name, idx) :: rest ->
        match graph (name, idx) with
        | None -> go visited rest
        | Some neighbors ->
            let unvisited = List.filter (fun n -> not (List.mem n visited)) neighbors in
            go ((name, idx) :: visited) (rest @ unvisited)
  in
  go [] [start]

(* Convert edges to adjacency graph *)
let edges_to_graph (edges: edge list): node list NodeMap.t =
  List.fold_left (fun acc (edge: edge) ->
    let neighbors: node list = 
      try NodeMap.find edge.src acc 
      with Not_found -> []
    in
    NodeMap.add edge.src (edge.dst :: neighbors) acc
  ) NodeMap.empty edges

(* Convert meta-edges to a function *)
let metas_to_fun (metas: meta_edge list): node -> node list option =
  let map: (name, name list) Hashtbl.t = Hashtbl.create (List.length metas) in
  List.iter (fun (meta: meta_edge) ->
    let neighbors: name list = 
      try Hashtbl.find map meta.src 
      with Not_found -> []
    in
    Hashtbl.replace map meta.src (meta.dst :: neighbors)
  ) metas;
  
  fun (name, index) ->
    match Hashtbl.find_opt map name with
    | None -> None
    | Some dst_names -> Some (List.map (fun dst_name -> (dst_name, index)) dst_names)

(* Extract edges from individual mono arguments *)
let rec arg_to_edges (src: mono_arg) (dst: name) (index: index): edge list =
  match src with
  | MonoBase _ -> []
  | MonoIndex (src_name, src_index) -> 
      [{ src = (src_name, src_index); dst = (dst, index); tpe = Stable }]
  | MonoEnum (_, targs) -> 
      List.concat_map (fun arg -> inner_arg_to_edges arg dst index) targs

(* Extract growing edges from nested enum arguments *)
and inner_arg_to_edges (src: mono_arg) (dst: name) (index: index): edge list =
  match src with
  | MonoEnum (_, targs) ->
      List.concat_map (fun arg -> inner_arg_to_edges arg dst index) targs
  | MonoBase _ -> []
  | MonoIndex (src_name, src_index) ->
      [{ src = (src_name, src_index); dst = (dst, index); tpe = Growing }]

(* Convert flows to edges *)
let flow_to_edges (flow: flow): edge list option * meta_edge option =
  match flow.input with
  | Vector args ->
      let edges = List.concat_map (fun (index, arg) ->
        arg_to_edges arg flow.dst index
      ) (List.mapi (fun i arg -> (i, arg)) args) in
      (Some edges, None)
  | Var src ->
      (None, Some { src; dst = flow.dst })

(* Find the smallest growing cycle *)
let find_growing_cycle (flows: flow list): node list option =
  (* Convert flows to edges and meta-edges *)
  let edges_and_metas = List.map flow_to_edges flows in
  let edges = List.concat (List.filter_map fst edges_and_metas) in
  let metas = List.filter_map snd edges_and_metas in
  
  (* Filter to only growing edges *)
  let growing_edges = List.filter (fun e -> e.tpe = Growing) edges in
  
  (* Build the graph *)
  let graph_map = edges_to_graph edges in
  let meta_fun = metas_to_fun metas in
  
  let full_fun (node: node) =
    match NodeMap.find_opt node graph_map with
    | Some neighbors -> Some neighbors
    | None -> meta_fun node
  in
  
  (* Do BFS from each growing edge's destination to its source *)
  let cycles = List.concat_map (fun (edge: edge) ->
    match bfs edge.dst edge.src full_fun with
    | None -> []
    | Some cycle -> [cycle]
  ) growing_edges in
  
  (* Return the shortest cycle *)
  match cycles with
  | [] -> None
  | cycles -> Some (List.fold_left (fun acc c ->
      if List.length c < List.length acc then c else acc
    ) (List.hd cycles) (List.tl cycles))

(* FlowSolver - solves flow constraints via fixpoint computation *)

type ground_arg =
  | GroundBase of name
  | GroundEnum of name * ground_arg list

type ground_flow_input = ground_arg list
type ground_flow = { src: ground_flow_input; dst: name }

(* Check if a mono arg contains type variables *)
let rec type_vars (arg: mono_arg): name list =
  match arg with
  | MonoBase _ -> []
  | MonoIndex (name, _) -> [name]
  | MonoEnum (_, targs) -> List.concat_map type_vars targs

(* Convert mono arg to ground arg if possible *)
let rec mono_arg_as_ground (arg: mono_arg): ground_arg option =
  match arg with
  | MonoEnum (name, targs) ->
      (match List.map mono_arg_as_ground targs |> List.fold_left (fun acc opt ->
        match (acc, opt) with
        | (Some lst, Some g) -> Some (g :: lst)
        | _ -> None
      ) (Some []) with
      | Some lst -> Some (GroundEnum (name, List.rev lst))
      | None -> None)
  | MonoBase name -> Some (GroundBase name)
  | MonoIndex (_, _) -> None

(* Convert ground arg back to mono arg *)
let rec ground_arg_as_mono (arg: ground_arg): mono_arg =
  match arg with
  | GroundBase name -> MonoBase name
  | GroundEnum (name, args) -> MonoEnum (name, List.map ground_arg_as_mono args)

(* Convert flow input to ground flow input if possible *)
let flow_input_as_ground (input: flow_input): ground_flow_input option =
  match input with
  | Vector args ->
      (match List.map mono_arg_as_ground args |> List.fold_left (fun acc opt ->
        match (acc, opt) with
        | (Some lst, Some g) -> Some (g :: lst)
        | _ -> None
      ) (Some []) with
      | Some lst -> Some (List.rev lst)
      | None -> None)
  | Var _ -> None

(* Partially instantiate a mono arg based on a ground flow *)
let rec partially_instantiate_mono_arg (arg: mono_arg) (fact: ground_flow): mono_arg =
  match arg with
  | MonoEnum (name, targs) -> 
      MonoEnum (name, List.map (fun t -> partially_instantiate_mono_arg t fact) targs)
  | MonoBase name -> MonoBase name
  | MonoIndex (name, index) when name = fact.dst ->
      (match List.nth_opt fact.src index with
      | Some g -> ground_arg_as_mono g
      | None -> MonoIndex (name, index))
  | MonoIndex (name, index) -> MonoIndex (name, index)

(* Partially instantiate a list of mono args *)
let partially_instantiate_args (args: mono_arg list) (fact: ground_flow): mono_arg list =
  List.map (fun arg -> partially_instantiate_mono_arg arg fact) args

(* Instantiate a rule based on facts *)
let rec instantiate_rule (rule: flow) (facts: ground_flow list): ground_flow list =
  match rule.input with
  | Vector args ->
      (match List.concat_map type_vars args |> List.find_opt (fun _ -> true) with
      | None ->
          (* Already ground *)
          (match flow_input_as_ground rule.input with
          | Some src -> [{ src; dst = rule.dst }]
          | None -> [])
      | Some tvar ->
          (* Instantiate the first type variable *)
          List.concat_map (fun fact ->
            if fact.dst = tvar then
              let new_args = partially_instantiate_args args fact in
              let new_rule = { input = Vector new_args; dst = rule.dst } in
              instantiate_rule new_rule facts
            else
              []
          ) facts)
  | Var src ->
      (* Forward all facts from src to dst *)
      List.filter_map (fun fact ->
        if fact.dst = src then
          Some { fact with dst = rule.dst }
        else
          None
      ) facts

(* Solve helper: apply all rules to current facts *)
let solve_helper (facts: ground_flow list) (rules: flow list): ground_flow list =
  let more_facts = List.concat_map (fun rule ->
    instantiate_rule rule facts
  ) rules in
  List.fold_left (fun acc fact ->
    if List.mem fact acc then acc else fact :: acc
  ) facts more_facts

(* Fixpoint operator *)
let rec fix_point (f: 'a -> 'a) (x: 'a): 'a =
  let x' = f x in
  if x' = x then x else fix_point f x'

(* Main solver *)
let solve (cs: flow list): ground_flow list =
  (* Divide flows into ground facts and rules *)
  let facts = ref [] in
  let rules = ref [] in
  
  List.iter (fun flow ->
    match flow_input_as_ground flow.input with
    | Some ground_src ->
        facts := { src = ground_src; dst = flow.dst } :: !facts
    | None ->
        rules := flow :: !rules
  ) cs;
  
  (* Apply fixpoint *)
  fix_point (fun fs -> solve_helper fs !rules) !facts

let meta_to_edge (meta: meta_edge) (nodes: (node) list): edge list =
  let ids = List.filter_map (fun (name, id) ->
    if name = meta.src || name = meta.dst then Some id else None
  ) nodes in
  List.map (fun id ->
    { src = (meta.src, id); dst = (meta.dst, id); tpe = Stable }
  ) ids