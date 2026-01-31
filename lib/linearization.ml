(**
  Module: Linearization
  Description: Pass B - Linearize variable usage in Cut terms with explicit substitutions
  
  This module implements the second pass of normalization, which:
  1. Analyzes free variable usage in each statement
  2. Inserts explicit Substitute statements to handle structural rules
  3. Handles contraction (variable used multiple times) by renaming
  4. Handles weakening (unused variables) by dropping
  5. Handles exchange (reordering) by rearranging variables
*)

open Common.Identifiers
module CutT = Cut.Terms

(** Compute free variables in a statement, with multiplicity *)
let rec free_vars_statement (s: CutT.statement) : (Ident.t * int) list =
  match s with
  | CutT.Jump _label -> []
  
  | CutT.Substitute (pairs, s') ->
    (* Free variables are those on the right-hand side of substitution pairs *)
    let rhs_vars = List.map snd pairs in
    let rhs_counts = count_occurrences rhs_vars in
    (* Also include free vars from the body that aren't bound by the substitution *)
    let body_vars = free_vars_statement s' in
    let bound = List.map fst pairs in
    let body_free = List.filter (fun (v, _) -> not (List.mem v bound)) body_vars in
    merge_var_counts rhs_counts body_free
  
  | CutT.Extern (_f, vars, branches) ->
    (* Free variables in vars *)
    let var_counts = count_occurrences vars in
    (* Plus free variables in branches *)
    let branch_vars = List.concat_map free_vars_extern_branch branches in
    merge_var_counts var_counts branch_vars
  
  | CutT.Let (v, _ctor, gamma, s') ->
    (* Free vars in gamma environment *)
    let gamma_vars = List.map fst gamma in
    let gamma_counts = count_occurrences gamma_vars in
    (* Free vars in body, minus the bound variable *)
    let body_vars = free_vars_statement s' in
    let body_free = List.filter (fun (x, _) -> not (Ident.equal x v)) body_vars in
    merge_var_counts gamma_counts body_free
  
  | CutT.New (v, _ty, gamma, branches, s') ->
    (* Free vars in gamma *)
    let gamma_vars = List.map fst gamma in
    let gamma_counts = count_occurrences gamma_vars in
    (* Free vars in branches *)
    let branch_vars = List.concat_map free_vars_branch branches in
    (* Free vars in continuation, minus bound variable *)
    let cont_vars = free_vars_statement s' in
    let cont_free = List.filter (fun (x, _) -> not (Ident.equal x v)) cont_vars in
    merge_var_counts gamma_counts (merge_var_counts branch_vars cont_free)
  
  | CutT.Switch (v, branches) ->
    (* Variable v is used once *)
    let v_count = [(v, 1)] in
    (* Plus free variables in all branches *)
    let branch_vars = List.concat_map free_vars_branch branches in
    merge_var_counts v_count branch_vars
  
  | CutT.Invoke (v, _dtor) ->
    (* Just the variable v *)
    [(v, 1)]

(** Free variables in a branch *)
and free_vars_branch ((_xtor, gamma, body): CutT.symbol * CutT.typ_env * CutT.statement) 
    : (Ident.t * int) list =
  (* Variables bound in the pattern *)
  let bound_vars = List.map fst gamma in
  (* Free variables in the body *)
  let body_vars = free_vars_statement body in
  (* Remove bound variables from free variables *)
  List.filter (fun (v, _) -> not (List.mem v bound_vars)) body_vars

(** Free variables in an extern branch *)
and free_vars_extern_branch ((gamma, body): CutT.typ_env * CutT.statement) 
    : (Ident.t * int) list =
  (* Variables bound in the pattern *)
  let bound_vars = List.map fst gamma in
  (* Free variables in the body *)
  let body_vars = free_vars_statement body in
  (* Remove bound variables from free variables *)
  List.filter (fun (v, _) -> not (List.mem v bound_vars)) body_vars

(** Count occurrences of variables in a list *)
and count_occurrences (vars: Ident.t list) : (Ident.t * int) list =
  let rec go vars acc =
    match vars with
    | [] -> acc
    | v :: rest ->
      let count = match List.assoc_opt v acc with
        | Some n -> n + 1
        | None -> 1
      in
      let acc' = (v, count) :: List.remove_assoc v acc in
      go rest acc'
  in
  go vars []

(** Merge two variable count lists, adding multiplicities *)
and merge_var_counts (xs: (Ident.t * int) list) (ys: (Ident.t * int) list) 
    : (Ident.t * int) list =
  let rec go xs ys =
    match xs with
    | [] -> ys
    | (v, n) :: rest ->
      let m = match List.assoc_opt v ys with
        | Some k -> k
        | None -> 0
      in
      (v, n + m) :: go rest (List.remove_assoc v ys)
  in
  go xs ys

(** Linearize a statement by inserting explicit substitutions
    
    @param current_env The current environment (list of available variables)
    @param s The statement to linearize
    @return A linearized statement with explicit substitutions
*)
let rec linearize_statement (current_env: Ident.t list) (s: CutT.statement) 
    : CutT.statement =
  match s with
  | CutT.Jump label ->
    (* Jump doesn't need variables, so drop all *)
    if current_env = [] then
      CutT.Jump label
    else
      (* Empty substitution effectively drops all variables *)
      CutT.Substitute ([], CutT.Jump label)
  
  | CutT.Substitute (pairs, s') ->
    (* Process the substitution *)
    let new_env = List.map fst pairs in
    linearize_statement new_env s'
  
  | CutT.Extern (f, vars, branches) ->
    (* Build substitution for extern statement *)
    let (subst, env_after) = build_substitution current_env vars [] in
    let branches' = List.map (linearize_extern_branch env_after) branches in
    prepend_subst subst (CutT.Extern (f, vars, branches'))
  
  | CutT.Let (v, ctor, gamma, s') ->
    (* Gamma lists the variables used by the constructor *)
    let gamma_vars = List.map fst gamma in
    let (subst, _env_after) = build_substitution current_env gamma_vars [] in
    (* After let, v is added to the environment *)
    let new_env = v :: current_env in
    let s_linearized = linearize_statement new_env s' in
    prepend_subst subst (CutT.Let (v, ctor, gamma, s_linearized))
  
  | CutT.New (v, ty, gamma, branches, s') ->
    (* Gamma lists variables in the new binding *)
    let gamma_vars = List.map fst gamma in
    let (subst, env_after_gamma) = build_substitution current_env gamma_vars [] in
    (* Linearize branches with their own environments *)
    let branches' = List.map (linearize_branch env_after_gamma) branches in
    (* After new, v is added to environment *)
    let new_env = v :: env_after_gamma in
    let s_linearized = linearize_statement new_env s' in
    prepend_subst subst (CutT.New (v, ty, gamma, branches', s_linearized))
  
  | CutT.Switch (v, branches) ->
    (* Build substitution that puts v first *)
    let (subst, env_after) = build_substitution current_env [v] [] in
    let branches' = List.map (linearize_branch env_after) branches in
    prepend_subst subst (CutT.Switch (v, branches'))
  
  | CutT.Invoke (v, dtor) ->
    (* Invoke uses variable v, everything else is dropped *)
    let (subst, _env_after) = build_substitution current_env [v] [] in
    prepend_subst subst (CutT.Invoke (v, dtor))

(** Linearize a branch 
    The branch binds new variables in its pattern and has a body
*)
and linearize_branch (current_env: Ident.t list) 
    ((xtor, gamma, body): CutT.symbol * CutT.typ_env * CutT.statement)
    : CutT.symbol * CutT.typ_env * CutT.statement =
  (* Variables bound by the pattern extend the environment *)
  let pattern_vars = List.map fst gamma in
  let new_env = pattern_vars @ current_env in
  let body' = linearize_statement new_env body in
  (xtor, gamma, body')

(** Linearize an extern branch
    Extern branches have (Γ) ⇒ s form
*)
and linearize_extern_branch (current_env: Ident.t list)
    ((gamma, body): CutT.typ_env * CutT.statement)
    : CutT.typ_env * CutT.statement =
  (* Variables bound by the pattern extend the environment *)
  let pattern_vars = List.map fst gamma in
  let new_env = pattern_vars @ current_env in
  let body' = linearize_statement new_env body in
  (gamma, body')

(** Build a substitution to transform current_env to support the needed variables
    
    @param current_env The current environment
    @param needed Variables needed (in order they'll be used)
    @param fresh_map Accumulator for fresh variables for contraction
    @return (substitution pairs, remaining environment after substitution)
*)
and build_substitution (_current_env: Ident.t list) (needed: Ident.t list)
    (fresh_map: (Ident.t * Ident.t list) list)
    : CutT.substitutions * Ident.t list =
  (* Count how many times each variable is needed *)
  let needed_counts = count_occurrences needed in
  
  (* For each needed variable, handle contraction if used multiple times *)
  let rec process_needed needed_list acc_subst acc_fresh_map =
    match needed_list with
    | [] -> (List.rev acc_subst, acc_fresh_map)
    | (v, count) :: rest ->
      if count = 1 then
        (* Single use: map v → v *)
        process_needed rest ((v, v) :: acc_subst) acc_fresh_map
      else
        (* Multiple uses: need to create fresh copies *)
        let existing_fresh = match List.assoc_opt v acc_fresh_map with
          | Some fs -> fs
          | None -> []
        in
        (* Generate fresh variables for remaining uses *)
        let fresh_vars = generate_fresh_vars v (count - List.length existing_fresh) in
        let all_fresh = existing_fresh @ fresh_vars in
        let acc_fresh_map' = (v, all_fresh) :: List.remove_assoc v acc_fresh_map in
        
        (* Use fresh variables in substitution *)
        let subst_entries = List.mapi (fun i _ ->
          if i = 0 then (v, v)
          else (List.nth all_fresh (i - 1), v)
        ) (List.init count (fun i -> i)) in
        
        process_needed rest (List.rev_append subst_entries acc_subst) acc_fresh_map'
  in
  
  let (subst_pairs, _fresh_map') = process_needed needed_counts [] fresh_map in
  
  (* The resulting environment contains the needed variables in order *)
  (subst_pairs, needed)

(** Generate n fresh variables based on a base variable *)
and generate_fresh_vars (_base: Ident.t) (n: int) : Ident.t list =
  List.init n (fun _ -> Ident.fresh ())

(** Prepend a substitution to a statement if non-empty *)
and prepend_subst (subst: CutT.substitutions) (s: CutT.statement) : CutT.statement =
  if subst = [] then s
  else CutT.Substitute (subst, s)

(** Main entry point: linearize a Cut program *)
let linearize_program (prog: CutT.program) : CutT.program =
  List.map (fun (label, gamma, body) ->
    (* Start with the environment defined by the function signature *)
    let initial_env = List.map fst gamma in
    let body' = linearize_statement initial_env body in
    (label, gamma, body')
  ) prog
