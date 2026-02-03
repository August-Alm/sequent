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
module CutTypes = Cut.Types

(** Look up a method signature by symbol *)
let lookup_method_signature (sigs: CutTypes.signature_defs) (method_sym: Path.t) 
    : (CutTypes.signature * CutTypes.method_sig) option =
  List.find_map (fun (_, (sig_def, _)) ->
    List.find_map (fun msig ->
      if Path.equal msig.CutTypes.symbol method_sym then
        Some (sig_def, msig)
      else None
    ) sig_def.CutTypes.methods
  ) sigs

(** Compute free variables in a statement, with multiplicity *)
let rec free_vars_statement (s: CutT.statement) : (Ident.t * int) list =
  match s with
  | CutT.Jump (_label, _type_args) -> []
  
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
  
  | CutT.Let (v, _ctor, _type_args, gamma, s') ->
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
  
  | CutT.Invoke (v, _dtor, _type_args, args) ->
    (* The variable v and all args *)
    [(v, 1)] @ count_occurrences args

(** Free variables in a branch *)
and free_vars_branch ((_xtor, _type_args, gamma, body): CutT.symbol * CutT.typ list * CutT.typ_env * CutT.statement) 
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

(** Merge variable counts taking maximum (for mutually exclusive branches) *)
and merge_var_counts_max (xs: (Ident.t * int) list) (ys: (Ident.t * int) list)
    : (Ident.t * int) list =
  let rec go xs ys =
    match xs with
    | [] -> ys
    | (v, n) :: rest ->
      let m = match List.assoc_opt v ys with
        | Some k -> k
        | None -> 0
      in
      (v, max n m) :: go rest (List.remove_assoc v ys)
  in
  go xs ys

(** Collect free variables from mutually exclusive branches (taking max, not sum) *)
and free_vars_branches_max (branches: (Ident.t * int) list list) : (Ident.t * int) list =
  match branches with
  | [] -> []
  | first :: rest ->
    List.fold_left merge_var_counts_max first rest

(** Deduplicate substitution pairs, keeping first occurrence of each target *)
let deduplicate_subst (subst: CutT.substitutions) : CutT.substitutions =
  let rec aux seen acc = function
    | [] -> List.rev acc
    | (target, source) :: rest ->
      if List.exists (fun t -> Ident.equal t target) seen then
        aux seen acc rest
      else
        aux (target :: seen) ((target, source) :: acc) rest
  in
  aux [] [] subst

(** Prepend a substitution to a statement if non-empty *)
let prepend_subst (subst: CutT.substitutions) (s: CutT.statement) : CutT.statement =
  if subst = [] then s
  else 
    (* First deduplicate the substitution itself *)
    let subst_deduped = deduplicate_subst subst in
    match s with
    | CutT.Substitute (inner_subst, _s') ->
      (* If continuation already has a substitution, avoid duplicating variables *)
      let inner_targets = List.map fst inner_subst in
      let subst_filtered = List.filter (fun (target, _) ->
        not (List.mem target inner_targets)
      ) subst_deduped in
      if subst_filtered = [] then
        (* All our substitutions are redundant, just use inner *)
        s
      else
        CutT.Substitute (subst_filtered, s)
    | _ ->
      CutT.Substitute (subst_deduped, s)

(** Linearize a statement by inserting explicit substitutions
    
    @param sigs The signature definitions for looking up constructor/destructor signatures
    @param prog The program with all label definitions
    @param current_env The current environment (list of available variables)
    @param s The statement to linearize
    @return A linearized statement with explicit substitutions
*)
let rec linearize_statement (sigs: CutTypes.signature_defs) (prog: CutT.program) (current_env: Ident.t list) (s: CutT.statement) 
    : CutT.statement =
  match s with
  | CutT.Jump (label, type_args) ->
    (* Look up the target label's expected environment *)
    let target_env = 
      match List.find_opt (fun (l, _, _) -> CutT.Label.to_string l = CutT.Label.to_string label) prog with
      | Some (_, gamma, _) -> List.map fst gamma
      | None -> failwith ("Jump to undefined label: " ^ CutT.Label.to_string label)
    in
    (* Build substitution mapping target params to current env vars *)
    let subst = List.combine target_env current_env in
    CutT.Substitute (subst, CutT.Jump (label, type_args))
  
  | CutT.Substitute (_pairs, s') ->
    (* This shouldn't appear in input from collapsing, but handle it anyway *)
    (* Just process the inner statement with current environment *)
    linearize_statement sigs prog current_env s'
  
  | CutT.Extern (f, vars, branches) ->
    (* Build substitution for extern statement *)
    let free_in_branches = List.concat_map free_vars_extern_branch branches in
    let preserve = List.filter (fun v -> not (List.mem v vars)) 
      (List.map fst free_in_branches) in
    let (subst, env_after) = build_substitution current_env vars preserve [] in
    let branches' = List.map (linearize_extern_branch sigs prog env_after) branches in
    prepend_subst subst (CutT.Extern (f, vars, branches'))
  
  | CutT.Let (v, ctor, type_args, gamma, s') ->
    (* Gamma lists the variables used by the constructor *)
    let gamma_vars = List.map fst gamma in
    
    (* Build substitution for variable flow using actual variables from gamma *)
    let free_in_cont = free_vars_statement s' in
    let preserve = List.filter (fun var -> 
      not (List.mem var gamma_vars) && 
      not (Ident.equal var v) &&
      List.mem var current_env
    ) (List.map fst free_in_cont) in
    
    (* Build flow substitution using gamma_vars (what's actually in the environment) *)
    let (subst, env_after) = build_substitution current_env gamma_vars preserve [] in
    
    (* After let, v is added to the environment *)
    let new_env = v :: env_after in
    let s_linearized = linearize_statement sigs prog new_env s' in
    
    (* Prepend the substitution to handle variable flow *)
    prepend_subst subst (CutT.Let (v, ctor, type_args, gamma, s_linearized))
  
  | CutT.New (v, ty, gamma, branches, s') ->
    (* Gamma lists variables in the new binding *)
    let gamma_vars = List.map fst gamma in
    (* Branches are mutually exclusive - take max, not sum *)
    let branch_free_lists = List.map free_vars_branch branches in
    let free_in_branches = free_vars_branches_max branch_free_lists in
    let free_in_cont = free_vars_statement s' in
    let all_free = merge_var_counts free_in_branches free_in_cont in
    (* Only preserve variables that are:
       1. Not consumed by the new binding (not in gamma_vars)
       2. Not the variable being bound (not v itself)
       3. Actually in current_env (not future variables) *)
    let preserve = List.filter (fun var -> 
      not (List.mem var gamma_vars) && 
      not (Ident.equal var v) &&
      List.mem var current_env
    ) (List.map fst all_free) in
    let (subst, env_after_gamma) = build_substitution current_env gamma_vars preserve [] in
    (* Linearize branches with their own environments *)
    let branches' = List.map (linearize_branch sigs prog env_after_gamma) branches in
    (* After new, v is added to environment *)
    let new_env = v :: env_after_gamma in
    let s_linearized = linearize_statement sigs prog new_env s' in
    prepend_subst subst (CutT.New (v, ty, gamma, branches', s_linearized))
  
  | CutT.Switch (v, branches) ->
    (* Build substitution that puts v first *)
    (* Branches are mutually exclusive - take max, not sum *)
    let branch_free_lists = List.map free_vars_branch branches in
    let free_in_branches = free_vars_branches_max branch_free_lists in
    let preserve = List.filter (fun w -> not (Ident.equal w v))
      (List.map fst free_in_branches) in
    let (subst, env_after) = build_substitution current_env [v] preserve [] in
    (* Remove v from env_after since it's consumed by the switch *)
    let env_for_branches = List.filter (fun w -> not (Ident.equal w v)) env_after in
    let branches' = List.map (linearize_branch sigs prog env_for_branches) branches in
    prepend_subst subst (CutT.Switch (v, branches'))
  
  | CutT.Invoke (v, dtor, type_args, args) ->
    (* Invoke uses variable v and all args, everything else is dropped *)
    (* INVOKE rule: Γ, v : cns T, so v comes first (rightmost = head) *)
    let needed = v :: args in
    let (subst, _env_after) = build_substitution current_env needed [] [] in
    prepend_subst subst (CutT.Invoke (v, dtor, type_args, args))

(** Linearize a branch 
    The branch binds new variables in its pattern and has a body
*)
and linearize_branch (sigs: CutTypes.signature_defs) (prog: CutT.program) (current_env: Ident.t list) 
    ((xtor, type_args, gamma, body): CutT.symbol * CutT.typ list * CutT.typ_env * CutT.statement)
    : CutT.symbol * CutT.typ list * CutT.typ_env * CutT.statement =
  (* Variables bound by the pattern extend the environment *)
  let pattern_vars = List.map fst gamma in
  
  (* Linearize the body with pattern variables + outer environment *)
  let new_env = pattern_vars @ current_env in
  let body' = linearize_statement sigs prog new_env body in
  
  (* Return branch with original gamma (pattern variables and their types) *)
  (xtor, type_args, gamma, body')

(** Linearize an extern branch
    Extern branches have (Γ) ⇒ s form
*)
and linearize_extern_branch (sigs: CutTypes.signature_defs) (prog: CutT.program) (current_env: Ident.t list)
    ((gamma, body): CutT.typ_env * CutT.statement)
    : CutT.typ_env * CutT.statement =
  (* Variables bound by the pattern extend the environment *)
  let pattern_vars = List.map fst gamma in
  let new_env = pattern_vars @ current_env in
  let body' = linearize_statement sigs prog new_env body in
  (gamma, body')

(** Build a substitution to transform current_env to support the needed variables
    
    @param current_env The current environment
    @param needed Variables needed immediately (in order they'll be used)
    @param preserve Additional variables to preserve in the environment
    @param fresh_map Accumulator for fresh variables for contraction
    @return (substitution pairs, resulting environment after substitution)
*)
and build_substitution (_current_env: Ident.t list) (needed: Ident.t list)
    (preserve: Ident.t list) (fresh_map: (Ident.t * Ident.t list) list)
    : CutT.substitutions * Ident.t list =
  (* Result environment should be: needed @ preserve *)
  let all_vars = needed @ preserve in
  (* Count multiplicities across all vars *)
  let var_counts = count_occurrences all_vars in
  
  (* Build substitution pairs in the order of all_vars *)
  let rec build_pairs vars acc_subst acc_fresh_map =
    match vars with
    | [] -> (acc_subst, acc_fresh_map)
    | v :: rest ->
      let count = match List.assoc_opt v var_counts with
        | Some n -> n
        | None -> 1
      in
      if count = 1 then
        (* Single use: v → v *)
        build_pairs rest (acc_subst @ [(v, v)]) acc_fresh_map
      else
        (* Multiple uses: need contraction *)
        let existing_fresh = match List.assoc_opt v acc_fresh_map with
          | Some fs -> fs
          | None -> []
        in
        (* How many fresh vars do we still need? *)
        let fresh_needed = count - List.length existing_fresh in
        let fresh_vars = if fresh_needed > 0 then
          generate_fresh_vars v fresh_needed
        else [] in
        let all_fresh = existing_fresh @ fresh_vars in
        let acc_fresh_map' = (v, all_fresh) :: List.remove_assoc v acc_fresh_map in
        
        (* Create substitution pairs: v → v, fresh1 → v, fresh2 → v, ... *)
        let subst_entries = (v, v) :: List.map (fun fv -> (fv, v)) all_fresh in
        build_pairs rest (acc_subst @ subst_entries) acc_fresh_map'
  in
  
  let (subst_pairs, _fresh_map') = build_pairs all_vars [] fresh_map in
  (subst_pairs, all_vars)

(** Generate n fresh variables based on a base variable *)
and generate_fresh_vars (_base: Ident.t) (n: int) : Ident.t list =
  List.init n (fun _ -> Ident.fresh ())

(** Main entry point: linearize a Cut program *)
let linearize_program (sigs: CutTypes.signature_defs) (prog: CutT.program) : CutT.program =
  List.map (fun (label, gamma, body) ->
    (* Start with the environment defined by the function signature *)
    let initial_env = List.map fst gamma in
    let body' = linearize_statement sigs prog initial_env body in
    (label, gamma, body')
  ) prog

let linearize_definitions (defs: CutT.definitions) : CutT.definitions =
  { signatures = defs.signatures
  ; program = linearize_program defs.signatures defs.program
  }
