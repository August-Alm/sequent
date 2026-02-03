(**
  Module: Cut.Semantics
  Description: Abstract machine evaluation for Cut programs
  
  Implements the operational semantics described in lib/cut/description.txt
  
  Machine configurations: ⟨s ∥ E ∥ P⟩
  - s: statement under execution
  - E: value environment mapping variables to values
  - P: program (labels to definitions)
*)

open Common.Identifiers
module CutT = Terms
module CutTypes = Types

(** Values in the abstract machine *)
type value =
  | Producer of Path.t * value_env   (* {m; E} - symbol and field environment *)
  | Consumer of value_env * branches (* {E; b} - closure environment and branches *)
  | Literal of int                   (* Machine integers for external types *)

(** Value environment: maps variables to values *)
and value_env = (Ident.t * value) list

(** Branches: map from symbol to statement *)
and branches = (Path.t * CutT.statement) list

(** Machine configuration *)
type config = {
  statement: CutT.statement;
  env: value_env;
  program: CutT.program;  (* List of (label, typ_env, statement) *)
}

(** Pretty-printing *)

let rec value_to_string (v: value) : string =
  match v with
  | Producer (symbol, env) ->
    Printf.sprintf "{%s; %s}" (Path.name symbol) (env_to_string env)
  | Consumer (env, branches) ->
    Printf.sprintf "{%s; %d branches}" (env_to_string env) (List.length branches)
  | Literal n -> string_of_int n

and env_to_string (env: value_env) : string =
  let bindings = List.map (fun (var, value) ->
    Printf.sprintf "%s → %s" (Ident.name var) (value_to_string value)
  ) env in
  String.concat ", " bindings

let config_to_string (config: config) : string =
  Printf.sprintf "⟨stmt ∥ %s⟩" (env_to_string config.env)

(** Exception for runtime errors *)
exception RuntimeError of string

(** Look up a variable in the value environment *)
let rec lookup_var (env: value_env) (v: Ident.t) : value =
  match env with
  | [] -> raise (RuntimeError (Printf.sprintf "Variable not found: %s" (Ident.name v)))
  | (var, value) :: rest ->
      if Ident.equal var v then value
      else lookup_var rest v

(** Look up a label in the program *)
let rec lookup_label (program: CutT.program) (MkLabel label: CutT.label) : (CutT.typ_env * CutT.statement) =
  match program with
  | [] -> raise (RuntimeError (Printf.sprintf "Label not found: %s" (Path.name label)))
  | (MkLabel lbl, gamma, stmt) :: rest ->
      if Path.equal lbl label then (gamma, stmt)
      else lookup_label rest (MkLabel label)

(** Look up a branch by symbol *)
let rec lookup_branch (branches: branches) (symbol: Path.t) : CutT.statement =
  match branches with
  | [] -> raise (RuntimeError (Printf.sprintf "Branch not found: %s" (Path.name symbol)))
  | (sym, stmt) :: rest ->
      if Path.equal sym symbol then stmt
      else lookup_branch rest symbol

(** Split environment into two parts: variables in gamma and the rest *)
let split_env (env: value_env) (gamma: CutT.typ_env) : (value_env * value_env) =
  let gamma_vars = List.map fst gamma in
  let is_in_gamma v = List.exists (fun gv -> Ident.equal v gv) gamma_vars in
  let env_gamma = List.filter (fun (v, _) -> is_in_gamma v) env in
  let env_rest = List.filter (fun (v, _) -> not (is_in_gamma v)) env in
  (env_gamma, env_rest)

(** Single step of evaluation
    Returns None if execution is complete (no more steps)
*)
let step (config: config) : config option =
  match config.statement with
  
  (* (let) ⟨let v = m(Γ0); s ∥ E, E0⟩ → ⟨s ∥ E, v → {m; E0}⟩ where E0 : Γ0 *)
  | CutT.LetPrd (v, symbol, _type_args, gamma, stmt) ->
    let (env_gamma, env_rest) = split_env config.env gamma in
    let new_value = Producer (symbol, env_gamma) in
    Some { config with
      statement = stmt;
      env = (v, new_value) :: env_rest
    }
  
  (* (new) ⟨new v = (Γ0)b; s ∥ E, E0⟩ → ⟨s ∥ E, v → {E0; b}⟩ where E0 : Γ0 *)
  | CutT.NewCns (v, _typ, gamma, branches_list, stmt) ->
    let (env_gamma, env_rest) = split_env config.env gamma in
    (* Convert branches from Cut syntax to runtime branches *)
    let runtime_branches = List.map (fun (symbol, _type_args, _branch_gamma, branch_stmt) ->
      (symbol, branch_stmt)
    ) branches_list in
    let new_value = Consumer (env_gamma, runtime_branches) in
    Some { config with
      statement = stmt;
      env = (v, new_value) :: env_rest
    }
  
  (* (switch) ⟨switch v b ∥ E, v → {m; E0}⟩ → ⟨b(m) ∥ E, E0⟩ *)
  | CutT.SwitchPrd (v, branches_list) ->
    let producer_value = lookup_var config.env v in
    (match producer_value with
    | Producer (symbol, field_env) ->
      (* Convert branches to runtime format *)
      let runtime_branches = List.map (fun (sym, _type_args, _branch_gamma, branch_stmt) ->
        (sym, branch_stmt)
      ) branches_list in
      let branch_stmt = lookup_branch runtime_branches symbol in
      (* Remove binding for v, add field environment *)
      let env_without_v = List.filter (fun (var, _) -> not (Ident.equal var v)) config.env in
      Some { config with
        statement = branch_stmt;
        env = field_env @ env_without_v
      }
    | _ -> raise (RuntimeError (Printf.sprintf "Expected producer value for switch on %s" (Ident.name v))))
  
  (* (invoke) ⟨invoke v m ∥ E, v → {E0; b}⟩ → ⟨b(m) ∥ E, E0⟩ *)
  | CutT.InvokeCns (v, symbol, _type_args, _args) ->
    let consumer_value = lookup_var config.env v in
    (match consumer_value with
    | Consumer (closure_env, branches) ->
      let branch_stmt = lookup_branch branches symbol in
      (* Remove binding for v, add closure environment *)
      let env_without_v = List.filter (fun (var, _) -> not (Ident.equal var v)) config.env in
      Some { config with
        statement = branch_stmt;
        env = closure_env @ env_without_v
      }
    | _ -> raise (RuntimeError (Printf.sprintf "Expected consumer value for invoke on %s" (Ident.name v))))
  
  (* (jump) ⟨jump l[τ̄] ∥ E⟩ → ⟨P(l) ∥ E⟩ *)
  | CutT.Jump (label, _type_args) ->
    let (_gamma, stmt) = lookup_label config.program label in
    Some { config with statement = stmt }
  
  (* (return) ⟨return x to k ∥ E⟩ → ⟨k.apply(x) ∥ E⟩ *)
  | CutT.Return (x, k) ->
    let _x_val = lookup_var config.env x in
    (match lookup_var config.env k with
    | Consumer (_closure_env, _branches) ->
      (* Return is a tail call - for now, just treat as not implemented *)
      (* Full implementation would invoke the continuation with x_val *)
      raise (RuntimeError "Return statement not yet fully implemented in semantics")
    | _ ->
      raise (RuntimeError (Printf.sprintf "Expected consumer value for return to %s" (Ident.name k))))
  
  (* (subst) ⟨substitute [v′1 → v1, ...]; s ∥ E⟩ → ⟨s ∥ v′1 → E(v1), ...⟩ *)
  | CutT.Substitute (subst, stmt) ->
    let new_env = List.map (fun (target, source) ->
      let value = lookup_var config.env source in
      (target, value)
    ) subst in
    Some { config with
      statement = stmt;
      env = new_env
    }
  
  (* (let_cns) ⟨let_cns v = m(Γ0); s ∥ E, E0⟩ → ⟨s ∥ E, v → {E0; b_m}⟩ where E0 : Γ0 *)
  (* Dual of let: creates a consumer instead of a producer *)
  | CutT.LetCns (v, symbol, _type_args, gamma, stmt) ->
    let (env_gamma, env_rest) = split_env config.env gamma in
    (* For letcns, we create a consumer with the method as a singleton branch *)
    let new_value = Consumer (env_gamma, [(symbol, stmt)]) in
    Some { config with
      statement = stmt;
      env = (v, new_value) :: env_rest
    }
  
  (* (new_prd) ⟨new_prd v = (Γ0)b; s ∥ E, E0⟩ → ⟨s ∥ E, v → {m; E0}⟩ where E0 : Γ0 *)
  (* Dual of new: creates a producer instead of a consumer *)
  | CutT.NewPrd (v, _typ, gamma, branches_list, stmt) ->
    let (env_gamma, env_rest) = split_env config.env gamma in
    (* For new_prd, we create a producer - but producers only have one method,
       so we'll use the first branch's symbol *)
    let (first_symbol, _, _, _) = List.hd branches_list in
    let new_value = Producer (first_symbol, env_gamma) in
    Some { config with
      statement = stmt;
      env = (v, new_value) :: env_rest
    }
  
  (* (switch_cns) ⟨switch_cns v b ∥ E, v → {E0; b}⟩ → ⟨b(m) ∥ E, E0⟩ *)
  (* Dual of switch: pattern matching on a consumer *)
  | CutT.SwitchCns (v, branches_list) ->
    let consumer_value = lookup_var config.env v in
    (match consumer_value with
    | Consumer (closure_env, runtime_branches) ->
      (* Find which branch to execute - use the first branch symbol from runtime_branches *)
      let (symbol, _branch_stmt) = List.hd runtime_branches in
      let runtime_branches_converted = List.map (fun (sym, _type_args, _branch_gamma, branch_stmt) ->
        (sym, branch_stmt)
      ) branches_list in
      let branch_stmt = lookup_branch runtime_branches_converted symbol in
      let env_without_v = List.filter (fun (var, _) -> not (Ident.equal var v)) config.env in
      Some { config with
        statement = branch_stmt;
        env = closure_env @ env_without_v
      }
    | _ -> raise (RuntimeError (Printf.sprintf "Expected consumer value for switch_cns on %s" (Ident.name v))))
  
  (* (invoke_prd) ⟨invoke_prd v m ∥ E, v → {m; E0}⟩ → ⟨b(m) ∥ E, E0⟩ *)
  (* Dual of invoke: invoking a method on a producer *)
  | CutT.InvokePrd (v, symbol, _type_args, _args) ->
    let producer_value = lookup_var config.env v in
    (match producer_value with
    | Producer (prod_symbol, field_env) ->
      if not (Path.equal symbol prod_symbol) then
        raise (RuntimeError (Printf.sprintf "InvokePrd: method mismatch - expected %s, got %s"
          (Path.name prod_symbol) (Path.name symbol)));
      let env_without_v = List.filter (fun (var, _) -> not (Ident.equal var v)) config.env in
      (* For invokeprd, we need to look up the implementation - 
         but this is tricky since producers don't have branches in our model.
         For now, treat as identity *)
      Some { config with env = field_env @ env_without_v }
    | _ -> raise (RuntimeError (Printf.sprintf "Expected producer value for invokeprd on %s" (Ident.name v))))
  
  (* (extern) External statements - platform-dependent operations *)
  | CutT.Extern (symbol, args, clauses) ->
    (* For now, implement a few basic external operations *)
    let symbol_name = Path.name symbol in
    (match symbol_name, args, clauses with
    (* (lit) ⟨extern lit n {(v) ⇒ s} ∥ E⟩ → ⟨s ∥ E, v → n⟩ *)
    | (litn, [v], [([], stmt)]) when String.starts_with ~prefix:"lit_" litn  ->
      (match int_of_string_opt (String.sub litn 4 (String.length litn - 4)) with
      | None -> raise (RuntimeError "lit expects integer literal")
      | Some n ->
        Some { config with
          statement = stmt;
          env = (v, Literal n) :: config.env 
        })
    
    (* (add) ⟨extern add(v1, v2) {(v) ⇒ s} ∥ E⟩ → ⟨s ∥ E, v → E(v1) + E(v2)⟩ *)
    | "add", [v1; v2], [([(result_var, _)], stmt)] ->
      let val1 = lookup_var config.env v1 in
      let val2 = lookup_var config.env v2 in
      (match val1, val2 with
      | Literal n1, Literal n2 ->
        Some { config with
          statement = stmt;
          env = (result_var, Literal (n1 + n2)) :: config.env
        }
      | _ -> raise (RuntimeError "add expects integer literals"))
    
    (* (ifz) ⟨extern ifz(v) {() ⇒ s1, () ⇒ s2} ∥ E⟩ → if E(v) = 0 then ⟨s1 ∥ E⟩ else ⟨s2 ∥ E⟩ *)
    | "ifz", [v], [([], then_stmt); ([], else_stmt)] ->
      let value = lookup_var config.env v in
      (match value with
      | Literal 0 -> Some { config with statement = then_stmt }
      | Literal _ -> Some { config with statement = else_stmt }
      | _ -> raise (RuntimeError "ifz expects integer literal"))
    
    (* return_<name> - Print result and terminate *)
    | name, [], [] when String.starts_with ~prefix:"return_" name ->
      let constructor = String.sub name 7 (String.length name - 7) in
      print_endline (Printf.sprintf "Result: %s with environment %s" constructor (env_to_string config.env));
      None  (* Terminate execution *)
    
    | "return", [v], [] ->
      print_endline (value_to_string (lookup_var config.env v));
      None  (* Terminate execution *)
    
    | _ -> raise (RuntimeError (Printf.sprintf "Unknown or malformed extern: %s" symbol_name)))

(** Evaluate a configuration for a maximum number of steps
    Returns the final configuration and number of steps taken
*)
let rec eval_steps (max_steps: int) (config: config) : (config * int) =
  if max_steps <= 0 then
    (config, 0)
  else
    match step config with
    | None -> (config, 0)  (* Execution complete *)
    | Some next_config -> 
      let (final_config, steps) = eval_steps (max_steps - 1) next_config in
      (final_config, steps + 1)

(** Evaluate a program starting from a given label *)
let eval_program ?(max_steps=1000) (program: CutT.program) (start_label: CutT.label) (env: value_env): config =
  let (_gamma, stmt) = lookup_label program start_label in
  (* Initialize environment with unbound variables from gamma - they should be provided *)
  (* For now, start with empty environment *)
  let initial_config = {
    statement = stmt;
    env = env;
    program = program;
  } in
  let (final_config, steps_taken) = eval_steps max_steps initial_config in
  if steps_taken >= max_steps then
    raise (RuntimeError "Maximum steps exceeded - possible infinite loop")
  else
    final_config
