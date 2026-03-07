(**
  module Axil.Semantics
  description: Abstract machine semantics for Axil.

  Values V ::=
              {m; E}        producers
            | {E; b}        consumers
            | 0 | 1 | ...   literals of external types (e.g. ext Int)
            | {E; x ⇒ s}     return continuations

  Environments E ::= x → V, ...
    The environment is a LIST (not a set). The head of the list is the
    "top of the stack" - the most recently bound variables.

  Configurations M ::= ⟨s ∥ E ∥ P⟩

  Selected step rules:

    (let)     ⟨let v = m(Γ0); s ∥ E, E0⟩ → ⟨s ∥ E, v → {m; E0}⟩ where E0 : Γ0
    (new)     ⟨new v = (Γ0)b; s ∥ E, E0⟩ → ⟨s ∥ E, v → {E0; b}⟩ where E0 : Γ0
    (switch)  ⟨switch v b ∥ E, v → {m; E0}⟩ → ⟨b(m) ∥ E, E0⟩
    (invoke)  ⟨invoke v m ∥ E, v → {E0; b}⟩ → ⟨b(m) ∥ E, E0⟩
    (jump)    ⟨jump l ∥ E⟩ → ⟨P(l) ∥ E⟩
    (subst)   ⟨substitute [v′1 → v1, ...]; s ∥ E⟩ → ⟨s ∥ v′1 → E(v1), ...⟩
    (lit)     ⟨lit n {(v) ⇒ s} ∥ E⟩ → ⟨s ∥ E, v → n⟩
    (add)     ⟨add(v1, v2) {(v) ⇒ s} ∥ E⟩ → ⟨s ∥ E, v → E(v1) + E(v2)⟩
*)

open Common.Identifiers
open Terms

(* ========================================================================= *)
(* Values and Environments                                                   *)
(* ========================================================================= *)

(** Runtime values in the abstract machine *)
type value =
    DataVal of sym * linear_env   (** {m; E} - constructor m with captured environment *)
  | CodataVal of linear_env * branch list  (** {E; bs} - branches with captured environment *)
  | ReturnVal of linear_env * var * command  (** {E; x ⇒ s} - return continuation *)
  | IntVal of int                           (** Literal integers *)

(** Linear environment: ordered list of bindings, head = top of stack *)
and linear_env = (var * value) list

(** Full environment includes the program definitions for jump *)
type env =
  { values: linear_env
  ; defs: Terms.definition Path.tbl
  }

(** Configuration: command + environment *)
type config = command * env

let empty_env : env = { values = []; defs = Path.emptytbl }

(* ========================================================================= *)
(* Environment Operations                                                    *)
(* ========================================================================= *)

(** Lookup a variable anywhere in the linear environment (for unrestricted use) *)
let lookup (e: linear_env) (x: var) : value =
  match List.assoc_opt x e with
    Some v -> v
  | None -> failwith ("unbound variable: " ^ Ident.name x)

let lookup_opt (e: linear_env) (x: var) : value option =
  List.assoc_opt x e

let lookup_int (e: linear_env) (x: var) : int =
  match lookup e x with
    IntVal n -> n
  | _ -> failwith ("expected int value for: " ^ Ident.name x)

(** Push a new binding at the head (top of stack) *)
let push (e: linear_env) (x: var) (v: value) : linear_env =
  (x, v) :: e

(** Pop n bindings from the head, returns (popped, remaining) *)
let pop (n: int) (e: linear_env) : linear_env * linear_env =
  let rec aux n acc e =
    if n <= 0 then (List.rev acc, e)
    else match e with
        [] -> failwith "pop: not enough bindings"
      | (x, v) :: rest -> aux (n - 1) ((x, v) :: acc) rest
  in
  aux n [] e

(** Pop the head binding, returns (binding, remaining) *)
let pop_head (e: linear_env) : (var * value) * linear_env =
  match e with
    [] -> failwith "pop_head: empty environment"
  | hd :: tl -> (hd, tl)

(** Prepend env2 in front of env1: env2 @ env1 *)
let prepend (env2: linear_env) (env1: linear_env) : linear_env =
  env2 @ env1

(* ========================================================================= *)
(* Branch Selection                                                          *)
(* ========================================================================= *)

(** Find the branch matching a given xtor name *)
let find_branch (x: sym) (branches: branch list) : branch option =
  List.find_opt (fun (x', _, _, _) -> Path.equal x' x) branches

(** Find the branch matching a given xtor, or fail *)
let select_branch (x: sym) (branches: branch list) : branch =
  match find_branch x branches with
    Some b -> b
  | None -> failwith ("no branch for xtor: " ^ Path.name x)

(* ========================================================================= *)
(* Pretty Printing                                                           *)
(* ========================================================================= *)

let pp_sym (x: sym) : string = Path.name x

let pp_value = function
    DataVal (m, _) -> "{" ^ pp_sym m ^ "; ...}"
  | CodataVal (_, bs) -> "{...; " ^ string_of_int (List.length bs) ^ " branches}"
  | ReturnVal _ -> "{return; ...}"
  | IntVal n -> string_of_int n

let pp_linear_env (e: linear_env) : string =
  String.concat ", " (List.map (fun (x, v) -> Ident.name x ^ " → " ^ pp_value v) e)

let rec pp_config ((cmd, e): config) : string =
  let cmd_str = cmd_name cmd in
  "⟨" ^ cmd_str ^ " ∥ [" ^ pp_linear_env e.values ^ "]⟩"

and cmd_name = function
    Let (v, _, x, _, _) -> "let " ^ Ident.name v ^ " = " ^ pp_sym x ^ "(...)"
  | Switch (v, _, _) -> "switch " ^ Ident.name v
  | New (v, _, _, _) -> "new " ^ Ident.name v
  | NewInt (k, _, _, _) -> "new " ^ Ident.name k ^ " {int...}"
  | Invoke (v, _, x, _) -> Ident.name v ^ "." ^ pp_sym x
  | Axiom (_, v, k) -> "⟨" ^ Ident.name v ^ " | " ^ Ident.name k ^ "⟩"
  | Lit (n, v, _) -> "lit " ^ string_of_int n ^ " → " ^ Ident.name v
  | Add (a, b, v, _) -> Ident.name a ^ " + " ^ Ident.name b ^ " → " ^ Ident.name v
  | Sub (a, b, v, _) -> Ident.name a ^ " - " ^ Ident.name b ^ " → " ^ Ident.name v
  | Ifz (v, _, _) -> "ifz " ^ Ident.name v
  | Jump (label, _) -> "jump " ^ pp_sym label
  | Substitute (subst, _) -> 
      "subst [" ^ String.concat ", " 
        (List.map (fun (v', v) -> Ident.name v' ^ " ← " ^ Ident.name v) subst) ^ "]"
  | End -> "end"
  | Ret (_, v) -> "ret " ^ Ident.name v

(* ========================================================================= *)
(* Single-Step Semantics                                                     *)
(* ========================================================================= *)

(** Single step of the abstract machine. Returns None if stuck or terminal. *)
let step ((cmd, e): config) : config option =
  match cmd with
  (* (subst) ⟨substitute [v′1 ← v1, ...]; s ∥ E⟩ → ⟨s ∥ v′1 → E(v1), ...⟩
     Build new environment from substitution, looking up each source var in E *)
    Substitute (subst, body) ->
      let new_values = List.map (fun (v', v) -> (v', lookup e.values v)) subst in
      Some (body, { e with values = new_values })

  (* (let) ⟨let v = m(args); s ∥ E, E0⟩ → ⟨s ∥ E, v → {m; E0}⟩
     The first |args| bindings are E0 (consumed/captured), rest is E.
     Result: v bound at head, then tail E *)
  | Let (v, _, m, args, body) ->
      let n_args = List.length args in
      let (e0, e_tail) = pop n_args e.values in
      let data_val = DataVal (m, e0) in
      Some (body, { e with values = push e_tail v data_val })

  (* (new) ⟨new v = {bs}; s ∥ E, E0⟩ → ⟨s ∥ E, v → {E0; bs}⟩
     For codata, the branches capture the current environment.
     NOTE: Unlike data, codata doesn't consume a prefix - it captures all visible vars *)
  | New (v, _, branches, body) ->
      let codata_val = CodataVal (e.values, branches) in
      Some (body, { e with values = push e.values v codata_val })

  (* (switch) ⟨switch v b ∥ E, v → {m; E0}⟩ → ⟨b(m) ∥ E, E0⟩
     v must be at head. Pop it, select branch, push captured E0 then branch params *)
  | Switch (v, _, branches) ->
      let ((head_var, head_val), e_tail) = pop_head e.values in
      if not (Ident.equal head_var v) then
        failwith (Printf.sprintf "switch: expected %s at head, got %s" 
          (Ident.name v) (Ident.name head_var));
      (match head_val with
        DataVal (m, e0) ->
          let (_, _, params, branch_body) = select_branch m branches in
          (* Bind branch params to values from captured e0 *)
          let param_bindings = List.combine params (List.map snd e0) in
          (* New env: params at head, then pushed e0 bindings, then E *)
          let new_values = prepend param_bindings e_tail in
          Some (branch_body, { e with values = new_values })
      | IntVal n ->
          (match branches with
            [] -> failwith "switch on int with no branches"
          | (_, _, params, branch_body) :: _ ->
              let new_values = push e_tail (List.hd params) (IntVal n) in
              Some (branch_body, { e with values = new_values }))
      | _ -> failwith "switch: expected data value at head")

  (* (invoke) ⟨invoke v m(args) ∥ [v, args..., E]⟩ → ⟨b(m) ∥ E0, params⟩
     Following Idris pattern: v at head, then args. Pop v first, then args. *)
  | Invoke (v, _, m, args) ->
      (* First, pop v from the head *)
      let ((head_var, head_val), e_after_v) = pop_head e.values in
      if not (Ident.equal head_var v) then
        failwith (Printf.sprintf "invoke: expected %s at head, got %s" 
          (Ident.name v) (Ident.name head_var));
      (* Now pop arg values *)
      let (arg_bindings, e_tail) = pop (List.length args) e_after_v in
      let _ = e_tail in  (* remaining context, not used *)
      let arg_vals = List.map snd arg_bindings in
      (match head_val with
        CodataVal (e0, branches) ->
          let (_, _, params, branch_body) = select_branch m branches in
          (* Bind params to arg values *)
          let param_bindings = List.combine params arg_vals in
          (* New env: captured e0 at head, params at tail (Idris pattern) *)
          let new_values = e0 @ param_bindings in
          Some (branch_body, { e with values = new_values })
      | _ -> failwith "invoke: expected codata value at head")

  (* (axiom) ⟨⟨v | k⟩ ∥ E⟩ - interaction between data and codata *)
  | Axiom (_, v1, v2) ->
      (match lookup_opt e.values v2 with
        None -> None  (* Open term - stuck *)
      | Some (CodataVal (e0, branches)) ->
          (match lookup e.values v1 with
            IntVal n ->
              (match branches with
                [] -> failwith "axiom: consumer with no branches"
              | (_, _, params, branch_body) :: _ ->
                  let new_values = push e0 (List.hd params) (IntVal n) in
                  Some (branch_body, { e with values = new_values }))
          | DataVal (m, e1) ->
              let (_, _, params, branch_body) = select_branch m branches in
              let param_bindings = List.combine params (List.map snd e1) in
              let new_values = prepend param_bindings e0 in
              Some (branch_body, { e with values = new_values })
          | _ -> failwith "axiom: expected data or int on the left")
      | Some (ReturnVal (e0, px, s)) ->
          (match lookup e.values v1 with
            DataVal (_, e1) ->
              (match e1 with
                [(_, v0)] ->
                  let new_values = push e0 px v0 in
                  Some (s, { e with values = new_values })
              | _ -> failwith "axiom: return expected 1 arg")
          | _ -> failwith "axiom: expected data on the left for return")
      | Some _ -> failwith "axiom: expected codata value on the right")

  (* =========== Primitives (unrestricted - don't consume from head) =========== *)

  (* (lit) ⟨lit n { v ⇒ s } ∥ E⟩ → ⟨s ∥ E, v → n⟩ *)
  | Lit (n, v, body) ->
      let new_values = push e.values v (IntVal n) in
      Some (body, { e with values = new_values })

  (* (add) ⟨add(v1, v2) { v ⇒ s } ∥ E⟩ → ⟨s ∥ E, v → E(v1) + E(v2)⟩ *)
  | Add (v1, v2, v, body) ->
      (match (lookup_opt e.values v1, lookup_opt e.values v2) with
        (Some (IntVal n1), Some (IntVal n2)) ->
          let new_values = push e.values v (IntVal (n1 + n2)) in
          Some (body, { e with values = new_values })
      | (Some val1, Some val2) ->
          failwith (Printf.sprintf "add: expected ints, got %s=%s, %s=%s"
            (Ident.name v1) (pp_value val1) (Ident.name v2) (pp_value val2))
      | (None, _) -> failwith ("add: unbound " ^ Ident.name v1)
      | (_, None) -> failwith ("add: unbound " ^ Ident.name v2))

  (* (sub) ⟨sub(v1, v2) { v ⇒ s } ∥ E⟩ → ⟨s ∥ E, v → E(v1) - E(v2)⟩ *)
  | Sub (v1, v2, v, body) ->
      (match (lookup_opt e.values v1, lookup_opt e.values v2) with
        (Some (IntVal n1), Some (IntVal n2)) ->
          let new_values = push e.values v (IntVal (n1 - n2)) in
          Some (body, { e with values = new_values })
      | (Some val1, Some val2) ->
          failwith (Printf.sprintf "sub: expected ints, got %s=%s, %s=%s"
            (Ident.name v1) (pp_value val1) (Ident.name v2) (pp_value val2))
      | (None, _) -> failwith ("sub: unbound " ^ Ident.name v1)
      | (_, None) -> failwith ("sub: unbound " ^ Ident.name v2))

  (* (newint) ⟨new k = { v ⇒ s1 }; s2 ∥ E⟩ → ⟨s2 ∥ E, k → intcns(E, v, s1)⟩ *)
  | NewInt (k, v, branch_body, cont) ->
      let codata_val = CodataVal (e.values, [(Path.of_primitive 0 "int", [], [v], branch_body)]) in
      let new_values = push e.values k codata_val in
      Some (cont, { e with values = new_values })

  (* (ifz) ⟨ifz v {s1} {s2} ∥ E⟩ → if E(v) = 0 then ⟨s1 ∥ E⟩ else ⟨s2 ∥ E⟩ *)
  | Ifz (v, then_cmd, else_cmd) ->
      let n = lookup_int e.values v in
      if n = 0 then Some (then_cmd, e)
      else Some (else_cmd, e)

  (* (jump) ⟨jump l(args) ∥ E⟩ → ⟨body ∥ E'⟩ 
     Build new env binding definition params to lookedup arg values *)
  | Jump (label, args) ->
      (match Path.find_opt label e.defs with
        None -> failwith ("undefined label: " ^ Path.name label)
      | Some def ->
          let param_names = List.map fst def.term_params in
          let arg_vals = List.map (lookup e.values) args in
          let new_values = List.combine param_names arg_vals in
          Some (def.body, { e with values = new_values }))

  (* =========== Terminals =========== *)
  | End -> None
  | Ret _ -> None

(* ========================================================================= *)
(* Machine Runners                                                           *)
(* ========================================================================= *)

(** Check if machine terminated with a result *)
let get_result ((cmd, e): config) : value option =
  match cmd with
    Ret (_, v) -> Some (lookup e.values v)
  | Axiom (_, v1, v2) when lookup_opt e.values v2 = None ->
      Some (lookup e.values v1)
  | _ -> None

(** Check if machine is stuck on an open term (axiom with unbound continuation) *)
let is_open_result ((cmd, e): config) : (var * value) option =
  match cmd with
    Axiom (_, v1, v2) when lookup_opt e.values v2 = None ->
      Some (v2, lookup e.values v1)
  | _ -> None

(** Run the machine until it stops. Returns (final_config, step_count) *)
let rec run ?(trace=false) ?(steps=0) ?(max_steps=500) (cfg: config) : config * int =
  if steps > max_steps then
    failwith (Printf.sprintf "[LOOP] Machine exceeded %d steps" max_steps);
  let (cmd, e) = cfg in
  if trace then begin
    Printf.printf "    [%d] %s | env has %d bindings"
      steps (cmd_name cmd) (List.length e.values);
    (* Extra info for ifz and arithmetic *)
    (match cmd with
      Ifz (v, _, _) -> 
        (try Printf.printf " [ifz val = %d]" (lookup_int e.values v)
         with _ -> Printf.printf " [ifz val = ?]")
    | Add (a, b, _, _) ->
        (try Printf.printf " [%d + %d]" (lookup_int e.values a) (lookup_int e.values b)
         with _ -> Printf.printf " [? + ?]")
    | Axiom (_, v, _) ->
        (try Printf.printf " [val = %d]" (lookup_int e.values v)
         with _ -> ())
    | _ -> ());
    Printf.printf "\n"
  end;
  match step cfg with
    None -> (cfg, steps)
  | Some cfg' -> run ~trace ~steps:(steps + 1) ~max_steps cfg'

(** Run with tracing, returning all intermediate configurations *)
let rec run_trace (cfg: config) : config list =
  cfg :: (match step cfg with None -> [] | Some cfg' -> run_trace cfg')

(** Initialize and run a command. Returns (final_config, step_count) *)
let eval ?(trace=false) (cmd: command) : config * int =
  run ~trace (cmd, empty_env)

(** Initialize and run with trace *)
let eval_trace (cmd: command) : config list =
  run_trace (cmd, empty_env)