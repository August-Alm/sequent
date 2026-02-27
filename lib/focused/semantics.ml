(**
  module Focused.Semantics
  description: Abstract machine semantics for the focused IR.
*)

open Common.Identifiers
open Terms

(* ========================================================================= *)
(* Values and Environments                                                   *)
(* ========================================================================= *)

(** Runtime values in the abstract machine *)
type value =
  | DataVal of sym * env            (** {m; E} - constructor m with captured environment *)
  | CodataVal of env * branch list  (** {E; bs} - branches with captured environment *)
  | ReturnVal of env * var * command        (** {E; x ⇒ s} - return continuation *)
  | IntVal of int                           (** Literal integers *)

(** Environment maps variables to values *)
and env =
  { values: value Ident.tbl
  ; defs: Terms.definition Path.tbl  (* Needed for jump semantics *)
  }

(** Configuration: command + environment *)
type config = command * env

let empty_env : env = { values = Ident.emptytbl; defs = Path.emptytbl }

(* ========================================================================= *)
(* Environment Operations                                                    *)
(* ========================================================================= *)

let lookup (e: env) (x: var) : value =
  match Ident.find_opt x e.values with
    Some v -> v
  | None -> failwith ("unbound variable: " ^ Ident.name x)

let lookup_opt (e: env) (x: var) : value option =
  Ident.find_opt x e.values

let lookup_int (e: env) (x: var) : int =
  match lookup e x with
    IntVal n -> n
  | _ -> failwith ("expected int value for: " ^ Ident.name x)

let extend (e: env) (x: var) (v: value) : env =
  { e with values = Ident.add x v e.values }

(** Build sub-environment containing only specified variables *)
let sub_env (e: env) (vars: var list) : env =
  List.fold_left (fun acc x -> extend acc x (lookup e x)) empty_env vars

(** Merge two environments (e2 values override e1 on conflicts) *)
let merge_env (e1: env) (e2: env) : env =
  List.fold_left (fun acc (x, v) -> extend acc x v) e1 (Ident.to_list e2.values)

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
  | DataVal (m, _) -> "{" ^ pp_sym m ^ "; ...}"
  | CodataVal (_, bs) -> "{...; " ^ string_of_int (List.length bs) ^ " branches}"
  | ReturnVal _ -> "{return; ...}"
  | IntVal n -> string_of_int n

let pp_env (e: env) : string =
  let bindings = Ident.to_list e.values in
  String.concat ", " (List.map (fun (x, v) -> Ident.name x ^ " → " ^ pp_value v) bindings)

let rec pp_config ((cmd, e): config) : string =
  let cmd_str = cmd_name cmd in
  "⟨" ^ cmd_str ^ " ∥ {" ^ pp_env e ^ "}⟩"

and cmd_name = function
  | Let (v, _, x, _, _) -> "let " ^ Ident.name v ^ " = " ^ pp_sym x ^ "(...)"
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
  | End -> "end"
  | Ret (_, v) -> "ret " ^ Ident.name v

(* ========================================================================= *)
(* Single-Step Semantics                                                     *)
(* ========================================================================= *)

(** Single step of the abstract machine. Returns None if stuck or terminal. *)
let step ((cmd, e): config) : config option =
  match cmd with
  (* (let) ⟨let v = m(args); s ∥ E⟩ → ⟨s ∥ E, v → {m; E|args}⟩ 
     Constructs a data value with the xtor name and captured args *)
  | Let (v, _, m, args, body) ->
      let e0 = sub_env e args in
      let e' = extend e v (DataVal (m, e0)) in
      Some (body, e')

  (* (new) ⟨new v = {bs}; s ∥ E⟩ → ⟨s ∥ E, v → {E; bs}⟩
     Creates a codata value: captures current env, branches bind params when invoked *)
  | New (v, _, branches, body) ->
      let e' = extend e v (CodataVal (e, branches)) in
      Some (body, e')

  (* (switch) ⟨switch v {bs} ∥ E⟩
     Destructure data value v, select matching branch, bind params *)
  | Switch (v, _, branches) ->
      (match lookup e v with
       | DataVal (m, e0) ->
           let (_, _, params, branch_body) = select_branch m branches in
           let e0_list = List.rev (Ident.to_list e0.values) in
           let e' = List.fold_left2 (fun acc p (_, val0) -> extend acc p val0) e params e0_list in
           Some (branch_body, e')
       | IntVal n ->
           (match branches with
              [] -> failwith "switch on int with no branches"
            | (_, _, params, branch_body) :: _ ->
                let e' = extend e (List.hd params) (IntVal n) in
                Some (branch_body, e'))
       | _ -> failwith "switch: expected data value")

  (* (invoke) ⟨v.m(args) ∥ E, v → {E0; bs}⟩ → ⟨b ∥ E0[params↦E(args)]⟩
     Invokes a codata value: find matching branch, bind args to params.
     Body runs in the CAPTURED env extended with args, not merged with current. *)
  | Invoke (v, _, m, args) ->
      (match lookup e v with
       | CodataVal (e0, branches) ->
           let (_, _, params, branch_body) = select_branch m branches in
           let arg_vals = List.map (fun a -> lookup e a) args in
           (* Use captured e0 extended with args, don't merge current env *)
           let e' = List.fold_left2 extend { e0 with defs = e.defs } params arg_vals in
           Some (branch_body, e')
       | _ -> failwith "invoke: expected codata value")

  (* (axiom) ⟨⟨v | k⟩ ∥ E⟩ - interaction between data and codata *)
  | Axiom (_, v1, v2) ->
      (match lookup_opt e v2 with
       | None -> None  (* Open term - stuck *)
       | Some (CodataVal (e0, branches)) ->
           (match lookup e v1 with
            | IntVal n ->
                (match branches with
                   [] -> failwith "axiom: consumer with no branches"
                 | (_, _, params, branch_body) :: _ ->
                     let e' = extend e0 (List.hd params) (IntVal n) in
                     Some (branch_body, e'))
            | DataVal (m, e1) ->
                let (_, _, params, branch_body) = select_branch m branches in
                let e1_list = List.rev (Ident.to_list e1.values) in
                let e' = List.fold_left2 (fun acc p (_, val0) -> extend acc p val0) e0 params e1_list in
                Some (branch_body, e')
            | _ -> failwith "axiom: expected data or int on the left")
       | Some (ReturnVal (e0, px, s)) ->
           (match lookup e v1 with
            | DataVal (_, e1) ->
                let e1_list = List.rev (Ident.to_list e1.values) in
                (match e1_list with
                 | [(_, v0)] ->
                     let e' = extend { e0 with defs = e.defs } px v0 in
                     Some (s, e')
                 | _ -> failwith "axiom: return expected 1 arg")
            | _ -> failwith "axiom: expected data on the left for return")
       | Some _ -> failwith "axiom: expected codata value on the right")

  (* =========== Primitives =========== *)

  (* (lit) ⟨lit n { v ⇒ s } ∥ E⟩ → ⟨s ∥ E, v → n⟩ *)
  | Lit (n, v, body) ->
      let e' = extend e v (IntVal n) in
      Some (body, e')

  (* (add) ⟨add(v1, v2) { v ⇒ s } ∥ E⟩ → ⟨s ∥ E, v → E(v1) + E(v2)⟩ *)
  | Add (v1, v2, v, body) ->
      (match (lookup_opt e v1, lookup_opt e v2) with
       | (Some (IntVal n1), Some (IntVal n2)) ->
           let e' = extend e v (IntVal (n1 + n2)) in
           Some (body, e')
       | (Some val1, Some val2) ->
           failwith (Printf.sprintf "add: expected ints, got %s=%s, %s=%s"
             (Ident.name v1) (pp_value val1) (Ident.name v2) (pp_value val2))
       | (None, _) -> failwith ("add: unbound " ^ Ident.name v1)
       | (_, None) -> failwith ("add: unbound " ^ Ident.name v2))

  (* (sub) ⟨sub(v1, v2) { v ⇒ s } ∥ E⟩ → ⟨s ∥ E, v → E(v1) - E(v2)⟩ *)
  | Sub (v1, v2, v, body) ->
      (match (lookup_opt e v1, lookup_opt e v2) with
       | (Some (IntVal n1), Some (IntVal n2)) ->
           let e' = extend e v (IntVal (n1 - n2)) in
           Some (body, e')
       | (Some val1, Some val2) ->
           failwith (Printf.sprintf "sub: expected ints, got %s=%s, %s=%s"
             (Ident.name v1) (pp_value val1) (Ident.name v2) (pp_value val2))
       | (None, _) -> failwith ("sub: unbound " ^ Ident.name v1)
       | (_, None) -> failwith ("sub: unbound " ^ Ident.name v2))

  (* (newint) ⟨new k = { v ⇒ s1 }; s2 ∥ E⟩ → ⟨s2 ∥ E, k → intcns(E, v, s1)⟩ *)
  | NewInt (k, v, branch_body, cont) ->
      (* Create an Int consumer closure: when k receives an int n, bind v=n and run branch_body *)
      let e' = extend e k (CodataVal (e, [(Path.of_primitive 0 "int", [], [v], branch_body)])) in
      Some (cont, e')

  (* (ifz) ⟨ifz v {s1} {s2} ∥ E⟩ → if E(v) = 0 then ⟨s1 ∥ E⟩ else ⟨s2 ∥ E⟩ *)
  | Ifz (v, then_cmd, else_cmd) ->
      let n = lookup_int e v in
      if n = 0 then Some (then_cmd, e)
      else Some (else_cmd, e)

  (* (jump) ⟨jump l(args) ∥ E⟩ → ⟨body ∥ E'⟩ where E' binds params to E(args) 
     Look up definition l, bind its parameters to the argument values *)
  | Jump (label, args) ->
      (match Path.find_opt label e.defs with
      | None -> failwith ("undefined label: " ^ Path.name label)
      | Some def ->
          (* Build new environment binding params to arg values.
             For each arg, try to look it up. If unbound, it's a continuation
             variable that we track specially. *)
          let param_names = List.map fst def.term_params in
          let e' = List.fold_left2 
            (fun acc param_name arg_val -> extend acc param_name arg_val)
            { e with values = Ident.emptytbl }  (* Start fresh but keep defs *)
            param_names (List.map (lookup e) args)
          in
          Some (def.body, e'))

  (* =========== Terminals =========== *)
  | End -> None
  | Ret _ -> None

(* ========================================================================= *)
(* Machine Runners                                                           *)
(* ========================================================================= *)

(** Check if machine terminated with a result *)
let get_result ((cmd, e): config) : value option =
  match cmd with
  | Ret (_, v) -> Some (lookup e v)
  | Axiom (_, v1, v2) when lookup_opt e v2 = None ->
      Some (lookup e v1)
  | _ -> None

(** Check if machine is stuck on an open term (axiom with unbound continuation) *)
let is_open_result ((cmd, e): config) : (var * value) option =
  match cmd with
  | Axiom (_, v1, v2) when lookup_opt e v2 = None ->
      Some (v2, lookup e v1)
  | _ -> None

(** Run the machine until it stops. Returns (final_config, step_count) *)
let rec run ?(trace=false) ?(steps=0) ?(max_steps=500) (cfg: config) : config * int =
  if steps > max_steps then
    failwith (Printf.sprintf "[LOOP] Machine exceeded %d steps" max_steps);
  let (cmd, e) = cfg in
  if trace then begin
    Printf.printf "    [%d] %s | env has %d bindings"
      steps (cmd_name cmd) (List.length (Ident.to_list e.values));
    (* Extra info for ifz and arithmetic *)
    (match cmd with
    | Ifz (v, _, _) -> 
        (try Printf.printf " [ifz val = %d]" (lookup_int e v)
         with _ -> Printf.printf " [ifz val = ?]")
    | Add (a, b, _, _) ->
        (try Printf.printf " [%d + %d]" (lookup_int e a) (lookup_int e b)
         with _ -> Printf.printf " [? + ?]")
    | Axiom (_, v, _) ->
        (try Printf.printf " [val = %d]" (lookup_int e v)
         with _ -> ())
    | _ -> ());
    Printf.printf "\n"
  end;
  match step cfg with
  | None -> (cfg, steps)
  | Some cfg' -> run ~trace ~steps:(steps + 1) ~max_steps cfg'

(** Run with tracing, returning all intermediate configurations *)
let rec run_trace (cfg: config) : config list =
  cfg :: (match step cfg with
          | None -> []
          | Some cfg' -> run_trace cfg')

(** Initialize and run a command. Returns (final_config, step_count) *)
let eval ?(trace=false) (cmd: command) : config * int =
  run ~trace (cmd, empty_env)

(** Initialize and run with trace *)
let eval_trace (cmd: command) : config list =
  run_trace (cmd, empty_env)