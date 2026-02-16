(**
  module Focused.Semantics
  description: Abstract machine semantics for the focused IR.
*)

open Common.Identifiers
open Common.Types
open Terms

(* ========================================================================= *)
(* Values and Environments                                                   *)
(* ========================================================================= *)

(** Runtime values in the abstract machine *)
type value =
    Producer of xtor * env       (** {m; E} - a constructor with its captured environment *)
  | Consumer of env * branch list (** {E; bs} - branches with their captured environment *)
  | IntVal of int                 (** Literal integers *)

(** Environment maps variables to values *)
and env = value Ident.tbl

(** Configuration: command + environment *)
type config = command * env

let empty_env : env = Ident.emptytbl

(* ========================================================================= *)
(* Environment Operations                                                    *)
(* ========================================================================= *)

let lookup (e: env) (x: var) : value =
  match Ident.find_opt x e with
    Some v -> v
  | None -> failwith ("unbound variable: " ^ Ident.name x)

let lookup_opt (e: env) (x: var) : value option =
  Ident.find_opt x e

let lookup_int (e: env) (x: var) : int =
  match lookup e x with
    IntVal n -> n
  | _ -> failwith ("expected int value for: " ^ Ident.name x)

let lookup_producer (e: env) (x: var) : xtor * env =
  match lookup e x with
    Producer (m, e0) -> (m, e0)
  | _ -> failwith ("expected producer value for: " ^ Ident.name x)

let lookup_consumer (e: env) (x: var) : env * branch list =
  match lookup e x with
    Consumer (e0, bs) -> (e0, bs)
  | _ -> failwith ("expected consumer value for: " ^ Ident.name x)

let extend (e: env) (x: var) (v: value) : env =
  Ident.add x v e

(** Build sub-environment containing only specified variables *)
let sub_env (e: env) (vars: var list) : env =
  List.fold_left (fun acc x -> extend acc x (lookup e x)) empty_env vars

(** Merge two environments (e2 values override e1 on conflicts) *)
let merge_env (e1: env) (e2: env) : env =
  List.fold_left (fun acc (x, v) -> extend acc x v) e1 (Ident.to_list e2)

(* ========================================================================= *)
(* Branch Selection                                                          *)
(* ========================================================================= *)

(** Find the branch matching a given xtor by name *)
let find_branch (x: xtor) (branches: branch list) : branch option =
  List.find_opt (fun ((x': xtor), _, _) -> Path.equal x'.name x.name) branches

(** Find the branch matching a given xtor, or fail *)
let select_branch (x: xtor) (branches: branch list) : branch =
  match find_branch x branches with
    Some b -> b
  | None -> failwith ("no branch for xtor: " ^ Path.name x.name)

(* ========================================================================= *)
(* Pretty Printing                                                           *)
(* ========================================================================= *)

let pp_xtor (x: xtor) : string = Path.name x.name

let pp_value = function
    Producer (m, _) -> "{" ^ pp_xtor m ^ "; ...}"
  | Consumer (_, bs) -> "{...; " ^ string_of_int (List.length bs) ^ " branches}"
  | IntVal n -> string_of_int n

let pp_env (e: env) : string =
  let bindings = Ident.to_list e in
  String.concat ", " (List.map (fun (x, v) -> Ident.name x ^ " → " ^ pp_value v) bindings)

let pp_config ((cmd, e): config) : string =
  let cmd_str = match cmd with
      Let (v, x, _, _) -> "let " ^ Ident.name v ^ " = " ^ pp_xtor x ^ "(...)"
    | Switch (_, v, _) -> "switch " ^ Ident.name v
    | New (_, v, _, _) -> "new " ^ Ident.name v
    | Invoke (v, x, _) -> Ident.name v ^ "." ^ pp_xtor x
    | Axiom (_, v, k) -> "⟨" ^ Ident.name v ^ " | " ^ Ident.name k ^ "⟩"
    | Lit (n, v, _) -> "lit " ^ string_of_int n ^ " → " ^ Ident.name v
    | Add (a, b, v, _) -> Ident.name a ^ " + " ^ Ident.name b ^ " → " ^ Ident.name v
    | Ifz (v, _, _) -> "ifz " ^ Ident.name v
    | End -> "end"
    | Ret (_, v) -> "ret " ^ Ident.name v
  in
  "⟨" ^ cmd_str ^ " ∥ {" ^ pp_env e ^ "}⟩"

(* ========================================================================= *)
(* Single-Step Semantics                                                     *)
(* ========================================================================= *)

(** Single step of the abstract machine. Returns None if stuck or terminal. *)
let step ((cmd, e): config) : config option =
  match cmd with
  (* (let) ⟨let v = m(Γ); s ∥ E⟩ → ⟨s ∥ E, v → {m; E|Γ}⟩ 
     Creates a producer: the xtor m with captured environment for args *)
    Let (v, m, args, body) ->
      let e0 = sub_env e args in
      let e' = extend e v (Producer (m, e0)) in
      Some (body, e')

  (* (new) ⟨new v = {bs}; s ∥ E⟩ → ⟨s ∥ E, v → {E; bs}⟩
     Creates a consumer: captures current env, branches will bind params when invoked *)
  | New (_, v, branches, body) ->
      let e' = extend e v (Consumer (e, branches)) in
      Some (body, e')

  (* (switch) ⟨switch v {bs} ∥ E⟩
     Destructure producer v, select matching branch, bind params *)
  | Switch (_, v, branches) ->
      (match lookup e v with
       | Producer (m, e0) ->
           (* Find the branch matching this constructor *)
           let (_, params, branch_body) = select_branch m branches in
           (* e0 has the captured argument values, bind them to params *)
           (* Note: sub_env builds with fold_left, so to_list is reversed *)
           let e0_list = List.rev (Ident.to_list e0) in
           let e' = List.fold_left2 (fun acc p (_, v) -> extend acc p v) e params e0_list in
           Some (branch_body, e')
       | IntVal n ->
           (* For integers, we need to match against a single-param branch *)
           (* Use the first branch and bind the int to its param *)
           (match branches with
              [] -> failwith "switch on int with no branches"
            | (_, params, branch_body) :: _ ->
                let e' = extend e (List.hd params) (IntVal n) in
                Some (branch_body, e'))
       | Consumer _ as c ->
           (* For a consumer value, this is eta-expansion - bind the consumer to params.
              This represents destructuring a consumer to re-package it. *)
           (match branches with
              [] -> failwith "switch on consumer with no branches"
            | (_, params, branch_body) :: _ ->
                (* Bind the whole consumer to all params (forwarding) *)
                let e' = List.fold_left (fun acc p -> extend acc p c) e params in
                Some (branch_body, e')))

  (* (invoke) ⟨v.m(Γ) ∥ E, v → {E0; bs}⟩ → ⟨b ∥ E0[params↦E(Γ)]⟩
     Invokes a consumer: find matching branch, bind args to params in captured env *)
  | Invoke (v, m, args) ->
      let (e0, branches) = lookup_consumer e v in
      let (_, params, branch_body) = select_branch m branches in
      (* Bind the current values of args to the branch params *)
      let arg_vals = List.map (fun a -> lookup e a) args in
      (* Merge current env with captured env, then add params *)
      let e_merged = merge_env e0 e in
      let e' = List.fold_left2 extend e_merged params arg_vals in
      Some (branch_body, e')

  (* (axiom) ⟨⟨v | k⟩ ∥ E⟩ - interaction between producer and consumer *)
  | Axiom (_, v1, v2) ->
      (match lookup_opt e v2 with
        None ->
          (* v2 is unbound (open term) - stuck *)
          None
      | Some (Consumer (e0, branches)) ->
          (match lookup e v1 with
           | IntVal n ->
               (* Int value passed to continuation *)
               (* For a simple continuation, use first branch and bind int to its param *)
               (match branches with
                  [] -> failwith "axiom: consumer with no branches"
                | (_, params, branch_body) :: _ ->
                    let e' = extend e0 (List.hd params) (IntVal n) in
                    Some (branch_body, e'))
           | Producer (m, e1) ->
               (* Producer passed to consumer - find matching branch *)
               let (_, params, branch_body) = select_branch m branches in
               (* Bind producer's captured values to params *)
               let e1_list = List.rev (Ident.to_list e1) in
               let e' = List.fold_left2 (fun acc p (_, v) -> extend acc p v) e0 params e1_list in
               Some (branch_body, e')
           | Consumer _ ->
               failwith "axiom: expected producer or int on the left, got consumer")
      | Some _ ->
          failwith "axiom: expected consumer on the right")

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

  (* (ifz) ⟨ifz v {s1} {s2} ∥ E⟩ → if E(v) = 0 then ⟨s1 ∥ E⟩ else ⟨s2 ∥ E⟩ *)
  | Ifz (v, then_cmd, else_cmd) ->
      let n = lookup_int e v in
      if n = 0 then Some (then_cmd, e)
      else Some (else_cmd, e)

  | End -> None

  | Ret _ -> None

(* ========================================================================= *)
(* Machine Runners                                                           *)
(* ========================================================================= *)

(** Check if machine terminated with a result *)
let get_result ((cmd, e): config) : value option =
  match cmd with
    Ret (_, v) -> Some (lookup e v)
  | Axiom (_, v1, v2) when lookup_opt e v2 = None ->
      Some (lookup e v1)
  | _ -> None

(** Check if machine is stuck on an open term (axiom with unbound continuation) *)
let is_open_result ((cmd, e): config) : (var * value) option =
  match cmd with
    Axiom (_, v1, v2) when lookup_opt e v2 = None ->
      Some (v2, lookup e v1)
  | _ -> None

(** Short name for a command (for tracing) *)
let cmd_name = function
    Let (v, x, _, _) -> "let " ^ Ident.name v ^ " = " ^ pp_xtor x
  | New (_, v, _, _) -> "new " ^ Ident.name v
  | Switch (_, v, _) -> "switch " ^ Ident.name v
  | Invoke (v, x, _) -> Ident.name v ^ "." ^ pp_xtor x
  | Axiom (_, v, k) -> "axiom(" ^ Ident.name v ^ ", " ^ Ident.name k ^ ")"
  | Lit (n, v, _) -> "lit " ^ string_of_int n ^ " → " ^ Ident.name v
  | Add (a, b, v, _) -> Ident.name a ^ " + " ^ Ident.name b ^ " → " ^ Ident.name v
  | Ifz (v, _, _) -> "ifz " ^ Ident.name v
  | End -> "end"
  | Ret (_, v) -> "ret " ^ Ident.name v

(** Run the machine until it stops. Returns (final_config, step_count) *)
let rec run ?(trace=false) ?(steps=0) (cfg: config) : config * int =
  let (cmd, e) = cfg in
  if trace then 
    Printf.printf "    [%d] %s | env has %d bindings\n"
      steps (cmd_name cmd) (List.length (Ident.to_list e));
  match step cfg with
    None -> (cfg, steps)
  | Some cfg' -> run ~trace ~steps:(steps + 1) cfg'

(** Run with tracing, returning all intermediate configurations *)
let rec run_trace (cfg: config) : config list =
  cfg :: (match step cfg with
            None -> []
          | Some cfg' -> run_trace cfg')

(** Initialize and run a command. Returns (final_config, step_count) *)
let eval ?(trace=false) (cmd: command) : config * int =
  run ~trace (cmd, empty_env)

(** Initialize and run with trace *)
let eval_trace (cmd: command) : config list =
  run_trace (cmd, empty_env)