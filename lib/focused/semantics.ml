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
  | DataVal of sym * env          (** {m; E} - constructor m with captured environment *)
  | CodataVal of env * branch list(** {E; bs} - branches with captured environment *)
  | FunVal of env * var * var * command     (** {E; x, y ⇒ s} - function value *)
  | ForallVal of env * var * command        (** {E; a ⇒ s} - polymorphic value *)
  | ThunkVal of env * var * command         (** {E; x ⇒ s} - thunk value *)
  | ReturnVal of env * var * command        (** {E; x ⇒ s} - return continuation *)
  | IntVal of int                           (** Literal integers *)

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
  | FunVal _ -> "{fun; ...}"
  | ForallVal _ -> "{forall; ...}"
  | ThunkVal _ -> "{thunk; ...}"
  | ReturnVal _ -> "{return; ...}"
  | IntVal n -> string_of_int n

let pp_env (e: env) : string =
  let bindings = Ident.to_list e in
  String.concat ", " (List.map (fun (x, v) -> Ident.name x ^ " → " ^ pp_value v) bindings)

let rec pp_config ((cmd, e): config) : string =
  let cmd_str = cmd_name cmd in
  "⟨" ^ cmd_str ^ " ∥ {" ^ pp_env e ^ "}⟩"

and cmd_name = function
  | Let (v, _, x, _, _) -> "let " ^ Ident.name v ^ " = " ^ pp_sym x ^ "(...)"
  | LetInstantiate (v, _, _, _, _) -> "let " ^ Ident.name v ^ " = instantiate[...]"
  | Switch (v, _, _) -> "switch " ^ Ident.name v
  | SwitchForall (v, _, _, _) -> "switch " ^ Ident.name v ^ " {instantiate...}"
  | New (v, _, _, _) -> "new " ^ Ident.name v
  | NewForall (v, _, _, _, _) -> "new " ^ Ident.name v ^ " {instantiate...}"
  | NewInt (k, _, _, _) -> "new " ^ Ident.name k ^ " {int...}"
  | Invoke (v, _, x, _) -> Ident.name v ^ "." ^ pp_sym x
  | InvokeInstantiate (v, _, _) -> Ident.name v ^ ".instantiate[...]"
  | Axiom (_, v, k) -> "⟨" ^ Ident.name v ^ " | " ^ Ident.name k ^ "⟩"
  | Lit (n, v, _) -> "lit " ^ string_of_int n ^ " → " ^ Ident.name v
  | Add (a, b, v, _) -> Ident.name a ^ " + " ^ Ident.name b ^ " → " ^ Ident.name v
  | Sub (a, b, v, _) -> Ident.name a ^ " - " ^ Ident.name b ^ " → " ^ Ident.name v
  | Ifz (v, _, _) -> "ifz " ^ Ident.name v
  | End -> "end"
  | Ret (_, v) -> "ret " ^ Ident.name v

(* ========================================================================= *)
(* Single-Step Semantics                                                     *)
(* ========================================================================= *)

(** Single step of the abstract machine. Returns None if stuck or terminal. *)
let step ((cmd, e): config) : config option =
  match cmd with
  (* =========== Let forms =========== *)
  
  (* (let) ⟨let v = m(args); s ∥ E⟩ → ⟨s ∥ E, v → {m; E|args}⟩ 
     Constructs a data value with the xtor name and captured args *)
  | Let (v, _, m, args, body) ->
      let e0 = sub_env e args in
      let e' = extend e v (DataVal (m, e0)) in
      Some (body, e')

  (* (let-instantiate) Constructs Forall value - type argument is erased *)
  | LetInstantiate (v, _, _, _, body) ->
      let inst_sym = Path.of_string "instantiate" in
      let e' = extend e v (DataVal (inst_sym, empty_env)) in
      Some (body, e')

  (* =========== New forms =========== *)

  (* (new) ⟨new v = {bs}; s ∥ E⟩ → ⟨s ∥ E, v → {E; bs}⟩
     Creates a codata value: captures current env, branches bind params when invoked *)
  | New (v, _, branches, body) ->
      let e' = extend e v (CodataVal (e, branches)) in
      Some (body, e')

  (* (new-forall) Creates a Forall codata value *)
  | NewForall (v, a, _, s1, s2) ->
      let e' = extend e v (ForallVal (e, a, s1)) in
      Some (s2, e')

  (* =========== Switch forms =========== *)

  (* (switch) ⟨switch v {bs} ∥ E⟩
     Destructure data value v, select matching branch, bind params *)
  | Switch (v, _, branches) ->
      (match lookup e v with
       | DataVal (m, e0) ->
           let (_, _, params, branch_body) = select_branch m branches in
           let e0_list = List.rev (Ident.to_list e0) in
           let e' = List.fold_left2 (fun acc p (_, val0) -> extend acc p val0) e params e0_list in
           Some (branch_body, e')
       | IntVal n ->
           (match branches with
              [] -> failwith "switch on int with no branches"
            | (_, _, params, branch_body) :: _ ->
                let e' = extend e (List.hd params) (IntVal n) in
                Some (branch_body, e'))
       | _ -> failwith "switch: expected data value")

  (* (switch-forall) Destructure Forall value - types are erased *)
  | SwitchForall (v, _, _, s) ->
      (match lookup e v with
       | DataVal _ | ForallVal _ -> Some (s, e)
       | _ -> failwith "switch-forall: expected forall value")

  (* =========== Invoke forms =========== *)

  (* (invoke) ⟨v.m(args) ∥ E, v → {E0; bs}⟩ → ⟨b ∥ E0[params↦E(args)]⟩
     Invokes a codata value: find matching branch, bind args to params *)
  | Invoke (v, _, m, args) ->
      (match lookup e v with
       | CodataVal (e0, branches) ->
           let (_, _, params, branch_body) = select_branch m branches in
           let arg_vals = List.map (fun a -> lookup e a) args in
           let e_merged = merge_env e0 e in
           let e' = List.fold_left2 extend e_merged params arg_vals in
           Some (branch_body, e')
       | _ -> failwith "invoke: expected codata value")

  (* (invoke-instantiate) Instantiate a Forall codata value - type erased *)
  | InvokeInstantiate (v, _, _) ->
      (match lookup e v with
       | ForallVal (e0, _, s) ->
           Some (s, merge_env e0 e)
       | CodataVal (e0, branches) ->
           let inst_sym = Path.of_string "instantiate" in
           let (_, _, _, branch_body) = select_branch inst_sym branches in
           Some (branch_body, merge_env e0 e)
       | _ -> failwith "invoke-instantiate: expected forall value")

  (* =========== Axiom =========== *)

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
                let e1_list = List.rev (Ident.to_list e1) in
                let e' = List.fold_left2 (fun acc p (_, val0) -> extend acc p val0) e0 params e1_list in
                Some (branch_body, e')
            | _ -> failwith "axiom: expected data or int on the left")
       | Some (FunVal (e0, px, py, s)) ->
           (match lookup e v1 with
            | DataVal (_, e1) ->
                let e1_list = List.rev (Ident.to_list e1) in
                (match e1_list with
                 | [(_, v_x); (_, v_y)] ->
                     let e' = extend (extend (merge_env e0 e) px v_x) py v_y in
                     Some (s, e')
                 | _ -> failwith "axiom: fun expected 2 args")
            | _ -> failwith "axiom: expected data on the left for fun")
       | Some (ForallVal (e0, _, s)) ->
           Some (s, merge_env e0 e)
       | Some (ThunkVal (e0, px, s)) ->
           (match lookup e v1 with
            | DataVal (_, e1) ->
                let e1_list = List.rev (Ident.to_list e1) in
                (match e1_list with
                 | [(_, v0)] ->
                     let e' = extend (merge_env e0 e) px v0 in
                     Some (s, e')
                 | _ -> failwith "axiom: thunk expected 1 arg")
            | _ -> failwith "axiom: expected data on the left for thunk")
       | Some (ReturnVal (e0, px, s)) ->
           (match lookup e v1 with
            | DataVal (_, e1) ->
                let e1_list = List.rev (Ident.to_list e1) in
                (match e1_list with
                 | [(_, v0)] ->
                     let e' = extend (merge_env e0 e) px v0 in
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
  if trace then 
    Printf.printf "    [%d] %s | env has %d bindings\n"
      steps (cmd_name cmd) (List.length (Ident.to_list e));
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