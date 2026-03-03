(**
  module: Compile_aarch64
  description: Compile AXIL to AARCH64 assembly.
  
  Translated from Idris2 implementation (Coder.idr).
*)

open Common.Identifiers
open Axil.Terms
open Axil.Types.AxilTypes
open Axil.Types.AxilBase
open Aarch64.Code
open Aarch64.Substitution

(*
  GOTCHAS
  - 0 must not be the address of a block
  - initially heap must point to a fresh block
  - initially free must point to enough space
  - free must be initially filled with 0
*)

(* ========================================================================= *)
(* State Monad for Fresh Label Generation                                    *)
(* ========================================================================= *)

type 'a state = int -> 'a * int

let return (x: 'a) : 'a state = fun s -> (x, s)
let bind (m: 'a state) (f: 'a -> 'b state) : 'b state =
  fun s -> let (a, s') = m s in f a s'
let ( let* ) = bind

let get : int state = fun s -> (s, s)
let put (s: int) : unit state = fun _ -> ((), s)
let run_state (m: 'a state) (s: int) : 'a * int = m s

let fresh_label : int state =
  let* n = get in
  let* () = put (n + 1) in
  return n

(* ========================================================================= *)
(* Context and Register Mapping                                              *)
(* ========================================================================= *)

(** The compilation context: an ordered list of variable bindings.
    Head of list = head of context (will be consumed first). *)
type ctx = (var * chiral_typ) list

(** Position of a variable from the END of the context (0 = last element) *)
let position_from_end (ctx: ctx) (x: var) : int =
  let rec find_pos lst i =
    match lst with
    | [] -> failwith ("variable not found in context: " ^ Ident.name x)
    | (v, _) :: rest ->
        if Ident.equal v x then i
        else find_pos rest (i + 1)
  in
  let pos_from_start = find_pos ctx 0 in
  let len = List.length ctx in
  len - 1 - pos_from_start

(** Maps variable to its first register (block pointer) *)
let symbol_register1 (ctx: ctx) (x: var) : Register.t =
  let pos = position_from_end ctx x in
  Register.mk (Register.reserved + 2 * pos)

(** Maps variable to its second register (value/tag) *)
let symbol_register2 (ctx: ctx) (x: var) : Register.t =
  let pos = position_from_end ctx x in
  Register.mk (Register.reserved + 2 * pos + 1)

(** Register for a fresh binding (after all existing vars) *)
let fresh_register1 (ctx: ctx) : Register.t =
  Register.mk (Register.reserved + 2 * List.length ctx)

let fresh_register2 (ctx: ctx) : Register.t =
  Register.mk (Register.reserved + 2 * List.length ctx + 1)

(** Check if type is external (primitive) *)
let is_ext_type (ct: chiral_typ) : bool =
  match ct with
  | Prd (Ext _) | Cns (Ext _) -> true
  | _ -> false

(* ========================================================================= *)
(* Control Flow Helpers                                                      *)
(* ========================================================================= *)

(** Generate code that skips if register is zero *)
let skip_if_zero (this: Register.t) (code: code list) : code list state =
  let* lab = fresh_label in
  let label = "lab" ^ string_of_int lab in
  return (
    CMPI (this, 0) ::
    BEQ label ::
    code @
    LAB label :: [])

(** Generate if-then-else based on register being zero *)
let if_zero_then_else (this: Register.t) (thn: code list) (els: code list) 
    : code list state =
  let* lab_then = fresh_label in
  let* lab_else = fresh_label in
  let label_then = "lab" ^ string_of_int lab_then in
  let label_else = "lab" ^ string_of_int lab_else in
  return (
    CMPI (this, 0) ::
    BEQ label_then ::
    els @
    B label_else ::
    LAB label_then ::
    thn @
    LAB label_else :: [])

(* ========================================================================= *)
(* Reference Counting                                                        *)
(* ========================================================================= *)

(** Share a block N times (increment ref count by N) *)
let share_block_n (this: Register.t) (k: int) : code list state =
  skip_if_zero this (
    LDR (Register.temp, this, Offset.reference_count) ::
    ADDI (Register.temp, Register.temp, k) ::
    STR (Register.temp, this, Offset.reference_count) :: [])

(** Share a block once *)
let share_block (this: Register.t) : code list state =
  share_block_n this 1

(** Erase a valid (non-null) object - decrement ref count, free if zero *)
let erase_valid_object (this: Register.t) : code list state =
  if_zero_then_else Register.temp
    (* then: ref count is 0, add to free list *)
    (STR (Register.free, this, Offset.next_element) ::
     MOVR (Register.free, this) :: [])
    (* else: decrement ref count *)
    (SUBI (Register.temp, Register.temp, 1) ::
     STR (Register.temp, this, Offset.reference_count) :: [])

(** Erase a block (null check + decrement/free) *)
let erase_block (this: Register.t) : code list state =
  let* erase_code = erase_valid_object this in
  skip_if_zero this (
    LDR (Register.temp, this, Offset.reference_count) ::
    erase_code)

(** Share all fields of a block *)
let rec share_fields (accu: Register.t) (this: Register.t) (n: int) 
    : code list state =
  if n = 0 then return []
  else
    let* share_code = share_block accu in
    let* rest = share_fields accu this (n - 1) in
    return (
      LDR (accu, this, Offset.field1 (n - 1)) ::
      share_code @
      rest)

(** Erase all fields of a block *)
let rec erase_fields (accu: Register.t) (this: Register.t) (n: int)
    : code list state =
  if n = 0 then return []
  else
    let* erase_code = erase_block accu in
    let* rest = erase_fields accu this (n - 1) in
    return (
      LDR (accu, this, Offset.field1 (n - 1)) ::
      erase_code @
      rest)

(** Acquire a fresh block from heap/free list *)
let acquire_block (accu: Register.t) (this: Register.t) : code list state =
  let* erase_code = erase_fields accu Register.heap Offset.fields_per_block in
  let* adapt_free = if_zero_then_else Register.free
    (* then: free list empty, advance free pointer *)
    (ADDI (Register.free, Register.heap, Offset.field1 Offset.fields_per_block) :: [])
    (* else: use next from free list *)
    (MOVI (Register.temp, 0) ::
     STR (Register.temp, Register.heap, Offset.next_element) ::
     erase_code) in
  let* adapt_heap = if_zero_then_else Register.heap
    (* then: heap exhausted, use from free list *)
    (MOVR (Register.heap, Register.free) ::
     LDR (Register.free, Register.free, Offset.next_element) ::
     adapt_free)
    (* else: use current heap block *)
    (MOVI (Register.temp, 0) ::
     STR (Register.temp, this, Offset.reference_count) :: []) in
  return (
    MOVR (this, Register.heap) ::
    LDR (Register.heap, Register.heap, Offset.next_element) ::
    adapt_heap)

(** Release a block (decrement ref count or share fields if still in use) *)
let release_block (accu: Register.t) (this: Register.t) : code list state =
  let* share_code = share_fields accu this Offset.fields_per_block in
  let* adapt_heap = if_zero_then_else Register.temp
    (* then: ref count is 0, return to free list *)
    (STR (Register.heap, this, Offset.next_element) ::
     MOVR (Register.heap, this) :: [])
    (* else: still in use, decrement and share fields *)
    (SUBI (Register.temp, Register.temp, 1) ::
     STR (Register.temp, this, Offset.reference_count) ::
     share_code) in
  return (
    LDR (Register.temp, this, Offset.reference_count) ::
    adapt_heap)

(* ========================================================================= *)
(* Store/Load Operations                                                     *)
(* ========================================================================= *)

(** Store a single value into a block at position k.
    For external types, store only register2 (the value).
    For other types, store both registers (block ptr + tag). *)
let store_value (ct: chiral_typ) (ctx: ctx) (into: Register.t) (k: int) 
    : code list =
  let fresh_var = Ident.fresh () in
  let extended_ctx = (fresh_var, ct) :: ctx in
  if is_ext_type ct then
    STR (symbol_register2 extended_ctx fresh_var, into, Offset.field2 k) ::
    MOVI (Register.temp, 0) ::
    STR (Register.temp, into, Offset.field1 k) :: []
  else
    STR (symbol_register2 extended_ctx fresh_var, into, Offset.field2 k) ::
    STR (symbol_register1 extended_ctx fresh_var, into, Offset.field1 k) :: []

(** Load a binder from a block at position k *)
let load_binder (ct: chiral_typ) (ctx: ctx) (from: Register.t) (k: int) 
    : code list =
  let fresh_var = Ident.fresh () in
  let extended_ctx = (fresh_var, ct) :: ctx in
  if is_ext_type ct then
    LDR (symbol_register2 extended_ctx fresh_var, from, Offset.field2 k) :: []
  else
    LDR (symbol_register2 extended_ctx fresh_var, from, Offset.field2 k) ::
    LDR (symbol_register1 extended_ctx fresh_var, from, Offset.field1 k) :: []

(** Store a block pointer at position k *)
let store_block (ctx: ctx) (into: Register.t) (k: int) : code list =
  STR (fresh_register1 ctx, into, Offset.field1 k) :: []

(** Load a block pointer from position k *)
let load_block (ctx: ctx) (from: Register.t) (k: int) : code list =
  LDR (fresh_register1 ctx, from, Offset.field1 k) :: []

(** Store zeros at positions 0..k-1 *)
let rec store_zeroes (into: Register.t) (k: int) : code list =
  if k = 0 then []
  else
    MOVI (Register.temp, 0) ::
    STR (Register.temp, into, Offset.field1 (k - 1)) ::
    store_zeroes into (k - 1)

(** Store multiple values from context prefix *)
let rec store_values (vs: (var * chiral_typ) list) (ctx: ctx) 
    (into: Register.t) (k: int) : code list =
  match vs with
  | [] -> store_zeroes into k
  | _ when k = 0 -> []  (* No more space *)
  | (_v, ct) :: rest ->
      let extended_ctx = rest @ ctx in
      store_value ct extended_ctx into (k - 1) @
      store_values rest ctx into (k - 1)

(** Load multiple binders into context prefix *)
let rec load_binders (xs: (var * chiral_typ) list) (ctx: ctx)
    (from: Register.t) (k: int) : code list =
  match xs with
  | [] -> []
  | _ when k = 0 -> []  (* No more space *)
  | (_, ct) :: rest ->
      let extended_ctx = rest @ ctx in
      load_binder ct extended_ctx from (k - 1) @
      load_binders rest ctx from (k - 1)

(** Helper to split list into chunks *)
let take n lst = 
  let rec aux n acc lst =
    if n = 0 then List.rev acc
    else match lst with
      | [] -> List.rev acc
      | x :: xs -> aux (n - 1) (x :: acc) xs
  in aux n [] lst

let drop n lst =
  let rec aux n lst =
    if n = 0 then lst
    else match lst with
      | [] -> []
      | _ :: xs -> aux (n - 1) xs
  in aux n lst

(** Store remaining values in linked blocks *)
let rec store_rest (vs: (var * chiral_typ) list) (ctx: ctx) : code list state =
  match vs with
  | [] -> return []
  | _ ->
      let vars = take (Offset.fields_per_block - 1) vs in
      let rest = drop (Offset.fields_per_block - 1) vs in
      let rest_ctx = rest @ ctx in
      let this = fresh_register1 rest_ctx in
      let accu = fresh_register2 rest_ctx in
      let* acquire = acquire_block accu this in
      let* store_rest_code = store_rest rest ctx in
      return (
        store_block (vars @ rest_ctx) Register.heap (Offset.fields_per_block - 1) @
        store_values vars rest_ctx Register.heap (Offset.fields_per_block - 1) @
        acquire @
        store_rest_code)

(** Store environment: creates linked blocks for all values *)
let store (vs: (var * chiral_typ) list) (ctx: ctx) : code list state =
  match vs with
  | [] ->
      return (MOVI (fresh_register1 ctx, 0) :: [])
  | _ ->
      let vars = take Offset.fields_per_block vs in
      let rest = drop Offset.fields_per_block vs in
      let rest_ctx = rest @ ctx in
      let this = fresh_register1 rest_ctx in
      let accu = fresh_register2 rest_ctx in
      let* acquire = acquire_block accu this in
      let* store_rest_code = store_rest rest ctx in
      return (
        store_values vars rest_ctx Register.heap Offset.fields_per_block @
        acquire @
        store_rest_code)

(** Load remaining values from linked blocks *)
let rec load_rest (xs: (var * chiral_typ) list) (ctx: ctx) : code list state =
  match xs with
  | [] -> return []
  | _ ->
      let vars = take (Offset.fields_per_block - 1) xs in
      let rest = drop (Offset.fields_per_block - 1) xs in
      let rest_ctx = rest @ ctx in
      let this = fresh_register1 rest_ctx in
      let accu = fresh_register2 rest_ctx in
      let* load_rest_code = load_rest rest ctx in
      let* release = release_block accu this in
      return (
        load_rest_code @
        release @
        load_block (vars @ rest_ctx) this (Offset.fields_per_block - 1) @
        load_binders vars rest_ctx this (Offset.fields_per_block - 1))

(** Load environment: loads all values from linked blocks *)
let load (xs: (var * chiral_typ) list) (ctx: ctx) : code list state =
  match xs with
  | [] -> return []
  | _ ->
      let vars = take Offset.fields_per_block xs in
      let rest = drop Offset.fields_per_block xs in
      let rest_ctx = rest @ ctx in
      let this = fresh_register1 rest_ctx in
      let accu = fresh_register2 rest_ctx in
      let* load_rest_code = load_rest rest ctx in
      let* release = release_block accu this in
      return (
        load_rest_code @
        release @
        load_binders vars rest_ctx this Offset.fields_per_block)

(* ========================================================================= *)
(* Branch Table Generation                                                   *)
(* ========================================================================= *)

(** Generate jump table entries *)
let rec code_table (n: int) (lab_base: int) (lab_branch: int) : code list =
  if n = 0 then []
  else
    B ("lab" ^ string_of_int lab_base ^ "b" ^ string_of_int lab_branch) ::
    code_table (n - 1) lab_base (lab_branch + 1)

(* ========================================================================= *)
(* Substitution Handling                                                     *)
(* ========================================================================= *)

(** Compute occurrences of a source variable in a substitution.
    Returns list of target positions that map from this source. *)
let occurrences (subst: (var * var) list) (src: var) : var list =
  List.filter_map (fun (tgt, s) ->
    if Ident.equal s src then Some tgt else None
  ) subst

(** Transpose a substitution: for each source var, list all targets.
    Result is indexed by source variables. *)
let transpose (src_ctx: ctx) (subst: (var * var) list) 
    : (var * var list) list =
  List.map (fun (v, _) -> (v, occurrences subst v)) src_ctx

(** Update reference count based on usage:
    - 0 uses: erase
    - 1 use: no change
    - n uses: share n-1 times *)
let update_reference_count (r: Register.t) (n: int) : code list state =
  if n = 0 then erase_block r
  else if n = 1 then return []
  else share_block_n r (n - 1)

(** Generate code for weakening/contraction based on usage counts *)
let rec code_weakening_contraction (ctx: ctx) (usage: (var * var list) list)
    : code list state =
  match ctx, usage with
  | [], [] -> return []
  | (v, ct) :: rest_ctx, (_, targets) :: rest_usage ->
      if is_ext_type ct then
        (* External types don't need reference counting *)
        code_weakening_contraction rest_ctx rest_usage
      else
        let* update = update_reference_count (symbol_register1 ctx v) 
                        (List.length targets) in
        let* rest = code_weakening_contraction rest_ctx rest_usage in
        return (update @ rest)
  | _ -> failwith "context and usage list length mismatch"

(** Build register connection graph for exchange.
    For each register, list the registers it should be moved to. *)
let connections (src_ctx: ctx) (tgt_ctx: ctx) (usage: (var * var list) list)
    : Register.t list list =
  let graph = Array.make 32 [] in
  List.iter2 (fun (v, ct) (_, targets) ->
    let src_r1 = symbol_register1 src_ctx v in
    let src_r2 = symbol_register2 src_ctx v in
    let tgt_regs1 = List.map (symbol_register1 tgt_ctx) targets in
    let tgt_regs2 = List.map (symbol_register2 tgt_ctx) targets in
    if is_ext_type ct then
      (* External types: only move register2 *)
      graph.(Register.to_int src_r2) <- tgt_regs2
    else begin
      graph.(Register.to_int src_r1) <- tgt_regs1;
      graph.(Register.to_int src_r2) <- tgt_regs2
    end
  ) src_ctx usage;
  Array.to_list graph

(* ========================================================================= *)
(* Label/Definition Indexing                                                 *)
(* ========================================================================= *)

(** Map from definition paths to indices *)
type label_map = int Path.tbl

(** Create label map from definitions *)
let make_label_map (defs: definition Path.tbl) : label_map =
  let lst = Path.to_list defs in
  let indexed = List.mapi (fun i (p, _) -> (p, i)) lst in
  Path.of_list indexed

(** Look up label index *)
let label_index (lmap: label_map) (p: Path.t) : int =
  match Path.find_opt p lmap with
  | Some i -> i
  | None -> failwith ("undefined label: " ^ Path.name p)

(* ========================================================================= *)
(* Main Code Generation                                                      *)
(* ========================================================================= *)

(** Compile a command to AARCH64 assembly *)
let rec code_command (lmap: label_map) (ctx: ctx) (cmd: command) 
    : code list state =
  match cmd with
  (* Substitute: explicit structural rules *)
  | Substitute (subst, body) ->
      (* Build target context from substitution *)
      let tgt_ctx = List.map (fun (v', v) ->
        let (_, ct) = List.find (fun (x, _) -> Ident.equal x v) ctx in
        (v', ct)
      ) subst in
      let usage = transpose ctx subst in
      let* weaken_contract = code_weakening_contraction ctx usage in
      let exchange = code_exhange (connections ctx tgt_ctx usage) in
      let* rest = code_command lmap tgt_ctx body in
      return (weaken_contract @ exchange @ rest)

  (* Jump to label *)
  | Jump (label, _args) ->
      let idx = label_index lmap label in
      return (B ("lab" ^ string_of_int idx) :: [])

  (* Let: construct data value *)
  | Let (v, dec, xtor, args, body) ->
      (* args are the captured environment *)
      let captured_ctx = List.map (fun arg ->
        List.find (fun (x, _) -> Ident.equal x arg) ctx
      ) args in
      let new_ctx = (v, Prd (Sgn (dec.name, dec.type_args))) :: ctx in
      let tag_reg = symbol_register2 new_ctx v in
      (* Find xtor index *)
      let xtor_idx = 
        let rec find_idx i = function
          | [] -> 0
          | (y: xtor) :: _ when Path.equal y.name xtor -> i
          | _ :: rest -> find_idx (i + 1) rest
        in find_idx 0 dec.xtors
      in
      let* stores = store captured_ctx ctx in
      let* rest = code_command lmap new_ctx body in
      return (
        stores @
        MOVI (tag_reg, Offset.jump_length xtor_idx) ::
        rest)

  (* Switch: pattern match on data *)
  | Switch (v, dec, branches) ->
      let tag_reg = symbol_register2 ctx v in
      let* base_lab = fresh_label in
      let num_branches = List.length branches in
      let* branch_codes = code_clauses lmap ctx dec branches base_lab 0 in
      return (
        ADR (Register.temp, "lab" ^ string_of_int base_lab) ::
        (if num_branches <= 1 then []
         else ADD (Register.temp, Register.temp, tag_reg) :: []) @
        BR Register.temp ::
        LAB ("lab" ^ string_of_int base_lab) ::
        (if num_branches <= 1 then []
         else code_table num_branches base_lab 0) @
        List.concat branch_codes)

  (* New: create codata value *)
  | New (v, dec, branches, body) ->
      (* Captured environment is the current context *)
      let captured_ctx = ctx in
      let new_ctx = (v, Cns (Sgn (dec.name, dec.type_args))) :: ctx in
      let tab_reg = symbol_register2 new_ctx v in
      let* stores = store captured_ctx ctx in
      let* base_lab = fresh_label in
      let* rest = code_command lmap new_ctx body in
      let num_branches = List.length branches in
      let* branch_codes = code_methods lmap captured_ctx dec branches base_lab 0 in
      return (
        stores @
        ADR (tab_reg, "lab" ^ string_of_int base_lab) ::
        rest @
        LAB ("lab" ^ string_of_int base_lab) ::
        (if num_branches <= 1 then []
         else code_table num_branches base_lab 0) @
        List.concat branch_codes)

  (* Invoke: call codata method *)
  | Invoke (v, dec, xtor, _args) ->
      let tab_reg = symbol_register2 ctx v in
      let xtor_idx = 
        let rec find_idx i = function
          | [] -> 0
          | (y: xtor) :: _ when Path.equal y.name xtor -> i
          | _ :: rest -> find_idx (i + 1) rest
        in find_idx 0 dec.xtors
      in
      let num_methods = List.length dec.xtors in
      return (
        if num_methods <= 1 then
          BR tab_reg :: []
        else
          ADDI (Register.temp, tab_reg, Offset.jump_length xtor_idx) ::
          BR Register.temp :: [])

  (* Axiom: cut between producer and consumer - invoke the continuation.
     For int continuations created by NewInt, the continuation expects
     the parameter in the same register position as k (since param replaces k
     in the context). So we save k's address, move v to k's register, then jump. *)
  | Axiom (_, v, k) ->
      let k_reg = symbol_register2 ctx k in
      let v_reg = symbol_register2 ctx v in
      return (
        MOVR (Register.temp, k_reg) ::   (* Save continuation address *)
        MOVR (k_reg, v_reg) ::           (* Put value where param expects it *)
        BR Register.temp :: [])          (* Jump to continuation *)

  (* Literal: create integer value *)
  | Lit (n, v, body) ->
      let new_ctx = (v, Prd (Ext Common.Types.Int)) :: ctx in
      let* rest = code_command lmap new_ctx body in
      return (
        MOVI (symbol_register2 new_ctx v, n) ::
        rest)

  (* NewInt: create integer consumer (continuation) *)
  | NewInt (k, param, then_body, cont_body) ->
      let k_ctx = (k, Cns (Ext Common.Types.Int)) :: ctx in
      let* stores = store ctx ctx in
      let* base_lab = fresh_label in
      let* cont = code_command lmap k_ctx cont_body in
      (* Generate the single "method" for int consumption *)
      let param_ctx = (param, Prd (Ext Common.Types.Int)) :: ctx in
      let* loads = load ctx ctx in
      let* method_body = code_command lmap param_ctx then_body in
      return (
        stores @
        ADR (symbol_register2 k_ctx k, "lab" ^ string_of_int base_lab) ::
        cont @
        LAB ("lab" ^ string_of_int base_lab) ::
        loads @
        method_body)

  (* Add: integer addition *)
  | Add (x, y, v, body) ->
      let new_ctx = (v, Prd (Ext Common.Types.Int)) :: ctx in
      let* rest = code_command lmap new_ctx body in
      return (
        ADD (symbol_register2 new_ctx v, symbol_register2 ctx x, 
             symbol_register2 ctx y) ::
        rest)

  (* Sub: integer subtraction *)
  | Sub (x, y, v, body) ->
      let new_ctx = (v, Prd (Ext Common.Types.Int)) :: ctx in
      let x_reg = symbol_register2 ctx x in
      let y_reg = symbol_register2 ctx y in
      let v_reg = symbol_register2 new_ctx v in
      let* rest = code_command lmap new_ctx body in
      (* SUB rd, rn, rm computes rn - rm *)
      return (
        (* Use SUBI with temp or direct subtraction *)
        MOVR (Register.temp, x_reg) ::
        MOVR (v_reg, x_reg) ::
        (* Implement subtraction: v = x - y *)
        (* Since we don't have SUB, use: v = x + (-y) = x - y via SUBI trick *)
        (* Actually, let's compute properly: we need to negate y then add *)
        (* Simpler: use the fact that SUBI can work if we have immediate *)
        (* For register-register sub, we need: rd = rn - rm *)
        (* We can do: MSUB rd, rm, #1, rn (rd = rn - rm*1) but that's not right *)
        (* Let's just use a sequence: temp = 0; temp = temp - y; temp = temp + x *)
        (* Or better: synthesize from available ops. SDIV/MUL can help but awkward *)
        (* Simplest correct: SUBI isn't right. We should add a SUB instruction. *)
        (* For now, use: v = x + (0 - y). Need NEG which is SUB from zero *)
        (* Actually SUBI rd, rn, imm does rd = rn - imm. We need rd = x - y. *)
        (* Hack: use MSUB: rd = ra - rn*rm --> rd = x - y*1 if we had const 1 *)
        (* Let's use: MOVI temp 1; MSUB v temp y x gives v = x - y*1 = x - y *)
        MOVI (Register.temp, 1) ::
        MSUB (v_reg, Register.temp, y_reg, x_reg) ::
        rest)

  (* Ifz: conditional on zero *)
  | Ifz (v, then_cmd, else_cmd) ->
      let v_reg = symbol_register2 ctx v in
      let* lab = fresh_label in
      let label = "lab" ^ string_of_int lab in
      let* else_code = code_command lmap ctx else_cmd in
      let* then_code = code_command lmap ctx then_cmd in
      return (
        CMPI (v_reg, 0) ::
        BEQ label ::
        else_code @
        LAB label ::
        then_code)

  (* Return: final result *)
  | Ret (_, v) ->
      return (
        MOVR (Register.return2, symbol_register2 ctx v) ::
        B "cleanup" :: [])

  (* End: terminal *)
  | End ->
      return (B "cleanup" :: [])

(** Compile a clause (branch of switch) *)
and code_clause (lmap: label_map) (ctx: ctx) (dec: dec)
    (xtor_name: Path.t) (_type_vars: var list) (term_vars: var list) 
    (body: command) : code list state =
  (* Find the xtor to get argument types *)
  let xtor = match List.find_opt (fun (x: xtor) ->
                   Path.equal x.name xtor_name) dec.xtors with
    | Some x -> x
    | None -> failwith ("xtor not found: " ^ Path.name xtor_name)
  in
  (* Build context for branch: term_vars bound to xtor argument types *)
  let arg_bindings = List.map2 (fun v ct -> (v, ct)) term_vars xtor.argument_types in
  (* After switch, the scrutinee is consumed; we have arg_bindings @ tail_ctx *)
  (* Since switch consumes head, ctx without head is the tail *)
  let tail_ctx = match ctx with
    | [] -> []
    | _ :: rest -> rest
  in
  let branch_ctx = arg_bindings @ tail_ctx in
  let* loads = load arg_bindings tail_ctx in
  let* body_code = code_command lmap branch_ctx body in
  return (loads @ body_code)

(** Compile all clauses of a switch *)
and code_clauses (lmap: label_map) (ctx: ctx) (dec: dec)
    (branches: branch list) (base_lab: int) (branch_idx: int) 
    : code list list state =
  match branches with
  | [] -> return []
  | (xtor_name, type_vars, term_vars, body) :: rest ->
      let* clause = code_clause lmap ctx dec xtor_name type_vars term_vars body in
      let* rest_clauses = code_clauses lmap ctx dec rest base_lab (branch_idx + 1) in
      let labeled = 
        LAB ("lab" ^ string_of_int base_lab ^ "b" ^ string_of_int branch_idx) :: 
        clause in
      return (labeled :: rest_clauses)

(** Compile a method (branch of new/codata) *)
and code_method (lmap: label_map) (captured_ctx: ctx) 
    (dec: dec) (xtor_name: Path.t) 
    (_type_vars: var list) (term_vars: var list) (body: command) 
    : code list state =
  (* Find the xtor to get argument types *)
  let xtor = match List.find_opt (fun (x: xtor) ->
                   Path.equal x.name xtor_name) dec.xtors with
    | Some x -> x
    | None -> failwith ("xtor not found: " ^ Path.name xtor_name)
  in
  (* Method context: term_vars (args) + captured_ctx *)
  let arg_bindings = List.map2 (fun v ct -> (v, ct)) term_vars xtor.argument_types in
  let method_ctx = arg_bindings @ captured_ctx in
  let* loads = load captured_ctx arg_bindings in
  let* body_code = code_command lmap method_ctx body in
  return (loads @ body_code)

(** Compile all methods of a codata value *)
and code_methods (lmap: label_map) (captured_ctx: ctx)
    (dec: dec) (branches: branch list)
    (base_lab: int) (branch_idx: int) : code list list state =
  match branches with
  | [] -> return []
  | (xtor_name, type_vars, term_vars, body) :: rest ->
      let* method_code = code_method lmap captured_ctx dec xtor_name 
                           type_vars term_vars body in
      let* rest_methods = code_methods lmap captured_ctx dec rest 
                            base_lab (branch_idx + 1) in
      let labeled =
        LAB ("lab" ^ string_of_int base_lab ^ "b" ^ string_of_int branch_idx) ::
        method_code in
      return (labeled :: rest_methods)

(* ========================================================================= *)
(* Top-Level Compilation                                                     *)
(* ========================================================================= *)

(** Compile all definitions to labeled code blocks *)
let translate (lmap: label_map) (defs: definition Path.tbl) 
    : code list list state =
  let def_list = Path.to_list defs in
  let rec compile_all = function
    | [] -> return []
    | (_, def) :: rest ->
        let ctx = def.term_params in
        let* code = code_command lmap ctx def.body in
        let* rest_code = compile_all rest in
        return (code :: rest_code)
  in
  compile_all def_list

(** Assemble code blocks with labels *)
let assemble (start_label: int) (sections: code list list) : code list =
  let rec aux lab = function
    | [] -> []
    | section :: rest ->
        (LAB ("lab" ^ string_of_int lab) :: section) @ aux (lab + 1) rest
  in
  aux start_label sections

(** Main compilation entry point *)
let compile (main: definition) (defs: definition Path.tbl) : code list * int =
  let all_defs = Path.add main.path main defs in
  let lmap = make_label_map all_defs in
  let (sections, _) = run_state (translate lmap all_defs) 
                        (List.length (Path.to_list all_defs)) in
  let code = assemble 0 sections in
  let main_args = List.length main.term_params in
  (code, main_args)

(** Compile to assembly string *)
let compile_to_string (name: string) (main: definition) (defs: definition Path.tbl) 
    : string =
  let (code, arg_num) = compile main defs in
  let prog = Code.list_to_string code in
  Code.into_aarch64_routine name prog arg_num
