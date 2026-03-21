(**
  module: Compile_checked
  description: Compile checked AXIL commands to AARCH64 assembly.
  
  This compiler operates on checked_command, where each AST node carries
  its typing context. This eliminates manual context threading and the
  bugs that come with it.
*)

open Common.Identifiers
open Axil.Terms
open Axil.Checked
open Axil.Types.AxilTypes
open Axil.Types.AxilBase
open Aarch64.Code
open Aarch64.Substitution

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

(** Position of a variable from the END of the context (0 = last element). *)
let position_from_end (ctx: ctx) (x: var) : int =
  let rec find_pos lst i =
    match lst with
      [] -> failwith ("variable not found in context: " ^ Ident.name x)
    | (v, _) :: rest ->
        if Ident.equal v x then i
        else find_pos rest (i + 1)
  in
  let pos_from_start = find_pos ctx 0 in
  let len = List.length ctx in
  len - 1 - pos_from_start

(** Maps variable to its first register (block pointer).  *)
let symbol_location1 (ctx: ctx) (x: var) : Register.t =
  let pos = position_from_end ctx x in
  Register.mk (Register.reserved + 2 * pos)

(** Maps variable to its second register (value/tag). *)
let symbol_location2 (ctx: ctx) (x: var) : Register.t =
  let pos = position_from_end ctx x in
  Register.mk (Register.reserved + 2 * pos + 1)

(** Register for a fresh binding (after all existing vars). *)
let fresh_location1 (ctx: ctx) : Register.t =
  Register.mk (Register.reserved + 2 * List.length ctx)

let fresh_location2 (ctx: ctx) : Register.t =
  Register.mk (Register.reserved + 2 * List.length ctx + 1)

(** Check if type is external (primitive) PRODUCER.
    Only external PRODUCERS use one register (just the value in location2).
    External CONSUMERS (Cns (Ext _)) use two registers like regular codata:
    - location1 = block pointer (captured environment)
    - location2 = code address
    This unifies CNewInt with CNew and CAxiom with CInvoke. *)
let is_ext_type (ct: chiral_typ) : bool =
  match ct with Prd (_, Ext _) -> true | _ -> false

(* ========================================================================= *)
(* Control Flow Helpers                                                      *)
(* ========================================================================= *)

let skip_if_zero (this: Register.t) (code: code) : code state =
  let* lab = fresh_label in
  let label = "lab" ^ string_of_int lab in
  return (
    CMPI (this, 0) ::
    BEQ label ::
    code @
    LAB label :: [])

let if_zero_then_else (this: Register.t) (thn: code) (els: code) 
    : code state =
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

let share_block_n (this: Register.t) (k: int) : code state =
  skip_if_zero this (
    LDR (Register.temp, this, Offset.reference_count) ::
    ADDI (Register.temp, Register.temp, k) ::
    STR (Register.temp, this, Offset.reference_count) :: [])

let share_block (this: Register.t) : code state =
  share_block_n this 1

let erase_valid_object (this: Register.t) : code state =
  if_zero_then_else Register.temp
    (STR (Register.free, this, Offset.next_element) ::
     MOVR (Register.free, this) :: [])
    (SUBI (Register.temp, Register.temp, 1) ::
     STR (Register.temp, this, Offset.reference_count) :: [])

let erase_block (this: Register.t) : code state =
  let* erase_code = erase_valid_object this in
  skip_if_zero this (
    LDR (Register.temp, this, Offset.reference_count) ::
    erase_code)

let rec share_fields (accu: Register.t) (this: Register.t) (n: int) : code state =
  if n = 0 then return []
  else
    let* share_code = share_block accu in
    let* rest = share_fields accu this (n - 1) in
    return (
      LDR (accu, this, Offset.field1 (n - 1)) ::
      share_code @
      rest)

let rec erase_fields (accu: Register.t) (this: Register.t) (n: int) : code state =
  if n = 0 then return []
  else
    let* erase_code = erase_block accu in
    let* rest = erase_fields accu this (n - 1) in
    return (
      LDR (accu, this, Offset.field1 (n - 1)) ::
      erase_code @
      rest)

let acquire_block (accu: Register.t) (this: Register.t) : code state =
  let* erase_code = erase_fields accu Register.heap Offset.fields_per_block in
  let* adapt_free = if_zero_then_else Register.free
    (ADDI (Register.free, Register.heap, Offset.field1 Offset.fields_per_block) :: [])
    (MOVI (Register.temp, 0L) ::
     STR (Register.temp, Register.heap, Offset.next_element) ::
     erase_code) in
  let* adapt_heap = if_zero_then_else Register.heap
    (MOVR (Register.heap, Register.free) ::
     LDR (Register.free, Register.free, Offset.next_element) ::
     adapt_free)
    (MOVI (Register.temp, 0L) ::
     STR (Register.temp, this, Offset.reference_count) :: []) in
  return (
    MOVR (this, Register.heap) ::
    LDR (Register.heap, Register.heap, Offset.next_element) ::
    adapt_heap)

let release_block (accu: Register.t) (this: Register.t) : code state =
  let* share_code = share_fields accu this Offset.fields_per_block in
  let* adapt_heap = if_zero_then_else Register.temp
    (STR (Register.heap, this, Offset.next_element) ::
     MOVR (Register.heap, this) :: [])
    (SUBI (Register.temp, Register.temp, 1) ::
     STR (Register.temp, this, Offset.reference_count) ::
     share_code) in
  return (
    LDR (Register.temp, this, Offset.reference_count) ::
    adapt_heap)

(* ========================================================================= *)
(* Store/Load Operations                                                     *)
(* ========================================================================= *)

(** Store a single value into a block.
    src_ctx is the context where v's registers can be looked up.
    For non-ext types, we must call share_block on the block pointer before storing,
    because storing creates an additional reference to that block. *)
let store_value (v: var) (ct: chiral_typ) (src_ctx: ctx) (into: Register.t) (k: int) 
    : code state =
  if is_ext_type ct then
    return (
      STR (symbol_location2 src_ctx v, into, Offset.field2 k) ::
      MOVI (Register.temp, 0L) ::
      STR (Register.temp, into, Offset.field1 k) :: [])
  else
    (* Non-ext types have a block pointer - share it before storing *)
    let loc1 = symbol_location1 src_ctx v in
    let* share_code = share_block loc1 in
    return (
      share_code @
      STR (symbol_location2 src_ctx v, into, Offset.field2 k) ::
      STR (loc1, into, Offset.field1 k) :: [])

(** Load a binder from a block.
    x_ctx is the context where x is at the head (x :: as). *)
let load_binder
    (x: var) (ct: chiral_typ) (x_ctx: ctx) (from: Register.t) (k: int) : code =
  let is_ext = is_ext_type ct in
  if is_ext then
    LDR (symbol_location2 x_ctx x, from, Offset.field2 k) :: []
  else
    LDR (symbol_location2 x_ctx x, from, Offset.field2 k) ::
    LDR (symbol_location1 x_ctx x, from, Offset.field1 k) :: []

let store_block (ctx: ctx) (into: Register.t) (k: int) : code =
  STR (fresh_location1 ctx, into, Offset.field1 k) :: []

let load_block (ctx: ctx) (from: Register.t) (k: int) : code =
  LDR (fresh_location1 ctx, from, Offset.field1 k) :: []

let rec store_zeroes (into: Register.t) (k: int) : code =
  if k = 0 then []
  else
    MOVI (Register.temp, 0L) ::
    STR (Register.temp, into, Offset.field1 (k - 1)) ::
    STR (Register.temp, into, Offset.field2 (k - 1)) ::
    store_zeroes into (k - 1)

(** Store multiple values into a block.
    vs: values to store (in order)
    src_ctx: context for looking up source registers *)
let rec store_values (vs: ctx) (src_ctx: ctx) (into: Register.t) (k: int) 
    : code state =
  match vs with
    [] -> return (store_zeroes into k)
  | _ when k = 0 -> return []
  | (v, ct) :: rest_vs ->
      let* this_store = store_value v ct src_ctx into (k - 1) in
      let* rest_store = store_values rest_vs src_ctx into (k - 1) in
      return (this_store @ rest_store)

(** Load multiple binders from a block.
    xs: binders to load (in order)
    as_ctx: tail context (after xs)
    After load, the full context is: xs @ as_ctx *)
let rec load_binders (xs: ctx) (as_ctx: ctx) (from: Register.t) (k: int) 
    : code =
  match xs with
    [] -> []
  | _ when k = 0 -> []
  | (x, ct) :: rest_xs ->
      (* Full context after this load: xs @ as_ctx
        x is at position 0 in xs, so register depends on xs @ as_ctx *)
      let x_ctx = xs @ as_ctx in
      load_binder x ct x_ctx from (k - 1) @
      load_binders rest_xs as_ctx from (k - 1)

(** Helper to split list into chunks *)
let take n lst = 
  let rec aux n acc lst =
    if n = 0 then List.rev acc
    else match lst with
        [] -> List.rev acc
      | x :: xs -> aux (n - 1) (x :: acc) xs
  in aux n [] lst

let drop n lst =
  let rec aux n lst =
    if n = 0 then lst
    else match lst with
        [] -> []
      | _ :: xs -> aux (n - 1) xs
  in aux n lst

(** Store remaining values in linked blocks. *)
let rec store_rest (vs: ctx) (src_ctx: ctx) (as_ctx: ctx) : code state =
  match vs with
  | [] -> return []
  | _ ->
      let vars = take (Offset.fields_per_block - 1) vs in
      let rest = drop (Offset.fields_per_block - 1) vs in
      let rest_ctx = rest @ as_ctx in
      let this = fresh_location1 rest_ctx in
      let accu = fresh_location2 rest_ctx in
      let* acquire = acquire_block accu this in
      let* store_rest_code = store_rest rest src_ctx as_ctx in
      let* stores = store_values vars src_ctx Register.heap (Offset.fields_per_block - 1) in
      return (
        store_block (vars @ rest_ctx) Register.heap (Offset.fields_per_block - 1) @
        stores @
        acquire @
        store_rest_code)

(** Store environment: creates linked blocks for all values.
    vs: values to store
    src_ctx: context for source register lookups
    as_ctx: tail context (context after vs) *)
let store (vs: ctx) (src_ctx: ctx) (as_ctx: ctx) : code state =
  match vs with
  | [] ->
      return (MOVI (fresh_location1 as_ctx, 0L) :: [])
  | _ ->
      let vars = take Offset.fields_per_block vs in
      let rest = drop Offset.fields_per_block vs in
      let rest_ctx = rest @ as_ctx in
      let this = fresh_location1 rest_ctx in
      let accu = fresh_location2 rest_ctx in
      let* acquire = acquire_block accu this in
      let* store_rest_code = store_rest rest src_ctx as_ctx in
      let* stores = store_values vars src_ctx Register.heap Offset.fields_per_block in
      return (
        stores @
        acquire @
        store_rest_code)

(** Load remaining values from linked blocks. *)
let rec load_rest (xs: ctx) (as_ctx: ctx) : code state =
  match xs with
  | [] -> return []
  | _ ->
      let vars = take (Offset.fields_per_block - 1) xs in
      let rest = drop (Offset.fields_per_block - 1) xs in
      let rest_ctx = rest @ as_ctx in
      let this = fresh_location1 rest_ctx in
      let accu = fresh_location2 rest_ctx in
      let* load_rest_code = load_rest rest as_ctx in
      let* release = release_block accu this in
      return (
        load_rest_code @
        release @
        load_block (vars @ rest_ctx) this (Offset.fields_per_block - 1) @
        load_binders vars rest_ctx this (Offset.fields_per_block - 1))

(** Load environment: loads all values from linked blocks.
    xs: binders to load (become new prefix of context)
    as_ctx: tail context
    After load, context is xs @ as_ctx (xs at HEAD, as_ctx at TAIL).
    Used by both codeClause and codeMethod - they differ only in what xs and as_ctx are. *)
let load (xs: ctx) (as_ctx: ctx) : code state =
  match xs with
    [] -> return []
  | _ ->
      let vars = take Offset.fields_per_block xs in
      let rest = drop Offset.fields_per_block xs in
      let rest_ctx = rest @ as_ctx in
      let this = fresh_location1 rest_ctx in
      let accu = fresh_location2 rest_ctx in
      let* load_rest_code = load_rest rest as_ctx in
      let* release = release_block accu this in
      return (
        load_rest_code @
        release @
        load_binders vars rest_ctx this Offset.fields_per_block)

(* ========================================================================= *)
(* Branch Table Generation                                                   *)
(* ========================================================================= *)

let rec code_table (n: int) (lab_base: int) (lab_branch: int) : code =
  if n = 0 then []
  else
    B ("lab" ^ string_of_int lab_base ^ "b" ^ string_of_int lab_branch) ::
    code_table (n - 1) lab_base (lab_branch + 1)

(* ========================================================================= *)
(* Substitution Handling                                                     *)
(* ========================================================================= *)

let occurrences (subst: (var * var) list) (src: var) : var list =
  List.filter_map (fun (tgt, s) ->
    if Ident.equal s src then Some tgt else None
  ) subst

let transpose (src_ctx: ctx) (subst: (var * var) list) 
    : (var * var list) list =
  List.map (fun (v, _) -> (v, occurrences subst v)) src_ctx

let update_reference_count (r: Register.t) (n: int) : code state =
  if n = 0 then erase_block r
  else if n = 1 then return []
  else share_block_n r (n - 1)

let rec code_weakening_contraction
    (ctx: ctx) (usage: (var * var list) list) : code state =
  match ctx, usage with
    [], [] -> return []
  | (v, ct) :: rest_ctx, (_, targets) :: rest_usage ->
      if is_ext_type ct then
        code_weakening_contraction rest_ctx rest_usage
      else
        let* update =
          update_reference_count (symbol_location1 ctx v) (List.length targets)
        in
        let* rest = code_weakening_contraction rest_ctx rest_usage in
        return (update @ rest)
  | _ -> failwith "context and usage list length mismatch"

let connections (src_ctx: ctx) (tgt_ctx: ctx) (usage: (var * var list) list)
    : Register.t list list =
  let graph = Array.make 32 [] in
  List.iter2 (fun (v, ct) (_, targets) ->
    let src_r1 = symbol_location1 src_ctx v in
    let src_r2 = symbol_location2 src_ctx v in
    let tgt_regs1 = List.map (symbol_location1 tgt_ctx) targets in
    let tgt_regs2 = List.map (symbol_location2 tgt_ctx) targets in
    if is_ext_type ct then
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

type label_map = int Path.tbl

let make_label_map (defs: checked_definition Path.tbl) : label_map =
  let lst = Path.to_list defs in
  let indexed = List.mapi (fun i (p, _) -> (p, i)) lst in
  Path.of_list indexed

let label_index (lmap: label_map) (p: Path.t) : int =
  match Path.find_opt p lmap with
    Some i -> i
  | None -> failwith ("undefined label: " ^ Path.name p)

(* ========================================================================= *)
(* Direct Branch Optimization                                                *)
(* ========================================================================= *)
(* For definitions that start with CSwitch (like foo.mono functions), we emit
   direct-entry labels that skip the switch dispatch. When we see:
     let v = ctor(args); jump foo.mono(v)
   we can instead jump directly to foo.mono's branch for ctor, passing args
   directly instead of packing them into a constructor and unpacking. *)

(** Info about a definition that starts with CSwitch *)
type switch_def_info =
  { dec: dec                        (* The type being switched on *)
  ; tail_ctx_size: int              (* Size of context after scrutinee *)
  ; branch_xtors: Path.t list       (* List of xtors handled by branches *)
  }

type switch_defs_map = switch_def_info Path.tbl

(** Build map of definitions that start with CSwitch *)
let make_switch_defs_map (defs: checked_definition Path.tbl) : switch_defs_map =
  let extract_switch_info (def: checked_definition) : switch_def_info option =
    match def.body with
      CSwitch { dec; tail_ctx; branches; _ } ->
        Some { dec
             ; tail_ctx_size = List.length tail_ctx
             ; branch_xtors = List.map (fun b -> b.xtor) branches
             }
    | _ -> None
  in
  Path.of_list (List.filter_map (fun (p, def) ->
    match extract_switch_info def with
      Some info -> Some (p, info)
    | None -> None
  ) (Path.to_list defs))

(** Direct-entry label for definition N, branch with original_index I *)
let direct_entry_label (def_idx: int) (branch_idx: int) : string =
  "lab" ^ string_of_int def_idx ^ "d" ^ string_of_int branch_idx

(* ========================================================================= *)
(* Main Code Generation                                                      *)
(* ========================================================================= *)

(*
  Compile a checked command to AARCH64 assembly.
  The context is embedded in each AST node, so no manual threading needed.
  
  switch_defs: map of definitions that start with CSwitch, used for
  direct-branch optimization.
*)

let rec code_command (lmap: label_map) (switch_defs: switch_defs_map)
    (cmd: checked_command) : code state =
  match cmd with
  (* Substitute: explicit structural rules *)
    CSubstitute { src_ctx; mapping; tgt_ctx; body } ->
      let usage = transpose src_ctx mapping in
      let* weaken_contract = code_weakening_contraction src_ctx usage in
      let graph = connections src_ctx tgt_ctx usage in
      let exchange = code_exhange graph in
      let* rest = code_command lmap switch_defs body in
      return (weaken_contract @ exchange @ rest)

  (* Jump to label - move args to target positions then branch *)
  | CJump { ctx; label; args } ->
      let idx = label_index lmap label in
      let num_args = List.length args in
      (* Move args from current positions to target positions.
        args[i] should go to position (num_args - 1 - i) from end.
        We build a graph of register moves and use exchange algorithm. *)
      let graph = Array.make 32 [] in
      List.iteri (fun i (arg, ct) ->
        let src_r2 = symbol_location2 ctx arg in
        let tgt_pos = num_args - 1 - i in
        let tgt_r2 = Register.mk (Register.reserved + 2 * tgt_pos + 1) in
        if is_ext_type ct then
          graph.(Register.to_int src_r2) <- [tgt_r2]
        else begin
          let src_r1 = symbol_location1 ctx arg in
          let tgt_r1 = Register.mk (Register.reserved + 2 * tgt_pos) in
          graph.(Register.to_int src_r1) <- [tgt_r1];
          graph.(Register.to_int src_r2) <- [tgt_r2]
        end
      ) args;
      let exchange = code_exhange (Array.to_list graph) in
      return (exchange @ [B ("lab" ^ string_of_int idx)])

  (* Let: construct data value 
     
    OPTIMIZATION: If body is `jump target(v)` where v is the just-constructed
    value and target starts with a switch on this type, we can jump directly
    to target's branch for this xtor, passing args directly. This eliminates:
    - Storing args to block
    - Setting tag
    - Loading args from block in target's branch *)
  | CLet { ctx; v; v_typ; dec; xtor; args; tail_ctx; body } ->
      (* Check for direct-branch optimization pattern:
        body = CJump { label = target; args = [(v, _)] }
        where target is in switch_defs and handles xtor *)
      let try_direct_branch () =
        match body with
          CJump { label = target; args = jump_args; _ } ->
            (match jump_args with
              [(jump_v, _)] when Ident.equal jump_v v ->
                (* Found pattern: let v = xtor(args); jump target(v) *)
                (match Path.find_opt target switch_defs with
                  Some info when List.exists (Path.equal xtor) info.branch_xtors ->
                    (* Target starts with switch and has branch for this xtor *)
                    let target_idx = label_index lmap target in
                    let xtor_original_idx =
                      match List.find_opt (fun (x: xtor) ->
                        Path.equal x.name xtor
                      ) dec.xtors
                      with
                        Some x -> x.original_index
                      | None -> 0
                    in
                    Some (target_idx, xtor_original_idx)
                | _ -> None)
            | _ -> None)
        | _ -> None
      in
      (match try_direct_branch () with
        Some (target_idx, branch_idx) ->
          (* OPTIMIZATION: Jump directly to target's branch.
            Move args to branch parameter positions and branch. *)
          let num_args = List.length args in
          let graph = Array.make 32 [] in
          List.iteri (fun i ((arg, ct): var * chiral_typ) ->
            let src_r2 = symbol_location2 ctx arg in
            let tgt_pos = num_args - 1 - i in
            let tgt_r2 = Register.mk (Register.reserved + 2 * tgt_pos + 1) in
            if is_ext_type ct then
              graph.(Register.to_int src_r2) <- [tgt_r2]
            else begin
              let src_r1 = symbol_location1 ctx arg in
              let tgt_r1 = Register.mk (Register.reserved + 2 * tgt_pos) in
              graph.(Register.to_int src_r1) <- [tgt_r1];
              graph.(Register.to_int src_r2) <- [tgt_r2]
            end
          ) args;
          let exchange = code_exhange (Array.to_list graph) in
          return (exchange @ [B (direct_entry_label target_idx branch_idx)])
      | None ->
          (* Normal path: construct the value *)
          let new_ctx = (v, v_typ) :: tail_ctx in
          let tag_reg = symbol_location2 new_ctx v in
          (* Use original_index to get consistent tag across filtered/unfiltered xtor lists *)
          let xtor_idx = 
            let rec find_xtor = function
                [] -> failwith
                  (Printf.sprintf "Compilation error: xtor '%s' not found!\n" (Path.name xtor))
              | (y: xtor) :: _ when Path.equal y.name xtor -> y.original_index
              | _ :: rest -> find_xtor rest
            in find_xtor dec.xtors
          in
          (* Store args with ctx as source context, tail_ctx as the "as" context *)
          let* stores = store args ctx tail_ctx in
          let* rest = code_command lmap switch_defs body in
          return (
            stores @
            MOVI (tag_reg, Int64.of_int (Offset.jump_length xtor_idx)) ::
            rest))

  (* Switch: pattern match on data 
     
    IMPORTANT: Tags are based on original_index (for consistent GADT handling).
    The jump table must be sparse - branches are at their original_index positions,
    not sequential. This ensures tag values match jump table offsets.
    
    For destination-passed values (from alloc), the tag is in memory, not in
    the register. We detect this via ALLOC_SENTINEL in loc2. *)
  | CSwitch { ctx; v; dec; tail_ctx; branches; _ } ->
      let tag_reg = symbol_location2 ctx v in
      let block_reg = symbol_location1 ctx v in
      let* base_lab = fresh_label in
      let* load_lab = fresh_label in
      (* Look up original_index for each branch's xtor *)
      let get_original_index xtor_path =
        match List.find_opt (fun (x: xtor) -> Path.equal x.name xtor_path) dec.xtors with
          Some x -> x.original_index
        | None -> 0  (* fallback - shouldn't happen *)
      in
      (* Find max original_index to size the jump table *)
      let max_idx = List.fold_left (fun acc branch ->
        max acc (get_original_index branch.xtor)
      ) 0 branches in
      (* Create sparse jump table: entries at original_index positions *)
      let* branch_codes =
        code_clauses_sparse lmap switch_defs tail_ctx branches base_lab get_original_index
      in
      (* Check if tag is ALLOC_SENTINEL - if so, load from memory *)
      let sentinel_check =
        CMPI (tag_reg, -1) ::
        BEQ ("lab" ^ string_of_int load_lab) ::
        []
      in
      let load_from_memory =
        LAB ("lab" ^ string_of_int load_lab) ::
        (* Check if field1(0) is non-zero - indicates fill at slot 0, need indirection *)
        LDR (Register.temp, block_reg, Offset.field1 0) ::
        CMPI (Register.temp, 0) ::
        BEQ ("lab" ^ string_of_int load_lab ^ "direct") ::
        (* Fill case: follow pointer at field1(0) to get actual data block *)
        MOVR (block_reg, Register.temp) ::
        LAB ("lab" ^ string_of_int load_lab ^ "direct") ::
        (* Load tag from the data block's data_tag *)
        LDR (tag_reg, block_reg, Offset.data_tag) ::
        []
      in
      return (
        sentinel_check @
        ADR (Register.temp, "lab" ^ string_of_int base_lab) ::
        (if max_idx = 0 then []
         else ADD (Register.temp, Register.temp, tag_reg) :: []) @
        BR Register.temp ::
        load_from_memory @
        ADR (Register.temp, "lab" ^ string_of_int base_lab) ::
        (if max_idx = 0 then []
         else ADD (Register.temp, Register.temp, tag_reg) :: []) @
        BR Register.temp ::
        LAB ("lab" ^ string_of_int base_lab) ::
        (if max_idx = 0 then []
         else code_table (max_idx + 1) base_lab 0) @
        List.concat branch_codes)

  (* New: create codata value 
     
    IMPORTANT: Tags are based on original_index (for consistent GADT handling).
    The jump table must be sparse - methods are at their original_index positions,
    not sequentially packed. This mirrors CSwitch's sparse table. *)
  | CNew { ctx; k; k_typ; dec; branches; body; _ } ->
      (* ctx is captured, new_ctx = (k,k_typ) :: ctx *)
      let new_ctx = (k, k_typ) :: ctx in
      let tab_reg = symbol_location2 new_ctx k in
      (* Look up original_index for each branch's xtor *)
      let get_original_index xtor_path =
        match List.find_opt (fun (x: xtor) -> Path.equal x.name xtor_path) dec.xtors with
          Some x -> x.original_index
        | None -> 0
      in
      (* Find max original_index to size the jump table *)
      let max_idx = List.fold_left (fun acc branch ->
        max acc (get_original_index branch.xtor)
      ) 0 branches in
      (* Store ctx (the captured environment).
        src_ctx = ctx (where values are now)
        as_ctx = ctx (so block ends up at fresh_location1(ctx) = k's position) *)
      let* stores = store ctx ctx ctx in
      let* base_lab = fresh_label in
      let* rest = code_command lmap switch_defs body in
      (* Create sparse jump table: entries at original_index positions *)
      let* branch_codes =
        code_methods_sparse lmap switch_defs ctx branches base_lab get_original_index
      in
      return (
        stores @
        ADR (tab_reg, "lab" ^ string_of_int base_lab) ::
        rest @
        LAB ("lab" ^ string_of_int base_lab) ::
        (if max_idx < 1 then []
         else code_table (max_idx + 1) base_lab 0) @
        List.concat branch_codes)

  (* Invoke: call codata method 
     
    Args are already at tail positions (0..n-1) from substitution.
    We just move block pointer and branch.
     
    IMPORTANT: Use original_index for consistent GADT handling.
     
    Method expects:
    - Block at fresh_location1(args) = X(reserved + 2*len(args))
    - Args already in place at positions 0..n-1 from end *)
  | CInvoke { ctx; v; dec; xtor; args; _ } ->
      let tab_reg = symbol_location2 ctx v in
      let block_reg = symbol_location1 ctx v in
      let this_reg = fresh_location1 args in  (* Block goes here *)
      (* Use original_index for consistent tag across filtered/unfiltered xtor lists *)
      let xtor_idx = 
        match List.find_opt (fun (y: xtor) -> Path.equal y.name xtor) dec.xtors with
          Some y -> y.original_index
        | None -> 0
      in
      (* Find max original_index to determine if jump table is needed *)
      let max_idx = List.fold_left (fun acc (y: xtor) ->
        max acc y.original_index
      ) 0 dec.xtors in
      (* Args are already in place at positions 0..n-1.
        We just need to move block pointer and branch.
        Use exchange graph to safely handle overlapping moves. *)
      let graph = Array.make 32 [] in
      (* tab_reg -> X2 (Register.temp) - save code pointer for branch *)
      if not (Register.equal tab_reg Register.temp) then
        graph.(Register.to_int tab_reg) <- Register.temp :: graph.(Register.to_int tab_reg);
      (* block_reg -> this_reg - move block pointer to where method expects it *)
      if not (Register.equal block_reg this_reg) then
        graph.(Register.to_int block_reg) <- this_reg :: graph.(Register.to_int block_reg);
      let substitute = code_exhange (Array.to_list graph) in
      return (
        substitute @
        (if max_idx < 1 then
          BR Register.temp :: []
        else
          ADDI (Register.temp, Register.temp, Offset.jump_length xtor_idx) ::
          BR Register.temp :: []))

  (* Axiom: cut between producer and consumer
     
    Exactly like CInvoke but for Cns (Ext Int) - a single-method codata.
    
    After CSubstitute with [k; v] ordering:
    - k at position 1 → r1 = X5 (this), r2 = X6 (code)  
    - v at position 0 → r2 = X4 (arg)
    
    Everything is already in place! Just save code pointer and branch. *)
  | CAxiom { ctx; k; _ } ->
      let k_code_reg = symbol_location2 ctx k in
      return (
        MOVR (Register.temp, k_code_reg) ::   (* Save code ptr to X2 *)
        BR Register.temp :: [])               (* Branch via X2 *)

  (* Literal: create integer value *)
  | CLit { ctx; n; v; body } ->
      let new_ctx = (v, Prd (Unr, Ext Int)) :: ctx in
      let* rest = code_command lmap switch_defs body in
      return (
        MOVI (symbol_location2 new_ctx v, n) ::
        rest)

  (* NewInt: create integer consumer (continuation)
     
    - Block at fresh_location1(tail_ctx) where tail_ctx = [param]
    - Arg incoming at X4 (r1 slot, safe since method saves before loading)
    
    k uses two registers just like CNew codata:
    - symbol_location1(k_ctx, k) = block pointer (captured environment)
    - symbol_location2(k_ctx, k) = code address *)
  | CNewInt { ctx; k; param; branch_body; cont_body } ->
      let k_ctx = (k, Cns (Lin, Ext Int)) :: ctx in
      let k_block_reg = symbol_location1 k_ctx k in  (* r1 = block pointer *)
      let k_code_reg = symbol_location2 k_ctx k in   (* r2 = code address *)
      (* Arg incoming at X4, matching CAxiom's convention *)
      let arg_incoming_reg = Register.mk (Register.reserved + 1) in (* X4 *)
      (* The arg register where method expects it.
        Method context after load = ctx @ tail_ctx = captured @ [param].
        param_ctx must match this order: ctx @ [param]. *)
      let param_ctx = ctx @ [(param, Prd (Unr, Ext Int))] in
      let arg_expected_reg = symbol_location2 param_ctx param in
      (* tail_ctx for block pointer calculation = [param] *)
      let tail_ctx = [(param, Prd (Unr, Ext Int))] in
      (* Store ctx as captured environment *)
      let* stores = store ctx ctx ctx in
      let* base_lab = fresh_label in
      let* cont = code_command lmap switch_defs cont_body in
      (* Method: load captured vars from block. After load, context is ctx @ tail_ctx. *)
      let* loads = load ctx tail_ctx in
      let* method_body = code_command lmap switch_defs branch_body in
      (* After stores, block pointer is at fresh_location1 ctx.
        Set k's two registers: r1 = block, r2 = code address *)
      let this_reg = fresh_location1 ctx in
      return (
        stores @
        (* k_block_reg = block pointer *)
        MOVR (k_block_reg, this_reg) ::
        (* k_code_reg = code address (direct, not stored in block) *)
        ADR (k_code_reg, "lab" ^ string_of_int base_lab) ::
        cont @
        LAB ("lab" ^ string_of_int base_lab) ::
        (* Move incoming arg directly to expected position (above load range) *)
        MOVR (arg_expected_reg, arg_incoming_reg) ::
        loads @
        method_body)

  (* Add: integer addition *)
  | CAdd { ctx; x; y; v; body } ->
      let new_ctx = (v, Prd (Unr, Ext Int)) :: ctx in
      let* rest = code_command lmap switch_defs body in
      return (
        ADD (symbol_location2 new_ctx v, symbol_location2 ctx x, 
             symbol_location2 ctx y) ::
        rest)

  (* Sub: integer subtraction *)
  | CSub { ctx; x; y; v; body } ->
      let new_ctx = (v, Prd (Unr, Ext Int)) :: ctx in
      let x_reg = symbol_location2 ctx x in
      let y_reg = symbol_location2 ctx y in
      let v_reg = symbol_location2 new_ctx v in
      let* rest = code_command lmap switch_defs body in
      return (
        MOVI (Register.temp, 1L) ::
        MSUB (v_reg, Register.temp, y_reg, x_reg) ::
        rest)

  (* Mul: integer multiplication *)
  | CMul { ctx; x; y; v; body } ->
      let new_ctx = (v, Prd (Unr, Ext Int)) :: ctx in
      let* rest = code_command lmap switch_defs body in
      return (
        MUL (symbol_location2 new_ctx v, symbol_location2 ctx x, 
             symbol_location2 ctx y) ::
        rest)

  (* Div: integer division *)
  | CDiv { ctx; x; y; v; body } ->
      let new_ctx = (v, Prd (Unr, Ext Int)) :: ctx in
      let* rest = code_command lmap switch_defs body in
      return (
        SDIV (symbol_location2 new_ctx v, symbol_location2 ctx x, 
              symbol_location2 ctx y) ::
        rest)

  (* Rem: integer remainder (x % y = x - (x / y) * y) *)
  | CRem { ctx; x; y; v; body } ->
      let new_ctx = (v, Prd (Unr, Ext Int)) :: ctx in
      let x_reg = symbol_location2 ctx x in
      let y_reg = symbol_location2 ctx y in
      let v_reg = symbol_location2 new_ctx v in
      let* rest = code_command lmap switch_defs body in
      return (
        SDIV (Register.temp, x_reg, y_reg) ::  (* temp = x / y *)
        MSUB (v_reg, Register.temp, y_reg, x_reg) ::  (* v = x - temp*y *)
        rest)

  (* Ifz: conditional on zero *)
  | CIfz { ctx; v; then_cmd; else_cmd } ->
      let v_reg = symbol_location2 ctx v in
      let* lab = fresh_label in
      let label = "lab" ^ string_of_int lab in
      let* else_code = code_command lmap switch_defs else_cmd in
      let* then_code = code_command lmap switch_defs then_cmd in
      return (
        CMPI (v_reg, 0) ::
        BEQ label ::
        else_code @
        LAB label ::
        then_code)

  (* Destination primitives *)

  (* Alloc: allocate uninitialized value and destination.
    After alloc, context = (d, dest(ty))::(v, ty)::ctx
    - v points to the allocated block (loc1=block, loc2=ALLOC_SENTINEL)
    - d points to where v's data should be filled (loc1=block, loc2=offset)
    
    The ALLOC_SENTINEL (-1) marks v as a "destination-passed value" whose
    actual tag is in memory at v.loc1 + field2(0), not in v.loc2. *)
  | CAlloc { ctx; v; d; ty; body } ->
      let v_typ = Prd (Unr, ty) in
      let d_typ = Prd (Lin, Dest ty) in
      let new_ctx = (d, d_typ) :: (v, v_typ) :: ctx in
      (* Acquire block for v's data *)
      let accu = fresh_location2 ctx in
      let this = fresh_location1 ctx in
      let* acquire = acquire_block accu this in
      (* v's registers in new context *)
      let v_loc1 = symbol_location1 new_ctx v in
      let v_loc2 = symbol_location2 new_ctx v in
      (* d's registers - d = (block, 0) meaning base destination *)
      let d_loc1 = symbol_location1 new_ctx d in
      let d_loc2 = symbol_location2 new_ctx d in
      let* rest = code_command lmap switch_defs body in
      let is_ext = match ty with Ext _ -> true | _ -> false in
      if is_ext then
        (* For external types, v uses only loc2 *)
        return (
          acquire @
          MOVR (d_loc1, this) ::
          MOVI (d_loc2, 0L) ::
          rest)
      else
        return (
          acquire @
          MOVR (v_loc1, this) ::  (* v points to block *)
          MOVI (v_loc2, Offset.alloc_sentinel) ::  (* sentinel: tag in memory *)
          MOVR (d_loc1, this) ::  (* d points to same block *)
          MOVI (d_loc2, 0L) ::    (* base slot 0 *)
          rest)

  (* Fill: fill destination d with value v.
    - Read destination (block, slot) from d
    - Store v's data into block at slot *)
  | CFill { ctx; d; v; ty; body; _ } ->
      let d_loc1 = symbol_location1 ctx d in
      let d_loc2 = symbol_location2 ctx d in
      let v_loc1 = symbol_location1 ctx v in
      let v_loc2 = symbol_location2 ctx v in
      (* Use scratch register for address computation *)
      let scratch = fresh_location1 ctx in
      let is_ext = match ty with Ext _ -> true | _ -> false in
      let* rest = code_command lmap switch_defs body in
      let* slot0_lab = fresh_label in
      let* done_lab = fresh_label in
      if is_ext then
        (* External: store just the value (loc2) *)
        return (
          (* Compute offset: d_loc2 holds slot number, multiply by 16 for field offset *)
          MOVI (Register.temp, 16L) ::
          MUL (Register.temp, d_loc2, Register.temp) ::
          ADDI (Register.temp, Register.temp, Offset.field2 0) ::
          ADD (Register.temp, d_loc1, Register.temp) ::
          STR (v_loc2, Register.temp, 0) ::
          rest)
      else
        (* Non-external: store both block ptr and tag
           For slot 0 (root destination from alloc), store tag at data_tag (offset 8)
           so that CSwitch can find it when checking ALLOC_SENTINEL.
           For other slots (nested destinations), store at field1/field2 offsets.
           
           IMPORTANT: If v_loc2 is ALLOC_SENTINEL, the value was DSP-constructed
           and already has its tag at data_tag. For slot 0, don't overwrite it.
           For nested slots, we need to copy the actual tag from v_loc1's data_tag. *)
        let* skip_tag_lab = fresh_label in
        let* nested_sentinel_lab = fresh_label in
        return (
          (* Check if slot 0 *)
          CMPI (d_loc2, 0) ::
          BEQ ("lab" ^ string_of_int slot0_lab) ::
          
          (* Non-zero slot: store at field1/field2 offsets *)
          MOVI (Register.temp, 16L) ::
          MUL (Register.temp, d_loc2, Register.temp) ::
          (* Store loc1 (block ptr) at field1 offset *)
          ADDI (scratch, Register.temp, Offset.field1 0) ::
          ADD (scratch, d_loc1, scratch) ::
          STR (v_loc1, scratch, 0) ::
          (* Prepare to store tag at field2 offset *)
          ADDI (scratch, Register.temp, Offset.field2 0) ::
          ADD (scratch, d_loc1, scratch) ::
          (* Check if v_loc2 is ALLOC_SENTINEL (DSP value) *)
          CMPI (v_loc2, -1) ::
          BEQ ("lab" ^ string_of_int nested_sentinel_lab) ::
          (* Regular value: store v_loc2 directly *)
          STR (v_loc2, scratch, 0) ::
          B ("lab" ^ string_of_int done_lab) ::
          (* DSP value: load tag from v_loc1's data_tag and store it *)
          LAB ("lab" ^ string_of_int nested_sentinel_lab) ::
          LDR (Register.temp, v_loc1, Offset.data_tag) ::
          STR (Register.temp, scratch, 0) ::
          B ("lab" ^ string_of_int done_lab) ::
          
          (* Slot 0: store block ptr at field1(0), tag at target block's data_tag *)
          LAB ("lab" ^ string_of_int slot0_lab) ::
          STR (v_loc1, d_loc1, Offset.field1 0) ::   (* block ptr at offset 16 *)
          (* Only store tag if not ALLOC_SENTINEL (DSP value already has tag set) *)
          CMPI (v_loc2, -1) ::
          BEQ ("lab" ^ string_of_int skip_tag_lab) ::
          STR (v_loc2, v_loc1, Offset.data_tag) ::   (* tag in target block at offset 8 *)
          LAB ("lab" ^ string_of_int skip_tag_lab) ::
          
          LAB ("lab" ^ string_of_int done_lab) ::
          rest)

  (* Unfold: create subdestinations for constructor arguments.
    - d is destination for type T 
    - xtor is constructor with argument types τi
    - xi_vars become destinations for each argument slot
    Also sets tag on the parent value. 
    
    For nested destinations (slot != 0), this is a sum-typed field like list's tail.
    We need to allocate a new block for the nested value and store a pointer to it
    in the parent's slot. *)
  | CUnfold { ctx; xi_vars; d; dec; xtor; tail_ctx; body } ->
      (* d at head of context *)
      let d_loc1 = symbol_location1 ctx d in
      let d_loc2 = symbol_location2 ctx d in
      (* Find xtor for tag *)
      let xtor_data = match List.find_opt (fun (x: xtor) ->
          Path.equal x.name xtor) dec.xtors with
        | Some x -> x
        | None -> failwith ("xtor not found in unfold: " ^ Path.name xtor)
      in
      let tag = xtor_data.original_index in
      (* Context after unfold: xi_vars @ tail_ctx *)
      let new_ctx = xi_vars @ tail_ctx in
      (* 
        For nested destinations (d_loc2 != 0), we need to:
        1. Allocate a new block for the nested value
        2. Store pointer to new block in parent's slot d_loc2
        3. Use the new block (at slot 0) for sub-destinations and tag
        
        For root destinations (d_loc2 == 0), we use the existing block directly.
        
        We use 'this' register to hold the block pointer for subdestinations.
        In root case: copy d_loc1 into this. In nested case: acquire puts block in this.
      *)
      (* Registers for acquire_block *)
      let accu = fresh_location2 ctx in
      let this = fresh_location1 ctx in
      let* acquire = acquire_block accu this in
      (* After acquire, 'this' has the new block pointer *)
      
      let tag_offset = Offset.data_tag in
      let* rest = code_command lmap switch_defs body in
      
      (* Set up subdestinations using 'this' as the block pointer *)
      let setup_code = List.mapi (fun i (xi, _ct) ->
        let xi_loc1 = symbol_location1 new_ctx xi in
        let xi_loc2 = symbol_location2 new_ctx xi in
        let slot = Offset.fields_per_block - 1 - i in
        [MOVR (xi_loc1, this);
         MOVI (xi_loc2, Int64.of_int slot)]
      ) xi_vars |> List.concat in
      
      (* Nested case: allocate, link to parent *)
      let nested_setup =
        acquire @
        (* Store pointer to new block in parent's slot (field1 part) *)
        MOVI (Register.temp, 16L) ::
        MUL (Register.temp, d_loc2, Register.temp) ::
        (* Store block pointer at field1 offset *)
        ADDI (accu, Register.temp, Offset.field1 0) ::
        ADD (accu, d_loc1, accu) ::
        STR (this, accu, 0) :: (* parent[slot].field1 = new_block *)
        (* Store ALLOC_SENTINEL at field2 offset so CSwitch knows tag is in memory *)
        ADDI (accu, Register.temp, Offset.field2 0) ::
        ADD (accu, d_loc1, accu) ::
        MOVI (Register.temp, Offset.alloc_sentinel) ::
        STR (Register.temp, accu, 0) :: (* parent[slot].field2 = SENTINEL *)
        []
      in
      
      (* Root case: copy d_loc1 into this *)
      let root_setup =
        MOVR (this, d_loc1) ::
        []
      in
      
      (* Common code after setup: store tag, zero unused slots, and set up subdests *)
      let num_subdests = List.length xi_vars in
      (* Subdests go to slots (fields_per_block-1) down to (fields_per_block-num_subdests)
         So unused slots are 0 to (fields_per_block-1-num_subdests) = (fields_per_block-num_subdests-1) slots *)
      let first_unused_slot = Offset.fields_per_block - num_subdests - 1 in
      let num_unused_slots = first_unused_slot + 1 in
      let common_code =
        (* Store tag at this + tag_offset *)
        MOVI (Register.temp, Int64.of_int (Offset.jump_length tag)) ::
        STR (Register.temp, this, tag_offset) ::
        (* Zero unused slots (below the subdestinations) *)
        store_zeroes this num_unused_slots @
        setup_code @
        rest
      in
      
      (* Branch based on whether d_loc2 == 0 (root) or != 0 (nested) *)
      let* lab_root = fresh_label in
      let* lab_common = fresh_label in
      return (
        CMPI (d_loc2, 0) ::
        BEQ ("lab" ^ string_of_int lab_root) ::
        (* Nested case: d_loc2 != 0, falls through here *)
        nested_setup @
        [B ("lab" ^ string_of_int lab_common);
         LAB ("lab" ^ string_of_int lab_root)] @
        (* Root case: d_loc2 == 0 *)
        root_setup @
        [LAB ("lab" ^ string_of_int lab_common)] @
        (* Common code for both cases *)
        common_code
      )

  (* Return: final result *)
  | CRet { ctx; v; _ } ->
      return (
        MOVR (Register.return2, symbol_location2 ctx v) ::
        B "cleanup" :: [])

  (* End: terminal *)
  | CEnd _ ->
      return (B "cleanup" :: [])

(** Compile a clause (branch of switch).
    tail_ctx: context after consuming scrutinee
    branch.args: binders introduced by this branch
    branch.branch_ctx = branch.args @ tail_ctx *)
and code_clause (lmap: label_map) (switch_defs: switch_defs_map) (tail_ctx: ctx) 
    (branch: checked_branch) : code state =
  (* Load args into HEAD positions, tail_ctx stays at TAIL *)
  let* loads = load branch.args tail_ctx in
  let* body_code = code_command lmap switch_defs branch.body in
  return (loads @ body_code)

and code_clauses (lmap: label_map) (switch_defs: switch_defs_map) (tail_ctx: ctx) 
    (branches: checked_branch list) (base_lab: int) (branch_idx: int) 
    : code list state =
  match branches with
    [] -> return []
  | branch :: rest ->
      let* clause = code_clause lmap switch_defs tail_ctx branch in
      let* rest_clauses =
        code_clauses lmap switch_defs tail_ctx rest base_lab (branch_idx + 1) in
      let labeled = 
        LAB ("lab" ^ string_of_int base_lab ^ "b" ^ string_of_int branch_idx) :: 
        clause in
      return (labeled :: rest_clauses)

(** Compile clauses with sparse indexing based on original_index.
    Used for CSwitch when xtors may be filtered due to GADT instantiation.
    Each branch is labeled with its xtor's original_index, not sequential index. *)
and code_clauses_sparse (lmap: label_map) (switch_defs: switch_defs_map) (tail_ctx: ctx) 
    (branches: checked_branch list) (base_lab: int)
    (get_original_index: Path.t -> int)
    : code list state =
  match branches with
    [] -> return []
  | branch :: rest ->
      let* clause = code_clause lmap switch_defs tail_ctx branch in
      let original_idx = get_original_index branch.xtor in
      let* rest_clauses =
        code_clauses_sparse lmap switch_defs tail_ctx rest base_lab get_original_index in
      let labeled = 
        LAB ("lab" ^ string_of_int base_lab ^ "b" ^ string_of_int original_idx) :: 
        clause in
      return (labeled :: rest_clauses)

(** Compile a method (branch of new/codata).
    captured_ctx: the context captured when creating the codata
    branch.args: arguments passed to this method
    branch.branch_ctx = captured_ctx @ args *)
and code_method (lmap: label_map) (switch_defs: switch_defs_map) (captured_ctx: ctx) 
    (branch: checked_branch) : code state =
  let args = branch.args in
  let* loads = load captured_ctx args in
  let* body_code = code_command lmap switch_defs branch.body in
  return (loads @ body_code)

and code_methods (lmap: label_map) (switch_defs: switch_defs_map) (captured_ctx: ctx)
    (branches: checked_branch list) (base_lab: int) (branch_idx: int) 
    : code list state =
  match branches with
    [] -> return []
  | branch :: rest ->
      let* method_code = code_method lmap switch_defs captured_ctx branch in
      let* rest_methods =
        code_methods lmap switch_defs captured_ctx rest base_lab (branch_idx + 1) in
      let labeled =
        LAB ("lab" ^ string_of_int base_lab ^ "b" ^ string_of_int branch_idx) ::
        method_code in
      return (labeled :: rest_methods)

(** Compile methods with sparse indexing based on original_index.
    Used for CNew when xtors may be filtered due to GADT instantiation.
    Each method is labeled with its xtor's original_index, not sequential index. *)
and code_methods_sparse (lmap: label_map) (switch_defs: switch_defs_map) (captured_ctx: ctx) 
    (branches: checked_branch list) (base_lab: int)
    (get_original_index: Path.t -> int)
    : code list state =
  match branches with
    [] -> return []
  | branch :: rest ->
      let* method_code = code_method lmap switch_defs captured_ctx branch in
      let original_idx = get_original_index branch.xtor in
      let* rest_methods =
        code_methods_sparse lmap switch_defs captured_ctx rest base_lab get_original_index in
      let labeled = 
        LAB ("lab" ^ string_of_int base_lab ^ "b" ^ string_of_int original_idx) :: 
        method_code in
      return (labeled :: rest_methods)

(* ========================================================================= *)
(* Top-Level Compilation                                                     *)
(* ========================================================================= *)

(** Compile a definition, emitting direct-entry labels for switch-at-entry defs *)
let compile_def (lmap: label_map) (switch_defs: switch_defs_map) 
    (def_idx: int) (def: checked_definition) : code state =
  match def.body with
    (* Definition starts with CSwitch - emit direct-entry labels for each branch *)
    CSwitch { ctx; v; dec; tail_ctx; branches; _ } ->
      let tag_reg = symbol_location2 ctx v in
      let block_reg = symbol_location1 ctx v in
      let* base_lab = fresh_label in
      let* load_lab = fresh_label in
      let get_original_index xtor_path =
        match List.find_opt (fun (x: xtor) ->
          Path.equal x.name xtor_path
        ) dec.xtors with
          Some x -> x.original_index
        | None -> 0
      in
      let max_idx = List.fold_left (fun acc branch ->
        max acc (get_original_index branch.xtor)
      ) 0 branches in
      (* Compile branches with direct-entry labels *)
      let* branch_codes = 
        let rec compile_branches = function
            [] -> return []
          | branch :: rest ->
              let original_idx = get_original_index branch.xtor in
              let* loads = load branch.args tail_ctx in
              let* body_code = code_command lmap switch_defs branch.body in
              let* rest_branches = compile_branches rest in
              (* Normal entry label, then load, then direct-entry label, then body *)
              let labeled = 
                LAB ("lab" ^ string_of_int base_lab ^ "b" ^ string_of_int original_idx) ::
                loads @
                LAB (direct_entry_label def_idx original_idx) ::
                body_code in
              return (labeled :: rest_branches)
        in compile_branches branches
      in
      (* Sentinel check and load_from_memory for ALLOC_SENTINEL values
         (same as in code_command's CSwitch case) *)
      let sentinel_check =
        CMPI (tag_reg, -1) ::
        BEQ ("lab" ^ string_of_int load_lab) ::
        []
      in
      let load_from_memory =
        LAB ("lab" ^ string_of_int load_lab) ::
        (* Check if field1(0) is non-zero - indicates fill at slot 0, need indirection *)
        LDR (Register.temp, block_reg, Offset.field1 0) ::
        CMPI (Register.temp, 0) ::
        BEQ ("lab" ^ string_of_int load_lab ^ "direct") ::
        (* Fill case: follow pointer at field1(0) to get actual data block *)
        MOVR (block_reg, Register.temp) ::
        LAB ("lab" ^ string_of_int load_lab ^ "direct") ::
        (* Load tag from the data block's data_tag *)
        LDR (tag_reg, block_reg, Offset.data_tag) ::
        []
      in
      return (
        sentinel_check @
        ADR (Register.temp, "lab" ^ string_of_int base_lab) ::
        (if max_idx = 0 then []
         else ADD (Register.temp, Register.temp, tag_reg) :: []) @
        BR Register.temp ::
        load_from_memory @
        ADR (Register.temp, "lab" ^ string_of_int base_lab) ::
        (if max_idx = 0 then []
         else ADD (Register.temp, Register.temp, tag_reg) :: []) @
        BR Register.temp ::
        LAB ("lab" ^ string_of_int base_lab) ::
        (if max_idx = 0 then []
         else code_table (max_idx + 1) base_lab 0) @
        List.concat branch_codes)
  | _ ->
      (* Normal definition - just compile the body *)
      code_command lmap switch_defs def.body

let translate (lmap: label_map) (switch_defs: switch_defs_map) 
    (defs: checked_definition Path.tbl) : code list state =
  let def_list = Path.to_list defs in
  let rec compile_all = function
      [] -> return []
    | (path, def) :: rest ->
        let def_idx = label_index lmap path in
        let* code = compile_def lmap switch_defs def_idx def in
        let* rest_code = compile_all rest in
        return (code :: rest_code)
  in
  compile_all def_list

let assemble (start_label: int) (sections: code list) : code =
  let rec aux lab = function
      [] -> []
    | section :: rest ->
        (LAB ("lab" ^ string_of_int lab) :: section) @ aux (lab + 1) rest
  in
  aux start_label sections

(** Main compilation entry point for checked definitions *)
let compile_checked (defs: checked_definition Path.tbl) : code * int =
  let lmap = make_label_map defs in
  let switch_defs = make_switch_defs_map defs in
  let num_defs = List.length (Path.to_list defs) in
  let (sections, _) = run_state (translate lmap switch_defs defs) num_defs in
  let main_args = match Path.to_list defs with
      [] -> 0
    | (_, def) :: _ -> List.length def.params
  in
  (assemble 0 sections, main_args)

(** Main entry point: takes unchecked definitions, checks them, and compiles.
    This is the interface used by the pipeline. *)
let compile (main: Axil.Terms.definition) (defs: Axil.Terms.definition Path.tbl) 
    : code * int =
  let all_defs = Path.add main.path main defs in
  let checked_defs = check_definitions all_defs in
  compile_checked checked_defs

(** Compile to assembly string *)
let compile_to_string (name: string) (main: Axil.Terms.definition) 
    (defs: Axil.Terms.definition Path.tbl) : string =
  let (code, arg_num) = compile main defs in
  let prog = Code.emit_all code in
  Code.into_aarch64_routine name prog arg_num
