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

(* Debug flags - defined early so store/load can use them *)
let debug_store = ref false

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
  match ct with Prd (Ext _) -> true | _ -> false

(* ========================================================================= *)
(* Control Flow Helpers                                                      *)
(* ========================================================================= *)

let skip_if_zero (this: Register.t) (code: code list) : code list state =
  let* lab = fresh_label in
  let label = "lab" ^ string_of_int lab in
  return (
    CMPI (this, 0) ::
    BEQ label ::
    code @
    LAB label :: [])

let if_zero_then_else (this: Register.t) (thn: code list) (els: code list) 
    : code list state =
  let* lab_then = fresh_label in
  let* lab_else = fresh_label in
  let label_then = "lab" ^ string_of_int lab_then in
  let label_else = "lab" ^ string_of_int lab_else in
  Printf.eprintf "if_zero_then_else: reg=X%d then_lab=%s else_lab=%s\n" (Register.to_int this) label_then label_else;
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

let share_block_n (this: Register.t) (k: int) : code list state =
  skip_if_zero this (
    LDR (Register.temp, this, Offset.reference_count) ::
    ADDI (Register.temp, Register.temp, k) ::
    STR (Register.temp, this, Offset.reference_count) :: [])

let share_block (this: Register.t) : code list state =
  share_block_n this 1

let erase_valid_object (this: Register.t) : code list state =
  if_zero_then_else Register.temp
    (STR (Register.free, this, Offset.next_element) ::
     MOVR (Register.free, this) :: [])
    (SUBI (Register.temp, Register.temp, 1) ::
     STR (Register.temp, this, Offset.reference_count) :: [])

let erase_block (this: Register.t) : code list state =
  let* erase_code = erase_valid_object this in
  skip_if_zero this (
    LDR (Register.temp, this, Offset.reference_count) ::
    erase_code)

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

let acquire_block (accu: Register.t) (this: Register.t) : code list state =
  let* erase_code = erase_fields accu Register.heap Offset.fields_per_block in
  let* adapt_free = if_zero_then_else Register.free
    (ADDI (Register.free, Register.heap, Offset.field1 Offset.fields_per_block) :: [])
    (MOVI (Register.temp, 0) ::
     STR (Register.temp, Register.heap, Offset.next_element) ::
     erase_code) in
  let* adapt_heap = if_zero_then_else Register.heap
    (MOVR (Register.heap, Register.free) ::
     LDR (Register.free, Register.free, Offset.next_element) ::
     adapt_free)
    (MOVI (Register.temp, 0) ::
     STR (Register.temp, this, Offset.reference_count) :: []) in
  return (
    MOVR (this, Register.heap) ::
    LDR (Register.heap, Register.heap, Offset.next_element) ::
    adapt_heap)

let release_block (accu: Register.t) (this: Register.t) : code list state =
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
    : code list state =
  if !debug_store then 
    Printf.eprintf "  store_value: %s at k=%d, src r1=X%d r2=X%d, offset1=%d offset2=%d\n" 
      (Ident.name v) k 
      (Register.to_int (symbol_location1 src_ctx v))
      (Register.to_int (symbol_location2 src_ctx v))
      (Offset.field1 k) (Offset.field2 k);
  if is_ext_type ct then
    return (
      STR (symbol_location2 src_ctx v, into, Offset.field2 k) ::
      MOVI (Register.temp, 0) ::
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
let load_binder (x: var) (ct: chiral_typ) (x_ctx: ctx) (from: Register.t) (k: int) 
    : code list =
  let is_ext = is_ext_type ct in
  if !debug_store then 
    Printf.eprintf "  load_binder: %s at k=%d, from=X%d, tgt r1=X%d r2=X%d, offset1=%d offset2=%d, is_ext=%b\n" 
      (Ident.name x) k 
      (Register.to_int from)
      (Register.to_int (symbol_location1 x_ctx x))
      (Register.to_int (symbol_location2 x_ctx x))
      (Offset.field1 k) (Offset.field2 k) is_ext;
  if is_ext then
    LDR (symbol_location2 x_ctx x, from, Offset.field2 k) :: []
  else
    LDR (symbol_location2 x_ctx x, from, Offset.field2 k) ::
    LDR (symbol_location1 x_ctx x, from, Offset.field1 k) :: []

let store_block (ctx: ctx) (into: Register.t) (k: int) : code list =
  STR (fresh_location1 ctx, into, Offset.field1 k) :: []

let load_block (ctx: ctx) (from: Register.t) (k: int) : code list =
  LDR (fresh_location1 ctx, from, Offset.field1 k) :: []

let rec store_zeroes (into: Register.t) (k: int) : code list =
  if k = 0 then []
  else
    MOVI (Register.temp, 0) ::
    STR (Register.temp, into, Offset.field1 (k - 1)) ::
    store_zeroes into (k - 1)

(** Store multiple values into a block.
    vs: values to store (in order)
    src_ctx: context for looking up source registers *)
let rec store_values (vs: ctx) (src_ctx: ctx) (into: Register.t) (k: int) 
    : code list state =
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
    : code list =
  Printf.eprintf "load_binders: xs=[%s] as_ctx=[%s] k=%d\n"
    (String.concat ", " (List.map (fun (v, ct) -> Printf.sprintf "%s:%s" (Ident.name v) (match ct with Prd (Ext _) -> "PrdExt" | Prd _ -> "Prd" | Cns _ -> "Cns")) xs))
    (String.concat ", " (List.map (fun (v, ct) -> Printf.sprintf "%s:%s" (Ident.name v) (match ct with Prd (Ext _) -> "PrdExt" | Prd _ -> "Prd" | Cns _ -> "Cns")) as_ctx))
    k;
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
let rec store_rest (vs: ctx) (src_ctx: ctx) (as_ctx: ctx) : code list state =
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
let store (vs: ctx) (src_ctx: ctx) (as_ctx: ctx) : code list state =
  match vs with
  | [] ->
      return (MOVI (fresh_location1 as_ctx, 0) :: [])
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
let rec load_rest (xs: ctx) (as_ctx: ctx) : code list state =
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
let load (xs: ctx) (as_ctx: ctx) : code list state =
  match xs with
  | [] -> return []
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

let rec code_table (n: int) (lab_base: int) (lab_branch: int) : code list =
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

let update_reference_count (r: Register.t) (n: int) : code list state =
  if n = 0 then erase_block r
  else if n = 1 then return []
  else share_block_n r (n - 1)

let rec code_weakening_contraction (ctx: ctx) (usage: (var * var list) list)
    : code list state =
  match ctx, usage with
  | [], [] -> return []
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

let debug_conn = ref false  (* Set to true for connections debug *)

let connections (src_ctx: ctx) (tgt_ctx: ctx) (usage: (var * var list) list)
    : Register.t list list =
  let graph = Array.make 32 [] in
  List.iter2 (fun (v, ct) (_, targets) ->
    let src_r1 = symbol_location1 src_ctx v in
    let src_r2 = symbol_location2 src_ctx v in
    let tgt_regs1 = List.map (symbol_location1 tgt_ctx) targets in
    let tgt_regs2 = List.map (symbol_location2 tgt_ctx) targets in
    if !debug_conn then begin
      Printf.eprintf "  conn: %s (%s) src=X%d,X%d tgt1=[%s] tgt2=[%s]\n"
        (Ident.name v)
        (if is_ext_type ct then "ext" else "non-ext")
        (Register.to_int src_r1) (Register.to_int src_r2)
        (String.concat "," (List.map (fun r -> Printf.sprintf "X%d" (Register.to_int r)) tgt_regs1))
        (String.concat "," (List.map (fun r -> Printf.sprintf "X%d" (Register.to_int r)) tgt_regs2))
    end;
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
(* Main Code Generation                                                      *)
(* ========================================================================= *)

(*
  Compile a checked command to AARCH64 assembly.
  The context is embedded in each AST node, so no manual threading needed.
*)

let debug_subst = ref false  (* Set to true to enable debug output *)

let pp_ctx ctx =
  String.concat ", " (List.map (fun (v, ct) ->
    let ct_str = match ct with
        Prd (Ext _) -> "PrdExt"
      | Cns (Ext _) -> "CnsExt" 
      | Prd _ -> "Prd"
      | Cns _ -> "Cns"
    in
    Printf.sprintf "%s:%s" (Ident.name v) ct_str
  ) ctx)

let rec code_command (lmap: label_map) (cmd: checked_command) 
    : code list state =
  match cmd with
  (* Substitute: explicit structural rules *)
    CSubstitute { src_ctx; mapping; tgt_ctx; body } ->
      if !debug_subst then begin
        Printf.eprintf "CSubstitute:\n";
        Printf.eprintf "  src_ctx (len=%d): [%s]\n" (List.length src_ctx) (pp_ctx src_ctx);
        Printf.eprintf "  tgt_ctx (len=%d): [%s]\n" (List.length tgt_ctx) (pp_ctx tgt_ctx);
        Printf.eprintf "  mapping: [%s]\n" (String.concat ", " (List.map (fun (t, s) ->
          Printf.sprintf "%s<-%s" (Ident.name t) (Ident.name s)) mapping))
      end;
      let usage = transpose src_ctx mapping in
      if !debug_subst then begin
        Printf.eprintf "  usage: [%s]\n" (String.concat ", " (List.map (fun (v, targets) ->
          Printf.sprintf "%s->[%s]" (Ident.name v) 
            (String.concat "," (List.map Ident.name targets))) usage))
      end;
      let* weaken_contract = code_weakening_contraction src_ctx usage in
      let graph = connections src_ctx tgt_ctx usage in
      if !debug_subst then begin
        Printf.eprintf "  graph edges (len=%d):\n" (List.length graph);
        List.iteri (fun i targets ->
          if targets <> [] then
            Printf.eprintf "    X%d -> [%s]\n" i 
              (String.concat ", " (List.map (fun r -> Printf.sprintf "X%d" (Register.to_int r)) targets))
        ) graph
      end;
      let exchange = code_exhange graph in
      if !debug_subst then begin
        Printf.eprintf "  exchange code: %d instructions\n" (List.length exchange);
        List.iter (fun c -> Printf.eprintf "    %s\n" (Code.to_string c)) exchange
      end;
      let* rest = code_command lmap body in
      return (weaken_contract @ exchange @ rest)

  (* Jump to label - move args to target positions then branch *)
  | CJump { ctx; label; args } ->
      let idx = label_index lmap label in
      let num_args = List.length args in
      Printf.eprintf "CJump: label=%s idx=%d num_args=%d\n" (Path.name label) idx num_args;
      Printf.eprintf "  ctx: [%s]\n" (pp_ctx ctx);
      Printf.eprintf "  args: [%s]\n" (pp_ctx args);
      (* Move args from current positions to target positions.
         args[i] should go to position (num_args - 1 - i) from end.
         We build a graph of register moves and use exchange algorithm. *)
      let graph = Array.make 32 [] in
      List.iteri (fun i (arg, ct) ->
        let src_r2 = symbol_location2 ctx arg in
        let tgt_pos = num_args - 1 - i in
        let tgt_r2 = Register.mk (Register.reserved + 2 * tgt_pos + 1) in
        Printf.eprintf "  arg %d: %s src_r2=X%d tgt_r2=X%d is_ext=%b\n" i (Ident.name arg) (Register.to_int src_r2) (Register.to_int tgt_r2) (is_ext_type ct);
        if is_ext_type ct then
          graph.(Register.to_int src_r2) <- [tgt_r2]
        else begin
          let src_r1 = symbol_location1 ctx arg in
          let tgt_r1 = Register.mk (Register.reserved + 2 * tgt_pos) in
          Printf.eprintf "    non-ext: src_r1=X%d tgt_r1=X%d\n" (Register.to_int src_r1) (Register.to_int tgt_r1);
          graph.(Register.to_int src_r1) <- [tgt_r1];
          graph.(Register.to_int src_r2) <- [tgt_r2]
        end
      ) args;
      let exchange = code_exhange (Array.to_list graph) in
      Printf.eprintf "  exchange: %d instructions\n" (List.length exchange);
      List.iter (fun c -> Printf.eprintf "    %s\n" (Code.to_string c)) exchange;
      return (exchange @ [B ("lab" ^ string_of_int idx)])

  (* Let: construct data value *)
  | CLet { ctx; v; v_typ; dec; xtor; args; tail_ctx; body } ->
      Printf.eprintf "CLet: v=%s xtor=%s dec=%s\n" (Ident.name v) (Path.name xtor) (Path.name dec.name);
      Printf.eprintf "  ctx: [%s]\n" (pp_ctx ctx);
      Printf.eprintf "  args: [%s]\n" (pp_ctx args);
      Printf.eprintf "  tail_ctx: [%s]\n" (pp_ctx tail_ctx);
      let new_ctx = (v, v_typ) :: tail_ctx in
      Printf.eprintf "  new_ctx: [%s]\n" (pp_ctx new_ctx);
      let tag_reg = symbol_location2 new_ctx v in
      Printf.eprintf "  tag_reg: X%d\n" (Register.to_int tag_reg);
      (* Use original_index to get consistent tag across filtered/unfiltered xtor lists *)
      let xtor_idx = 
        let rec find_xtor = function
            [] -> 
              Printf.eprintf "WARNING: xtor '%s' not found in dec.xtors! Defaulting to 0.\n" (Path.name xtor);
              0
          | (y: xtor) :: _ when Path.equal y.name xtor -> y.original_index
          | _ :: rest -> find_xtor rest
        in find_xtor dec.xtors
      in
      Printf.eprintf "  xtor_idx=%d tag=%d\n" xtor_idx (Offset.jump_length xtor_idx);
      (* Store args with ctx as source context, tail_ctx as the "as" context *)
      let* stores = store args ctx tail_ctx in
      Printf.eprintf "  stores: %d instructions\n" (List.length stores);
      let* rest = code_command lmap body in
      Printf.eprintf "  rest (body): %d instructions, first: %s\n" (List.length rest) (if rest = [] then "empty" else Code.to_string (List.hd rest));
      return (
        stores @
        MOVI (tag_reg, Offset.jump_length xtor_idx) ::
        rest)

  (* Switch: pattern match on data 
     
    IMPORTANT: Tags are based on original_index (for consistent GADT handling).
    The jump table must be sparse - branches are at their original_index positions,
    not sequential. This ensures tag values match jump table offsets. *)
  | CSwitch { ctx; v; dec; tail_ctx; branches; _ } ->
      let tag_reg = symbol_location2 ctx v in
      let* base_lab = fresh_label in
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
      if !debug_subst then begin
        Printf.eprintf "CSwitch: v=%s dec=%s\n" (Ident.name v) (Path.name dec.name);
        Printf.eprintf "  ctx (len=%d): [%s]\n" (List.length ctx) (pp_ctx ctx);
        Printf.eprintf "  v pos_from_end=%d\n" (position_from_end ctx v);
        Printf.eprintf "  dec.xtors: [%s]\n" (String.concat ", " (List.map (fun (x: xtor) -> Printf.sprintf "%s(orig_idx=%d)" (Path.name x.name) x.original_index) dec.xtors));
        Printf.eprintf "  branches: [%s]\n" (String.concat ", " (List.map (fun b -> Printf.sprintf "%s->%d" (Path.name b.xtor) (get_original_index b.xtor)) branches));
        Printf.eprintf "  max_idx=%d base_lab=%d tag_reg=X%d\n" max_idx base_lab (Register.to_int tag_reg)
      end;
      (* Create sparse jump table: entries at original_index positions *)
      let* branch_codes = code_clauses_sparse lmap tail_ctx branches base_lab get_original_index in
      return (
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
      Printf.eprintf "CNew: k=%s k_typ=%s\n" (Ident.name k) (match k_typ with Prd _ -> "Prd" | Cns _ -> "Cns");
      Printf.eprintf "  ctx (captured): [%s]\n" (pp_ctx ctx);
      Printf.eprintf "  dec.xtors: [%s]\n" (String.concat ", " (List.map (fun (x: xtor) -> Printf.sprintf "%s(orig_idx=%d)" (Path.name x.name) x.original_index) dec.xtors));
      Printf.eprintf "  branches: [%s]\n" (String.concat ", " (List.map (fun b -> Printf.sprintf "%s->%d" (Path.name b.xtor) (get_original_index b.xtor)) branches));
      Printf.eprintf "  max_idx=%d base_lab=TBD tag_reg=X%d\n" max_idx (Register.to_int tab_reg);
      (* Store ctx (the captured environment).
         src_ctx = ctx (where values are now)
         as_ctx = ctx (so block ends up at fresh_location1(ctx) = k's position) *)
      let* stores = store ctx ctx ctx in
      let* base_lab = fresh_label in
      let* rest = code_command lmap body in
      (* Create sparse jump table: entries at original_index positions *)
      let* branch_codes = code_methods_sparse lmap ctx branches base_lab get_original_index in
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
      let max_idx = List.fold_left (fun acc (y: xtor) -> max acc y.original_index) 0 dec.xtors in
      if !debug_subst then begin
        Printf.eprintf "CInvoke: v=%s xtor=%s dec=%s\n" (Ident.name v) (Path.name xtor) (Path.name dec.name);
        Printf.eprintf "  ctx (len=%d): [%s]\n" (List.length ctx) (pp_ctx ctx);
        Printf.eprintf "  args: [%s]\n" (pp_ctx args);
        Printf.eprintf "  v pos_from_end=%d\n" (position_from_end ctx v);
        Printf.eprintf "  xtor_idx=%d max_idx=%d\n" xtor_idx max_idx;
        Printf.eprintf "  tab_reg=X%d block_reg=X%d this_reg=X%d\n" 
          (Register.to_int tab_reg) (Register.to_int block_reg) (Register.to_int this_reg)
      end;
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
      if !debug_subst then begin
        Printf.eprintf "  substitute: %d instructions\n" (List.length substitute);
        List.iter (fun c -> Printf.eprintf "    %s\n" (Code.to_string c)) substitute
      end;
      return (
        substitute @
        (if max_idx < 1 then
          BR Register.temp :: []
        else
          ADDI (Register.temp, Register.temp, Offset.jump_length xtor_idx) ::
          BR Register.temp :: []))

  (* Axiom: cut between producer and consumer
     
    Exactly like CInvoke but for Cns (Ext Int) - a single-method codata.
    Block pointer goes to fresh_location1(args) where args has length 1.
    Arg goes to standard incoming position X(reserved + 1) = X4.
    
    IMPORTANT: Save code pointer to X2 first, as arg_reg=X4 might clobber it. *)
  | CAxiom { ctx; v; k; _ } ->
      let v_reg = symbol_location2 ctx v in
      let k_block_reg = symbol_location1 ctx k in
      let k_code_reg = symbol_location2 ctx k in
      (* Method has 1 parameter, so block at X(reserved + 2*1) = X5 *)
      let this_reg = Register.mk (Register.reserved + 2 * 1) in
      let arg_reg = Register.mk (Register.reserved + 1) in  (* X4 *)
      return (
        MOVR (Register.temp, k_code_reg) ::   (* Save code ptr to X2 first! *)
        MOVR (this_reg, k_block_reg) ::       (* Block to X5 *)
        MOVR (arg_reg, v_reg) ::              (* Arg to X4 *)
        BR Register.temp :: [])               (* Branch via X2 *)

  (* Literal: create integer value *)
  | CLit { ctx; n; v; body } ->
      let new_ctx = (v, Prd (Ext Common.Types.Int)) :: ctx in
      Printf.eprintf "CLit: n=%d v=%s ctx=[%s] target_reg=X%d\n" n (Ident.name v) (pp_ctx ctx) (Register.to_int (symbol_location2 new_ctx v));
      let* rest = code_command lmap body in
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
      let k_ctx = (k, Cns (Ext Common.Types.Int)) :: ctx in
      let k_block_reg = symbol_location1 k_ctx k in  (* r1 = block pointer *)
      let k_code_reg = symbol_location2 k_ctx k in   (* r2 = code address *)
      (* Arg incoming at X4, matching CAxiom's convention *)
      let arg_incoming_reg = Register.mk (Register.reserved + 1) in (* X4 *)
      (* The arg register where method expects it.
        Method context after load = ctx @ tail_ctx = captured @ [param].
        param_ctx must match this order: ctx @ [param]. *)
      let param_ctx = ctx @ [(param, Prd (Ext Common.Types.Int))] in
      let arg_expected_reg = symbol_location2 param_ctx param in
      (* tail_ctx for block pointer calculation = [param] *)
      let tail_ctx = [(param, Prd (Ext Common.Types.Int))] in
      (* Store ctx as captured environment *)
      let* stores = store ctx ctx ctx in
      Printf.eprintf "CNewInt: k=%s ctx=[%s]\n" (Ident.name k) (pp_ctx ctx);
      Printf.eprintf "  stores: %d instructions, last few:\n" (List.length stores);
      let last_5 = List.rev (List.filteri (fun i _ -> i < 5) (List.rev stores)) in
      List.iter (fun c -> Printf.eprintf "    %s\n" (Code.to_string c)) last_5;
      let* base_lab = fresh_label in
      let* cont = code_command lmap cont_body in
      Printf.eprintf "  cont: %d instructions, first few:\n" (List.length cont);
      let first_5 = List.filteri (fun i _ -> i < 5) cont in
      List.iter (fun c -> Printf.eprintf "    %s\n" (Code.to_string c)) first_5;
      (* Method: load captured vars from block. After load, context is ctx @ tail_ctx. *)
      let* loads = load ctx tail_ctx in
      let* method_body = code_command lmap branch_body in
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
      let new_ctx = (v, Prd (Ext Common.Types.Int)) :: ctx in
      let* rest = code_command lmap body in
      return (
        ADD (symbol_location2 new_ctx v, symbol_location2 ctx x, 
             symbol_location2 ctx y) ::
        rest)

  (* Sub: integer subtraction *)
  | CSub { ctx; x; y; v; body } ->
      let new_ctx = (v, Prd (Ext Common.Types.Int)) :: ctx in
      let x_reg = symbol_location2 ctx x in
      let y_reg = symbol_location2 ctx y in
      let v_reg = symbol_location2 new_ctx v in
      let* rest = code_command lmap body in
      return (
        MOVI (Register.temp, 1) ::
        MSUB (v_reg, Register.temp, y_reg, x_reg) ::
        rest)

  (* Ifz: conditional on zero *)
  | CIfz { ctx; v; then_cmd; else_cmd } ->
      let v_reg = symbol_location2 ctx v in
      let* lab = fresh_label in
      let label = "lab" ^ string_of_int lab in
      let* else_code = code_command lmap else_cmd in
      let* then_code = code_command lmap then_cmd in
      return (
        CMPI (v_reg, 0) ::
        BEQ label ::
        else_code @
        LAB label ::
        then_code)

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
and code_clause (lmap: label_map) (tail_ctx: ctx) (branch: checked_branch)
    : code list state =
  (* Load args into HEAD positions, tail_ctx stays at TAIL *)
  if !debug_store then
    Printf.eprintf "code_clause: xtor=%s args=[%s] tail_ctx=[%s]\n" 
      (Path.name branch.xtor) (pp_ctx branch.args) (pp_ctx tail_ctx);
  let* loads = load branch.args tail_ctx in
  let* body_code = code_command lmap branch.body in
  return (loads @ body_code)

and code_clauses (lmap: label_map) (tail_ctx: ctx) 
    (branches: checked_branch list) (base_lab: int) (branch_idx: int) 
    : code list list state =
  match branches with
  | [] -> return []
  | branch :: rest ->
      let* clause = code_clause lmap tail_ctx branch in
      let* rest_clauses = code_clauses lmap tail_ctx rest base_lab (branch_idx + 1) in
      let labeled = 
        LAB ("lab" ^ string_of_int base_lab ^ "b" ^ string_of_int branch_idx) :: 
        clause in
      return (labeled :: rest_clauses)

(** Compile clauses with sparse indexing based on original_index.
    Used for CSwitch when xtors may be filtered due to GADT instantiation.
    Each branch is labeled with its xtor's original_index, not sequential index. *)
and code_clauses_sparse (lmap: label_map) (tail_ctx: ctx) 
    (branches: checked_branch list) (base_lab: int)
    (get_original_index: Path.t -> int)
    : code list list state =
  match branches with
  | [] -> return []
  | branch :: rest ->
      let* clause = code_clause lmap tail_ctx branch in
      let original_idx = get_original_index branch.xtor in
      let* rest_clauses = code_clauses_sparse lmap tail_ctx rest base_lab get_original_index in
      let labeled = 
        LAB ("lab" ^ string_of_int base_lab ^ "b" ^ string_of_int original_idx) :: 
        clause in
      return (labeled :: rest_clauses)

(** Compile a method (branch of new/codata).
    captured_ctx: the context captured when creating the codata
    branch.args: arguments passed to this method
    branch.branch_ctx = captured_ctx @ args *)
and code_method (lmap: label_map) (captured_ctx: ctx) (branch: checked_branch)
    : code list state =
  let args = branch.args in
  if !debug_subst then begin
    Printf.eprintf "code_method: xtor=%s\n" (Path.name branch.xtor);
    Printf.eprintf "  args: [%s]\n" (pp_ctx args);
    Printf.eprintf "  captured_ctx: [%s]\n" (pp_ctx captured_ctx);
    Printf.eprintf "  full_ctx: [%s]\n" (pp_ctx branch.branch_ctx)
  end;
  let* loads = load captured_ctx args in
  let* body_code = code_command lmap branch.body in
  return (loads @ body_code)

and code_methods (lmap: label_map) (captured_ctx: ctx)
    (branches: checked_branch list) (base_lab: int) (branch_idx: int) 
    : code list list state =
  match branches with
  | [] -> return []
  | branch :: rest ->
      let* method_code = code_method lmap captured_ctx branch in
      let* rest_methods = code_methods lmap captured_ctx rest base_lab (branch_idx + 1) in
      let labeled =
        LAB ("lab" ^ string_of_int base_lab ^ "b" ^ string_of_int branch_idx) ::
        method_code in
      return (labeled :: rest_methods)

(** Compile methods with sparse indexing based on original_index.
    Used for CNew when xtors may be filtered due to GADT instantiation.
    Each method is labeled with its xtor's original_index, not sequential index. *)
and code_methods_sparse (lmap: label_map) (captured_ctx: ctx) 
    (branches: checked_branch list) (base_lab: int)
    (get_original_index: Path.t -> int)
    : code list list state =
  match branches with
  | [] -> return []
  | branch :: rest ->
      let* method_code = code_method lmap captured_ctx branch in
      let original_idx = get_original_index branch.xtor in
      let* rest_methods = code_methods_sparse lmap captured_ctx rest base_lab get_original_index in
      let labeled = 
        LAB ("lab" ^ string_of_int base_lab ^ "b" ^ string_of_int original_idx) :: 
        method_code in
      return (labeled :: rest_methods)

(* ========================================================================= *)
(* Top-Level Compilation                                                     *)
(* ========================================================================= *)

let translate (lmap: label_map) (defs: checked_definition Path.tbl) 
    : code list list state =
  let def_list = Path.to_list defs in
  let rec compile_all = function
    | [] -> return []
    | (path, def) :: rest ->
        let _ = path in
        let* code = code_command lmap def.body in
        let* rest_code = compile_all rest in
        return (code :: rest_code)
  in
  compile_all def_list

let assemble (start_label: int) (sections: code list list) : code list =
  let rec aux lab = function
    | [] -> []
    | section :: rest ->
        (LAB ("lab" ^ string_of_int lab) :: section) @ aux (lab + 1) rest
  in
  aux start_label sections

(** Main compilation entry point for checked definitions *)
let compile_checked (defs: checked_definition Path.tbl) : code list * int =
  let lmap = make_label_map defs in
  let num_defs = List.length (Path.to_list defs) in
  let (sections, _) = run_state (translate lmap defs) num_defs in
  let main_args = match Path.to_list defs with
      [] -> 0
    | (_, def) :: _ -> List.length def.params
  in
  (assemble 0 sections, main_args)

(** Main entry point: takes unchecked definitions, checks them, and compiles.
    This is the interface used by the pipeline. *)
let compile (main: Axil.Terms.definition) (defs: Axil.Terms.definition Path.tbl) 
    : code list * int =
  let all_defs = Path.add main.path main defs in
  (* Debug: print Axil IR before checking *)
  List.iter (fun (path, def) ->
    let pn = Path.name path in
    let starts_with prefix s = 
      String.length s >= String.length prefix && 
      String.sub s 0 (String.length prefix) = prefix in
    if starts_with "replicate" pn || starts_with "length" pn then
      Printf.eprintf "=== Axil IR for %s ===\n%s\n\n" pn 
        (Axil.Printing.command_to_string_typed def.Axil.Terms.body)
  ) (Path.to_list all_defs);
  let checked_defs = check_definitions all_defs in
  compile_checked checked_defs

(** Compile to assembly string *)
let compile_to_string (name: string) (main: Axil.Terms.definition) 
    (defs: Axil.Terms.definition Path.tbl) : string =
  let (code, arg_num) = compile main defs in
  let prog = Code.list_to_string code in
  Code.into_aarch64_routine name prog arg_num
