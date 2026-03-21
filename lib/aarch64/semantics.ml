(**
  module Aarch64.Semantics
  description: Abstract machine semantics for a subset of AARCH64.
*)

open Code
open Stdint

(** Machine state *)
type state =
  { code: code               (* The program *)
  ; counter: int             (* Program counter *)
  ; registers: int array     (* 31 registers holding integer values *)
  ; memory: int array        (* Memory as growable array *)
  ; o_flag: bool             (* Overflow flag *)
  ; s_flag: bool             (* Sign flag *)
  ; z_flag: bool             (* Zero flag *)
  }

(** Get register value *)
let get (regs: int array) (r: Register.t) : int =
  regs.(Register.to_int r)

(** Set register value *)
let set (regs: int array) (r: Register.t) (v: int) : unit =
  regs.(Register.to_int r) <- v

(** Fetch instruction at counter position.
    Labels don't count toward address; each real instruction is 4 bytes. *)
let rec fetch_at (code: code) (counter: int) : instruction =
  match code with
    [] -> failwith ("jumped beyond instructions " ^ string_of_int counter)
  | LAB _ :: rest -> fetch_at rest counter
  | instr :: _ when counter = 0 -> instr
  | _ :: rest when counter >= 4 -> fetch_at rest (counter - 4)
  | _ -> failwith ("jumped between instructions " ^ string_of_int counter)

(* Debug version that tracks original counter *)
let fetch_at_debug (code: code) (counter: int) : instruction =
  let original = counter in
  let rec aux code cnt =
    match code with
      [] -> failwith (Printf.sprintf "jumped beyond instructions (original PC=%d, remaining=%d)" original cnt)
    | LAB _ :: rest -> aux rest cnt
    | instr :: _ when cnt = 0 -> instr
    | _ :: rest when cnt >= 4 -> aux rest (cnt - 4)
    | _ -> failwith ("jumped between instructions " ^ string_of_int cnt)
  in
  aux code counter

(** Get counter value for a label *)
let get_counter (code: code) (label: string) : int =
  let label = if label = "cleanup" then "lab0" else label in
  let rec aux code acc =
    match code with
      [] -> failwith ("label " ^ label ^ " not found")
    | LAB l :: rest -> 
        if l = label then acc 
        else aux rest acc
    | _ :: rest -> aux rest (acc + 4)
  in
  aux code 0

(** Load from memory at address *)
let load (mem: int array) (addr: int) : int =
  if addr < 0 || addr >= Array.length mem then 0
  else mem.(addr)

(** Store to memory at address (grows memory if needed) *)
let store (mem: int array ref) (addr: int) (value: int) : unit =
  if addr < 0 then failwith "negative memory address"
  else if addr >= Array.length !mem then begin
    let new_size = max (addr + 1) (2 * Array.length !mem) in
    let new_mem = Array.make new_size 0 in
    Array.blit !mem 0 new_mem 0 (Array.length !mem);
    mem := new_mem
  end;
  (!mem).(addr) <- value


(** Execute one instruction, return new state *)
let step (st: state) (mem_ref: int array ref) (_step_count: int) : state =
  let instr = fetch_at_debug st.code st.counter in
  match instr with
  | ADD (rd, rs1, rs2) ->
      set st.registers rd (get st.registers rs1 + get st.registers rs2);
      { st with counter = st.counter + 4 }
  
  | ADDI (rd, rs1, imm) ->
      set st.registers rd (get st.registers rs1 + imm);
      { st with counter = st.counter + 4 }
  
  | SUBI (rd, rs1, imm) ->
      set st.registers rd (get st.registers rs1 - imm);
      { st with counter = st.counter + 4 }
  
  | MUL (rd, rs1, rs2) ->
      set st.registers rd (get st.registers rs1 * get st.registers rs2);
      { st with counter = st.counter + 4 }
  
  | SDIV (rd, rs1, rs2) ->
      set st.registers rd (get st.registers rs1 / get st.registers rs2);
      { st with counter = st.counter + 4 }
  
  | MSUB (rd, rs1, rs2, rs3) ->
      (* rd = rs3 - rs1 * rs2 *)
      set st.registers rd (get st.registers rs3 - (get st.registers rs1 * get st.registers rs2));
      { st with counter = st.counter + 4 }
  
  | B label ->
      { st with counter = get_counter st.code label }
  
  | BR r ->
      let target = get st.registers r in
      if target mod 4 <> 0 then
        failwith (Printf.sprintf "BR %s: unaligned jump to %d (from PC %d)" 
          (Register.to_string r) target st.counter);
      { st with counter = target }

  | ADR (rd, label) ->
      set st.registers rd (get_counter st.code label);
      { st with counter = st.counter + 4 }

  | MOVR (rd, rs) ->
      set st.registers rd (get st.registers rs);
      { st with counter = st.counter + 4 }

  | MOVI (rd, imm) ->
      set st.registers rd (Int64.to_int imm);
      { st with counter = st.counter + 4 }

  | LDR (rt, rn, offset) ->
      let addr = get st.registers rn + offset in
      set st.registers rt (load !mem_ref addr);
      { st with counter = st.counter + 4 }

  | STR (rs, rn, offset) ->
      let addr = get st.registers rn + offset in
      store mem_ref addr (get st.registers rs);
      { st with counter = st.counter + 4; memory = !mem_ref }
  
  | CMPR (rs1, rs2) ->
      let comparee1 = get st.registers rs1 in
      let comparee2 = get st.registers rs2 in
      let result = comparee1 - comparee2 in
      let sign1 = comparee1 < 0 in
      let sign_result = result < 0 in
      { st with 
        counter = st.counter + 4
      ; o_flag = sign1 <> sign_result
      ; s_flag = sign_result
      ; z_flag = result = 0
      }
  
  | CMPI (rs, imm) ->
      let comparee = get st.registers rs in
      let result = comparee - imm in
      let sign_cmp = comparee < 0 in
      let sign_result = result < 0 in
      { st with 
        counter = st.counter + 4
      ; o_flag = sign_cmp <> sign_result
      ; s_flag = sign_result
      ; z_flag = result = 0
      }
  
  | BEQ label ->
      if st.z_flag 
      then { st with counter = get_counter st.code label }
      else { st with counter = st.counter + 4 }
  
  | BLT label ->
      if st.o_flag <> st.s_flag
      then { st with counter = get_counter st.code label }
      else { st with counter = st.counter + 4 }
  
  | LAB _ -> failwith "jumped between instructions (label)"

(** Create initial state from code *)
let initial (code: code) : state =
  let regs = Array.make 31 0 in
  (* x0 = heap pointer, x1 = free list pointer 
    Each block needs 144 bytes (18 words × 8 bytes each):
    - offset 0: ref_count/next_element
    - offset 8: code_pointer (for int consumers)
    - offsets 16-143: 8 fields × 2 words × 8 bytes
    We need multiple blocks, so space them 144 bytes apart. *)
  let block_size = 144 in
  regs.(0) <- 64;                    (* heap starts at first block *)
  regs.(1) <- 64 + block_size;       (* free list starts at second block *)
  { code; counter = 0
  ; registers = regs
  ; memory = Array.make (64 + 10 * block_size) 0
  ; o_flag = false; s_flag = false; z_flag = false
  }

(** Run until counter returns to 0 (cleanup jumped to lab0) *)
let run ?(max_steps=10000) (st: state) : int array =
  let mem_ref = ref st.memory in
  let step_count = ref 0 in
  let rec loop st steps =
    if steps >= max_steps then 
      failwith (Printf.sprintf "Max steps (%d) exceeded at counter %d" max_steps st.counter);
    incr step_count;
    let st' = step st mem_ref !step_count in
    if st'.counter = 0 then st'.registers
    else loop st' (steps + 1)
  in
  loop st 0

(** Run with trace output for debugging *)
let trace ?(max_steps=1000) (st: state) : unit =
  let mem_ref = ref st.memory in
  let print_regs regs =
    Printf.printf "[";
    Array.iteri (fun i v -> 
      if i > 0 then Printf.printf ", ";
      Printf.printf "%d" v
    ) regs;
    Printf.printf "]\n"
  in
  let rec loop st steps =
    if steps >= max_steps then begin
      Printf.printf "Max steps (%d) exceeded at counter %d\n" max_steps st.counter;
      Printf.printf "Registers: ";
      print_regs st.registers
    end else begin
      let st' = step st mem_ref steps in
      if st'.counter = 0 then begin
        Printf.printf "Final: ";
        print_regs st'.registers
      end else begin
        Printf.printf "%d: " st'.counter;
        print_regs st'.registers;
        Printf.printf "  %s\n" (Code.emit (fetch_at st'.code st'.counter));
        loop st' (steps + 1)
      end
    end
  in
  loop st 0

(** Run and return the value in register X1 (return2) *)
let run_and_get_result ?(max_steps=10000) (code: code) : int =
  let st = initial code in
  let final_regs = run ~max_steps st in
  final_regs.(Register.to_int Register.return2)