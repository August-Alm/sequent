(**
  module: Aarch64.Code
  description:  Type definitions for the AARCCH64 encoding.
*)


module Register: sig
    type t
    val mk: int -> t
    val to_int: t -> int
    val equal: t -> t -> bool
    val range: t list
    val reserved: int
    val temp: t
    val heap: t
    val free: t
    val return1: t
    val return2: t
    val to_string: t -> string
end = struct
  type t = int

  let mk n =
    if n > 31 || n < 0 then failwith "register number out of bounds"
    else n

  let to_int r = r

  let equal r1 r2 = (r1 = r2)

  let range = List.init 32 mk

  (**
    - x2 is used for our purposes
    - x0 is a heap pointer to an object which we can directly overwrite
      AND the first part of the return value
    - x1 is a deferred-free-list pointer to objects which we have to free
      AND the second part of the return value
  *)
  let reserved = 3
  let temp: t = mk 2
  let heap: t = mk 0
  let free: t = mk 1
  let return1: t = mk 0
  let return2: t = mk 1

  let to_string r = "X" ^ string_of_int r
end

module Offset = struct
  let jump_length n = 4 * n
  let address n = 8 * n
  let fields_per_block = 8  (* Increased to handle larger captured contexts *)
  let reference_count = address 0
  let next_element = address 0
  let code_pointer = address 1  (* For int consumers: method code address *)
  (* For destination-passed values, store the constructor tag at code_pointer offset
     since data types don't use the code_pointer slot *)
  let data_tag = address 1  (* offset 8, same as code_pointer *)
  let field1 i = address (2 + 2 * i)
  let field2 i = address (2 + 2 * i + 1)
  (* Sentinel value indicating tag should be loaded from memory (destination-passing) *)
  let alloc_sentinel = Int64.minus_one  (* -1 / 0xFFFFFFFFFFFFFFFF *)
end

type instruction =
    ADD of Register.t * Register.t * Register.t
  | ADDI of Register.t * Register.t * int
  | SUBI of Register.t * Register.t * int
  | MUL of Register.t * Register.t * Register.t
  | SDIV of Register.t * Register.t * Register.t
  | MSUB of Register.t * Register.t * Register.t * Register.t
  | B of string
  | BR of Register.t
  | ADR of Register.t * string
  | MOVR of Register.t * Register.t
  | MOVI of Register.t * Stdint.int64
  | LDR of Register.t * Register.t * int
  | STR of Register.t * Register.t * int
  | CMPR of Register.t * Register.t
  | CMPI of Register.t * int
  | BEQ of string
  | BLT of string
  | LAB of string

type code = instruction list

module Code = struct

  (** Emit a move-immediate for larger than 16-bit values.
      Uses MOVZ for first chunk, MOVK for subsequent non-zero chunks.
      Treats values as unsigned bit patterns for encoding. *)
  let emit_movi rd imm =
    let x = Register.to_string in
    (* 64-bit: up to 4 chunks *)
    let chunk n = Int64.(to_int (logand (shift_right_logical imm (16 * n)) 0xFFFFL)) in
    let c0, c1, c2, c3 = chunk 0, chunk 1, chunk 2, chunk 3 in
    if c3 = 0 && c2 = 0 && c1 = 0 then
      Printf.sprintf "MOV %s, %d" (x rd) c0
    else if c3 = 0 && c2 = 0 then
      Printf.sprintf "MOVZ %s, %d\nMOVK %s, %d, LSL #16" (x rd) c0 (x rd) c1
    else if c3 = 0 then
      Printf.sprintf "MOVZ %s, %d\nMOVK %s, %d, LSL #16\nMOVK %s, %d, LSL #32" 
        (x rd) c0 (x rd) c1 (x rd) c2
    else
      Printf.sprintf "MOVZ %s, %d\nMOVK %s, %d, LSL #16\nMOVK %s, %d, LSL #32\nMOVK %s, %d, LSL #48"
        (x rd) c0 (x rd) c1 (x rd) c2 (x rd) c3

  let emit =
    let x rd = Register.to_string rd in
    function
      ADD (rd, rn, rm) -> Printf.sprintf "ADD %s, %s, %s" (x rd) (x rn) (x rm)
    | ADDI (rd, rn, imm) -> Printf.sprintf "ADD %s, %s, %d" (x rd) (x rn) imm
    | SUBI (rd, rn, imm) -> Printf.sprintf "SUB %s, %s, %d" (x rd) (x rn) imm
    | MUL (rd, rn, rm) -> Printf.sprintf "MUL %s, %s, %s" (x rd) (x rn) (x rm)
    | SDIV (rd, rn, rm) -> Printf.sprintf "SDIV %s, %s, %s" (x rd) (x rn) (x rm)
    | MSUB (rd, rn, rm1, rm2) -> Printf.sprintf "MSUB %s, %s, %s, %s" (x rd) (x rn) (x rm1) (x rm2)
    | B label -> Printf.sprintf "B %s" label
    | BR reg -> Printf.sprintf "BR %s" (x reg)
    | ADR (reg, label) -> Printf.sprintf "ADR %s, %s" (x reg) label
    | MOVR (rd, rs) -> Printf.sprintf "MOV %s, %s" (x rd) (x rs)
    | MOVI (rd, imm) -> emit_movi rd imm
    | LDR (rt, rn, offset) -> Printf.sprintf "LDR %s, [%s, %d]" (x rt) (x rn) offset
    | STR (rt, rn, offset) -> Printf.sprintf "STR %s, [%s, %d]" (x rt) (x rn) offset
    | CMPR (rn, rm) -> Printf.sprintf "CMP %s, %s" (x rn) (x rm)
    | CMPI (rn, imm) -> Printf.sprintf "CMP %s, %d" (x rn) imm
    | BEQ label -> Printf.sprintf "BEQ %s" label
    | BLT label -> Printf.sprintf "BLT %s" label
    | LAB label -> Printf.sprintf "\n%s:" label

  let emit_all code = String.concat "\n" (List.map emit code)

  let header name =
    "// To create an executable:\n" ^
    "// $ as -o " ^ name ^ ".aarch64.o " ^ name ^ ".aarch64.asm\n" ^
    "// $ gcc -o " ^ name ^ " path/to/aarch64-infrastructure/driver.c " ^ name ^ ".aarch64.o"

  let rec move_params n =
    let x i = Register.to_string (Register.mk i) in
    match n with
      0 -> ""
    | 1 -> "MOV " ^ x 4 ^ "," ^ x 1
    | 2 -> "MOV " ^ x 6 ^ "," ^ x 2 ^ "\n" ^ move_params 1
    | 3 -> "MOV " ^ x 8 ^ "," ^ x 3 ^ "\n" ^ move_params 2
    | 4 -> "MOV " ^ x 10 ^ "," ^ x 4 ^ "\n" ^ move_params 3
    | 5 -> "MOV " ^ x 12 ^ "," ^ x 5 ^ "\n" ^ move_params 4
    | 6 -> "MOV " ^ x 14 ^ "," ^ x 6 ^ "\n" ^ move_params 5
    | 7 -> "MOV " ^ x 16 ^ "," ^ x 7 ^ "\n" ^ move_params 6
    | _ -> failwith "too many arguments for main"

  let setup arg_num =
    ".text\n" ^
    "  .global asm_main0, _asm_main0\n" ^
    "  .global asm_main1, _asm_main1\n" ^
    "  .global asm_main2, _asm_main2\n" ^
    "  .global asm_main3, _asm_main3\n" ^
    "  .global asm_main4, _asm_main4\n" ^
    "  .global asm_main5, _asm_main5\n" ^
    "  .global asm_main6, _asm_main6\n" ^
    "  .global asm_main7, _asm_main7\n" ^
    "asm_main0:\n" ^
    "_asm_main0:\n" ^
    "asm_main1:\n" ^
    "_asm_main1:\n" ^
    "asm_main2:\n" ^
    "_asm_main2:\n" ^
    "asm_main3:\n" ^
    "_asm_main3:\n" ^
    "asm_main4:\n" ^
    "_asm_main4:\n" ^
    "asm_main5:\n" ^
    "_asm_main5:\n" ^
    "asm_main6:\n" ^
    "_asm_main6:\n" ^
    "asm_main7:\n" ^
    "_asm_main7:\n" ^
    "// setup\n" ^
    "// save registers\n" ^
    "STR X16, [sp, -16]!\n" ^
    "STR X17, [sp, -16]!\n" ^
    "STR X18, [sp, -16]!\n" ^
    "STR X19, [sp, -16]!\n" ^
    "STR X20, [sp, -16]!\n" ^
    "STR X21, [sp, -16]!\n" ^
    "STR X22, [sp, -16]!\n" ^
    "STR X23, [sp, -16]!\n" ^
    "STR X24, [sp, -16]!\n" ^
    "STR X25, [sp, -16]!\n" ^
    "STR X26, [sp, -16]!\n" ^
    "STR X27, [sp, -16]!\n" ^
    "STR X28, [sp, -16]!\n" ^
    "STR X29, [sp, -16]!\n" ^
    "STR X30, [sp, -16]!\n" ^
    "\n" ^
    "// move parameters into place\n" ^
    move_params arg_num ^
    "\n" ^
    "// initialize free pointer\n" ^
    "MOV " ^ Register.to_string Register.free ^ "," ^ Register.to_string Register.heap ^
    "\n" ^
    "ADD " ^ Register.to_string Register.free ^ "," ^ Register.to_string Register.free ^ "," ^ string_of_int (Offset.field1 Offset.fields_per_block)

  let cleanup =
    "// cleanup\n" ^
    "cleanup:" ^
    "\n" ^
    "// restore registers\n" ^
    "LDR X30, [sp], 16\n" ^
    "LDR X29, [sp], 16\n" ^
    "LDR X28, [sp], 16\n" ^
    "LDR X27, [sp], 16\n" ^
    "LDR X26, [sp], 16\n" ^
    "LDR X25, [sp], 16\n" ^
    "LDR X24, [sp], 16\n" ^
    "LDR X23, [sp], 16\n" ^
    "LDR X22, [sp], 16\n" ^
    "LDR X21, [sp], 16\n" ^
    "LDR X20, [sp], 16\n" ^
    "LDR X19, [sp], 16\n" ^
    "LDR X18, [sp], 16\n" ^
    "LDR X17, [sp], 16\n" ^
    "LDR X16, [sp], 16\n" ^
    "RET"

  let into_aarch64_routine name prog arg_num =
    header name ^
    "\n\n" ^
    setup arg_num ^ "\n\n" ^
    " // actual code" ^
    prog ^
    "\n" ^
    cleanup

end