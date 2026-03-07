(**
  Compiler executable for the Sequent language.
  
  Usage: 
    compile <src_file> <asm_file>           -- compile to assembly only
    compile --link <src_file> <exe_file>    -- compile, assemble, and link
  
  Compiles source code through the full pipeline:
  1. Parse and desugar to Melcore
  2. Type-check in Melcore
  3. Normalize and encode to Core
  4. Type-check in Core
  5. Focus to Focused
  6. Type-check in Focused
  7. Reduce, monomorphize and linearize to Axil
  8. Type-check in Axil
  9. Compile to AArch64 and write assembly to file
  10. (with --link) Assemble and link to executable
*)

module Pipe = Sequent.Pipeline

let ( let* ) = Result.bind

(* Path to the C driver, relative to the workspace root *)
let driver_path = "aarch64_infrastructure/driver.c"

let compile_source (source: string) (output_name: string)
    : (string, string) result =
  
  (* Stage 1: Parse and desugar *)
  let* (decs, defs) = Pipe.LangStage.to_melcore source in
  
  (* Stage 2: Melcore type-check *)
  let* (decs, typed_defs) = Pipe.MelcoreStage.type_check decs defs in
  
  (* Stage 3: Normalize *)
  let norm_defs = Pipe.MelcoreStage.normalize typed_defs in
  
  (* Stage 4: Encode to Core *)
  let* (types_ctx, core_defs) = Pipe.MelcoreStage.encode decs norm_defs in
  
  (* Stage 5: Core type-check *)
  let* (types_ctx, core_defs) = Pipe.CoreStage.type_check types_ctx core_defs in
  
  (* Stage 6: Monomorphize *)
  let* mono_result = Pipe.CoreStage.monomorphize types_ctx core_defs in
  
  (* Stage 7: Focus *)
  let* (focused_decs, focused_main, focused_defs) = 
    Pipe.CoreStage.focus types_ctx mono_result in
  
  (* Stage 7b: Reduce - inline single-use continuations *)
  let (reduced_main, reduced_defs) = 
    Pipe.FocusedStage.reduce focused_main focused_defs in
  
  (* Stage 8: Focused type-check *)
  let* _ = Pipe.FocusedStage.type_check focused_decs reduced_defs in
  
  (* Stage 9: Linearize to Axil *)
  let* (axil_decs, axil_main, axil_defs) = 
    Pipe.AxilStage.linearize focused_decs reduced_main reduced_defs in
  
  (* Stage 10: Axil type-check *)
  let* _ = Pipe.AxilStage.type_check axil_decs axil_defs in
  
  (* Stage 11: Compile to Aarch64 *)
  let* asm_string = 
    Pipe.EmitStage.compile_to_string Pipe.EmitStage.AARCH64 output_name axil_main axil_defs in
  
  Ok asm_string

let read_file (path: string) : string =
  let ic = open_in path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let write_file (path: string) (content: string) : unit =
  let oc = open_out path in
  output_string oc content;
  close_out oc

(** Create directory if it doesn't exist (including parents) *)
let ensure_dir (path: string) : unit =
  let dir = Filename.dirname path in
  if dir <> "." && dir <> "/" && not (Sys.file_exists dir) then
    ignore (Sys.command (Printf.sprintf "mkdir -p %s" (Filename.quote dir)))

(** Assemble .asm to .o and link with driver to produce executable *)
let assemble_and_link ~asm_file ~obj_file ~exe_file : (unit, string) result =
  let as_cmd = Printf.sprintf "as -o %s %s" (Filename.quote obj_file) (Filename.quote asm_file) in
  let gcc_cmd = Printf.sprintf "gcc -o %s %s %s" 
    (Filename.quote exe_file) (Filename.quote driver_path) (Filename.quote obj_file) in
  match Sys.command as_cmd with
  | 0 -> 
      (match Sys.command gcc_cmd with
       | 0 -> Ok ()
       | n -> Error (Printf.sprintf "gcc failed with exit code %d" n))
  | n -> Error (Printf.sprintf "as failed with exit code %d" n)

let print_usage () =
  Printf.eprintf "Usage:\n";
  Printf.eprintf "  %s <src_file> <asm_file>           -- compile to assembly\n" Sys.argv.(0);
  Printf.eprintf "  %s --link <src_file> <exe_file>   -- compile, assemble, and link\n" Sys.argv.(0)

let () =
  let link_mode = Array.length Sys.argv >= 2 && Sys.argv.(1) = "--link" in
  
  if link_mode then begin
    (* --link mode: compile <src> <exe> *)
    if Array.length Sys.argv <> 4 then begin
      print_usage ();
      exit 1
    end;
    
    let src_file = Sys.argv.(2) in
    let exe_file = Sys.argv.(3) in
    let base_name = Filename.remove_extension exe_file in
    let asm_file = base_name ^ ".asm" in
    let obj_file = base_name ^ ".o" in
    let output_name = Filename.basename base_name in
    let source = 
      try read_file src_file
      with Sys_error msg ->
        Printf.eprintf "Error reading %s: %s\n" src_file msg;
        exit 1
    in
    
    match compile_source source output_name with
    | Error msg ->
        Printf.eprintf "Compilation failed:\n%s\n" msg;
        exit 1
    | Ok asm_string ->
        ensure_dir asm_file;
        (try write_file asm_file asm_string
         with Sys_error msg ->
           Printf.eprintf "Error writing %s: %s\n" asm_file msg;
           exit 1);
        Printf.printf "Compiled %s -> %s\n" src_file asm_file;
        
        match assemble_and_link ~asm_file ~obj_file ~exe_file with
        | Ok () ->
            Printf.printf "Assembled %s -> %s\n" asm_file obj_file;
            Printf.printf "Linked -> %s\n" exe_file
        | Error msg ->
            Printf.eprintf "Link failed: %s\n" msg;
            exit 1
  end
  else begin
    (* Normal mode: compile <src> <asm> *)
    if Array.length Sys.argv <> 3 then begin
      print_usage ();
      exit 1
    end;
    
    let src_file = Sys.argv.(1) in
    let asm_file = Sys.argv.(2) in
    let output_name = Filename.remove_extension (Filename.basename asm_file) in
    
    let source = 
      try read_file src_file
      with Sys_error msg ->
        Printf.eprintf "Error reading %s: %s\n" src_file msg;
        exit 1
    in
    
    match compile_source source output_name with
    | Ok asm_string ->
        ensure_dir asm_file;
        (try 
          write_file asm_file asm_string;
          Printf.printf "Compiled %s -> %s\n" src_file asm_file
        with Sys_error msg ->
          Printf.eprintf "Error writing %s: %s\n" asm_file msg;
          exit 1)
    | Error msg ->
        Printf.eprintf "Compilation failed:\n%s\n" msg;
        exit 1
  end
