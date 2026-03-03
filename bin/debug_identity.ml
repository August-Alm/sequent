open Sequent
open Common.Identifiers

module Pipe = Pipeline

(* Simplest test: just apply identity to a number *)
let source = {|let main: int =
  let f = fun{c}(z: c) => z in
  f{int}(5)
|}

let () = 
  print_endline "Test: simple identity function";
  let (decs, defs) = match Pipe.LangStage.to_melcore source with Ok x -> x | Error e -> failwith e in
  let (decs, typed_defs) = match Pipe.MelcoreStage.type_check decs defs with Ok x -> x | Error e -> failwith e in
  let norm_defs = Pipe.MelcoreStage.normalize typed_defs in
  let (types_ctx, core_defs) = match Pipe.MelcoreStage.encode decs norm_defs with Ok x -> x | Error e -> failwith e in
  let mono_result = match Pipe.CoreStage.monomorphize types_ctx core_defs with Ok x -> x | Error e -> failwith e in
  
  (* Focus *)
  let module CTypes = Core.Types.CoreTypes in
  let decs_with_new =
    List.fold_left (fun acc (dec: CTypes.dec) ->
      Path.add dec.name dec acc
    ) types_ctx.decs mono_result.new_declarations
  in
  
  let _focused_decs = Focus.focus_decs decs_with_new in
  let focused_main_unclosed = Focus.focus_def decs_with_new mono_result.main in
  
  (* Close it *)
  let closed_main = 
    match List.rev focused_main_unclosed.term_params with
    | (ret_k, Focused.Types.FocusedBase.Cns ret_ty) :: _ ->
        let closed_body = Focused.Return.close_ret_var ret_ty ret_k focused_main_unclosed.body in
        { focused_main_unclosed with Focused.Terms.body = closed_body }
    | _ -> focused_main_unclosed
  in
  
  print_endline "\n=== Focused main ===";
  print_endline (Focused.Printing.pp_command closed_main.body);
  
  (* Run through full pipeline stages *)
  let ( let* ) = Result.bind in
  let result =
    let* (focused_decs, focused_main, focused_defs) = 
      Pipe.CoreStage.focus types_ctx mono_result in
    
    let* (_, axil_main, axil_defs) = 
      Pipe.AxilStage.linearize focused_decs focused_main focused_defs in
    
    print_endline "\n=== Axil main ===";
    print_endline (Axil.Printing.pp_command axil_main.Axil.Terms.body);
    
    let* (asm_code, _) = 
      Pipe.EmitStage.compile Pipe.EmitStage.AARCH64 axil_main axil_defs in
    
    print_endline "\n=== Assembly (first 50 lines) ===";
    let asm_lines = List.mapi (fun i c -> Printf.sprintf "%d: %s" (i*4) (Aarch64.Code.Code.to_string c)) asm_code in
    List.iter print_endline (List.filteri (fun i _ -> i < 50) asm_lines);
    
    print_endline "\n=== Execution Trace ===";
    let* result = Pipe.EmitStage.eval ~trace:true ~max_steps:200 asm_code in
    Ok result
  in
  match result with
  | Ok n -> Printf.printf "\nResult: %d (expected 5)\n" n
  | Error e -> Printf.printf "\nError: %s\n" e
