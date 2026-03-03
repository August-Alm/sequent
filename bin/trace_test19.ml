module Pipe = Sequent.Pipeline

let expr = {|
let g(a: int)(b: int)(c: int): int = a + b + c
let main: int = g(2)(3)(4)
|}

let ( let* ) = Result.bind

let () =
  let result =
    let* (decs, defs) = Pipe.LangStage.to_melcore expr in
    let* (decs, typed_defs) = Pipe.MelcoreStage.type_check decs defs in
    let norm_defs = Pipe.MelcoreStage.normalize typed_defs in
    let* (types_ctx, core_defs) = Pipe.MelcoreStage.encode decs norm_defs in
    let* (types_ctx, core_defs) = Pipe.CoreStage.type_check types_ctx core_defs in
    let* mono_result = Pipe.CoreStage.monomorphize types_ctx core_defs in
    let* (focused_decs, focused_main, focused_defs) = 
      Pipe.CoreStage.focus types_ctx mono_result in
    let* _ = Pipe.FocusedStage.type_check focused_decs focused_defs in
    let* (axil_decs, axil_main, axil_defs) = 
      Pipe.AxilStage.linearize focused_decs focused_main focused_defs in
    let* _ = Pipe.AxilStage.type_check axil_decs axil_defs in
    let (code, _arg_count) = Sequent.Compile_checked.compile axil_main axil_defs in
    Printf.printf "%d instructions generated\n" (List.length code);
    let* result = Pipe.EmitStage.eval ~trace:false ~max_steps:50000 code in
    Printf.printf "Result: %d (expected: 9)\n" result;
    Ok ()
  in
  match result with
  | Ok () -> ()
  | Error msg -> Printf.printf "Error: %s\n" msg
