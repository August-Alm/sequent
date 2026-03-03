(* Test 22: Data kind (vectors) *)
module Pipe = Sequent.Pipeline

let source = {|
data nat: type where
  { zero: nat
  ; succ: nat -> nat
  }

data vec: type -> nat -> type where
  { nil: {a} vec(a)(zero)
  ; cons: {a}{n: nat} a -> vec(a)(n) -> vec(a)(succ(n))
  }

let length{a}{k: nat}(v: vec(a)(k)): int =
  match v with
  { nil{_} => 0
  ; cons{_}{n}(x)(xs) => 1 + length{a}{n}(xs)
  }

let main: int =
  let v0 = cons{int}{zero}(0)(nil{int}) in
  let v1 = cons{int}{succ(zero)}(1)(v0) in
  let v2 = cons{int}{succ(succ(zero))}(2)(v1) in
  length{int}{succ(succ(succ(zero)))}(v2)
|}

let ( let* ) = Result.bind

let () =
  let result =
    let* (decs, defs) = Pipe.LangStage.to_melcore source in
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
    Printf.printf "=== Compiling ===\n";
    let (code, _arg_count) = Sequent.Compile_checked.compile axil_main axil_defs in
    Printf.printf "\n=== Running ===\n";
    let* result = Pipe.EmitStage.eval ~trace:false ~max_steps:50000 code in
    Printf.printf "Result: %d (expected: 3)\n" result;
    Ok ()
  in
  match result with
  | Ok () -> ()
  | Error msg -> Printf.printf "Error: %s\n" msg
