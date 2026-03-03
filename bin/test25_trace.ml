(* Test replicate with 2 elements *)
module Pipe = Sequent.Pipeline

let source = {|
data nat: type where
  { zero: nat
  ; succ: nat -> nat
  }

data single_nat: nat -> type where
  { single_zero: single_nat(zero)
  ; single_succ: {n: nat} single_nat(n) -> single_nat(succ(n))
  }

data vec: type -> nat -> type where
  { nil: {a} vec(a)(zero)
  ; cons: {a}{n: nat} a -> vec(a)(n) -> vec(a)(succ(n))
  }

let replicate{a}{n: nat}(x: a)(k: single_nat(n)): vec(a)(n) =
  match k with
  { single_zero => nil{a}
  ; single_succ{m}(k') => cons{a}{m}(x)(replicate{a}{m}(x)(k'))
  }

let length{a}{n: nat}(v: vec(a)(n)): int =
  match v with
  { nil{_} => 0
  ; cons{_}{m}(x)(xs) => 1 + length{a}{m}(xs)
  }

let main: int =
  let n2_single = single_succ{succ(zero)}(single_succ{zero}(single_zero)) in
  let v = replicate{int}{succ(succ(zero))}(42)(n2_single) in
  length{int}{succ(succ(zero))}(v)
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
    let* result = Pipe.EmitStage.eval ~trace:true ~max_steps:50000 code in
    Printf.printf "Result: %d (expected: 2)\n" result;
    Ok ()
  in
  match result with
  | Ok () -> ()
  | Error msg -> Printf.printf "Error: %s\n" msg

