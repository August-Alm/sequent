[@@@warning "-33"]
open Common.Identifiers

module Pipe = Sequent.Pipeline
module FPrint = Focused.Printing
module FTerms = Focused.Terms

let ( let* ) = Result.bind

let code = {|
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

let vec_length{a}{n: nat}(v: vec(a)(n)): int =
  match v with
  { nil{_} => 0
  ; cons{_}{m}(x)(xs) => 1 + vec_length{a}{m}(xs)
  }

let main: int =
  let s0 = single_zero in
  let s1 = single_succ{zero}(s0) in
  let s2 = single_succ{succ(zero)}(s1) in
  let v = replicate{int}{succ(succ(zero))}(42)(s2) in
  vec_length{int}{succ(succ(zero))}(v)
|}

let () = 
  match (
    let* (decs, defs) = Pipe.LangStage.to_melcore code in
    let* (decs, typed_defs) = Pipe.MelcoreStage.type_check decs defs in
    let norm_defs = Pipe.MelcoreStage.normalize typed_defs in
    let* (types_ctx, core_defs) = Pipe.MelcoreStage.encode decs norm_defs in
    let* (types_ctx, core_defs) = Pipe.CoreStage.type_check types_ctx core_defs in
    let* mono_result = Pipe.CoreStage.monomorphize types_ctx core_defs in
    let* (focused_decs, focused_main, focused_defs) = 
      Pipe.CoreStage.focus types_ctx mono_result in
    
    (* Test with Focused semantics first *)
    let* (result_cmd, _env, steps) = 
      Pipe.FocusedStage.eval ~trace:true focused_main focused_defs in
    Printf.printf "=== FOCUSED RESULT ===\n";
    Printf.printf "Steps: %d\n" steps;
    Printf.printf "Result: %s\n\n" (FPrint.command_to_string result_cmd);
    
    let* (axil_decs, axil_main, axil_defs) = 
      Pipe.AxilStage.linearize focused_decs focused_main focused_defs in
    
    (* Compile to ASM with debug *)
    let* (asm, _) = Pipe.EmitStage.compile Pipe.EmitStage.AARCH64 axil_main axil_defs in
    
    (* Print ASM *)
    Printf.printf "=== ASM CODE ===\n";
    Printf.printf "%s\n" (Aarch64.Code.Code.list_to_string asm);
    Printf.printf "=== END ASM ===\n\n";
    
    (* Execute WITH TRACE *)
    let* result = Pipe.EmitStage.eval ~trace:true ~max_steps:10000 asm in
    Printf.printf "=== ASM RESULT ===\n";
    Printf.printf "Result: %d\n" result;
    
    Ok ()
  ) with
  | Ok () -> ()
  | Error msg -> Printf.printf "Error: %s\n" msg
