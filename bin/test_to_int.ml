[@@@warning "-33"]

module Pipe = Sequent.Pipeline
module ACode = Aarch64.Code

let ( let* ) = Result.bind

(* Test just to_int directly *)
let code = {|
data nat: type where
  { zero: nat
  ; succ: nat -> nat
  }

data single_nat: nat -> type where
  { single_zero: single_nat(zero)
  ; single_succ: {n: nat} single_nat(n) -> single_nat(succ(n))
  }

let to_int{n: nat}(k: single_nat(n)): int =
  match k with
  { single_zero => 0
  ; single_succ{m}(k') => 1 + to_int{m}(k')
  }

let main: int =
  let s0 = single_zero in
  let s1 = single_succ{zero}(s0) in
  let s2 = single_succ{succ(zero)}(s1) in
  let s3 = single_succ{succ(succ(zero))}(s2) in
  to_int{succ(succ(succ(zero)))}(s3)
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
    
    Printf.printf "=== FOCUSED to_int.mono ===\n";
    (match Common.Identifiers.Path.find_opt 
       (Common.Identifiers.Path.of_string "to_int.mono") focused_defs with
     | Some def -> 
         Printf.printf "%s\n\n" (Focused.Printing.command_to_string def.Focused.Terms.body)
     | None -> Printf.printf "(not found)\n\n");
    
    let* _ = Pipe.FocusedStage.type_check focused_decs focused_defs in
    let* (axil_decs, axil_main, axil_defs) = 
      Pipe.AxilStage.linearize focused_decs focused_main focused_defs in
    
    Printf.printf "=== AXIL to_int.mono ===\n";
    (match Common.Identifiers.Path.find_opt 
       (Common.Identifiers.Path.of_string "to_int.mono") axil_defs with
     | Some def -> 
         Printf.printf "%s\n\n" (Axil.Printing.command_to_string def.Axil.Terms.body)
     | None -> Printf.printf "(not found)\n\n");
    
    let* _ = Pipe.AxilStage.type_check axil_decs axil_defs in
    let* (asm, _) = Pipe.EmitStage.compile Pipe.EmitStage.AARCH64 axil_main axil_defs in
    
    Printf.printf "=== ASM CODE ===\n%s\n=== END ASM ===\n\n" 
      (ACode.Code.list_to_string asm);
    
    (* First run normally *)
    let* result = Pipe.EmitStage.eval ~max_steps:10000 asm in
    Printf.printf "Result: %d (expected 3)\n" result;
    
    (* Then run with trace *)
    Printf.printf "\n=== TRACE ===\n";
    let* _ = Pipe.EmitStage.eval ~trace:true ~max_steps:200 asm in
    
    Ok ()
  ) with
  | Ok () -> ()
  | Error msg -> Printf.printf "Error: %s\n" msg
