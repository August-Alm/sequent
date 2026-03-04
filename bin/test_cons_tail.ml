(* Super minimal test - just a single cons with manual tail access *)
module Pipe = Sequent.Pipeline

(* Test: Build cons manually, access tail with separate function *)
let source = {|
data nat: type where
  { zero: nat
  ; succ: nat -> nat
  }

data vec: type -> nat -> type where
  { nil: {a} vec(a)(zero)
  ; cons: {a}{n: nat} a -> vec(a)(n) -> vec(a)(succ(n))
  }

let get_tail{a}{n: nat}(v: vec(a)(succ(n))): vec(a)(n) =
  match v with
  { cons{_}{m}(x)(xs) => xs
  }

let main: int =
  let inner = nil{int} in
  let outer = cons{int}{zero}(42)(inner) in
  let t = get_tail{int}{zero}(outer) in
  100
|}

let ( let* ) = Result.bind

let () =
  Printf.printf "=== Manual cons tail test ===\n%!";
  let result =
    Printf.printf "Stage 1: Parse...\n%!";
    let* (decs, defs) = Pipe.LangStage.to_melcore source in
    Printf.printf "Stage 2: Type check...\n%!";
    let* (decs, typed_defs) = Pipe.MelcoreStage.type_check decs defs in
    Printf.printf "Stage 3: Normalize...\n%!";
    let norm_defs = Pipe.MelcoreStage.normalize typed_defs in
    Printf.printf "Stage 4: Encode...\n%!";
    let* (types_ctx, core_defs) = Pipe.MelcoreStage.encode decs norm_defs in
    Printf.printf "Stage 5: Core type check...\n%!";
    let* (types_ctx, core_defs) = Pipe.CoreStage.type_check types_ctx core_defs in
    Printf.printf "Stage 6: Monomorphize...\n%!";
    let* mono_result = Pipe.CoreStage.monomorphize types_ctx core_defs in
    Printf.printf "Stage 7: Focus...\n%!";
    let* (focused_decs, focused_main, focused_defs) = 
      Pipe.CoreStage.focus types_ctx mono_result in
    Printf.printf "Stage 8: Focused type check (SKIPPING)...\n%!";
    (* let* _ = Pipe.FocusedStage.type_check focused_decs focused_defs in *)
    Printf.printf "Stage 9: Linearize...\n%!";
    let* (_axil_decs, axil_main, axil_defs) = 
      Pipe.AxilStage.linearize focused_decs focused_main focused_defs in
    Printf.printf "Stage 10: Axil type check (SKIPPING)...\n%!";
    (* let* _ = Pipe.AxilStage.type_check axil_decs axil_defs in *)
    Printf.printf "Stage 11: Compiling...\n%!";
    Sequent.Compile_checked.debug_subst := false;
    Sequent.Compile_checked.debug_store := false;
    let (code, _) = Sequent.Compile_checked.compile axil_main axil_defs in
    Printf.printf "Stage 12: Running (max 200 steps)...\n%!";
    let* result = Pipe.EmitStage.eval ~trace:false ~max_steps:200 code in
    Printf.printf "Result: %d (expected: 100)\n%!" result;
    Ok ()
  in
  match result with
  | Ok () -> ()
  | Error msg -> Printf.printf "Error: %s\n%!" msg
