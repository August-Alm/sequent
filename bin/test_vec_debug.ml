(* Debug test - check structure of replicate result *)
module Pipe = Sequent.Pipeline

(* Test 1: Check if outer cons is really cons *)
let source1 = {|
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

let is_cons{a}{n: nat}(v: vec(a)(n)): int =
  match v with
  { nil{_} => 100
  ; cons{_}{m}(x)(xs) => 200
  }

let main: int =
  let n2 = single_succ{succ(zero)}(single_succ{zero}(single_zero)) in
  let v = replicate{int}{succ(succ(zero))}(42)(n2) in
  is_cons{int}{succ(succ(zero))}(v)
|}

(* Test 2: Just get tail - does it even run? *)
let source2 = {|
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

let get_tail{a}{n: nat}(v: vec(a)(succ(n))): vec(a)(n) =
  match v with
  { cons{_}{m}(x)(xs) => xs
  }

let main: int =
  let n2 = single_succ{succ(zero)}(single_succ{zero}(single_zero)) in
  let v = replicate{int}{succ(succ(zero))}(42)(n2) in
  let t = get_tail{int}{succ(zero)}(v) in
  123
|}

(* Test 3: Skipped - depends on test 2 *)
let _source3 = source1

let ( let* ) = Result.bind

let run_test ?(trace=false) name source expected =
  Printf.printf "=== %s ===\n%!" name;
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
    Sequent.Compile_checked.debug_subst := true;
    Sequent.Compile_checked.debug_store := true;
    let (code, _) = Sequent.Compile_checked.compile axil_main axil_defs in
    Sequent.Compile_checked.debug_subst := false;
    Sequent.Compile_checked.debug_store := false;
    let* result = Pipe.EmitStage.eval ~trace ~max_steps:500 code in
    Ok result
  in
  match result with
  | Ok actual -> 
      Printf.printf "Result: %d (expected %d) %s\n\n" actual expected 
        (if actual = expected then "✓" else "✗")
  | Error msg -> Printf.printf "Error: %s\n\n%!" msg

let () =
  run_test "is_cons(outer)" source1 200;  (* outer should be cons *)
  run_test "get_tail_constant" source2 123    (* just run get_tail, return constant *)
  (* run_test "second_head" source3 42  -- skipped, depends on test 2 *)
