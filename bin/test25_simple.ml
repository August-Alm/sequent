[@@@warning "-33"]
open Common.Identifiers

module Pipe = Sequent.Pipeline
module FPrint = Focused.Printing

let ( let* ) = Result.bind

(* Test vec_length on nil - should return 0 *)
let code_nil = {|
data nat: type where
  { zero: nat
  ; succ: nat -> nat
  }

data vec: type -> nat -> type where
  { nil: {a} vec(a)(zero)
  ; cons: {a}{n: nat} a -> vec(a)(n) -> vec(a)(succ(n))
  }

let vec_length{a}{n: nat}(v: vec(a)(n)): int =
  match v with
  { nil{_} => 0
  ; cons{_}{m}(x)(xs) => 1 + vec_length{a}{m}(xs)
  }

let main: int =
  vec_length{int}{zero}(nil{int})
|}

(* Test vec_length on 1-element - should return 1 *)
let code_one = {|
data nat: type where
  { zero: nat
  ; succ: nat -> nat
  }

data vec: type -> nat -> type where
  { nil: {a} vec(a)(zero)
  ; cons: {a}{n: nat} a -> vec(a)(n) -> vec(a)(succ(n))
  }

let vec_length{a}{n: nat}(v: vec(a)(n)): int =
  match v with
  { nil{_} => 0
  ; cons{_}{m}(x)(xs) => 1 + vec_length{a}{m}(xs)
  }

let main: int =
  vec_length{int}{succ(zero)}(cons{int}{zero}(42)(nil{int}))
|}

(* Test vec_length on 2-element - should return 2 *)
let code_two = {|
data nat: type where
  { zero: nat
  ; succ: nat -> nat
  }

data vec: type -> nat -> type where
  { nil: {a} vec(a)(zero)
  ; cons: {a}{n: nat} a -> vec(a)(n) -> vec(a)(succ(n))
  }

let vec_length{a}{n: nat}(v: vec(a)(n)): int =
  match v with
  { nil{_} => 0
  ; cons{_}{m}(x)(xs) => 1 + vec_length{a}{m}(xs)
  }

let main: int =
  vec_length{int}{succ(succ(zero))}(cons{int}{succ(zero)}(42)(cons{int}{zero}(43)(nil{int})))
|}

(* Test vec_length on replicate - should return 2 *)
let code_replicate = {|
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

(* Test replicate with just 1 element - should return 1 *)
let code_replicate_1 = {|
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
  let v = replicate{int}{succ(zero)}(42)(s1) in
  vec_length{int}{succ(zero)}(v)
|}

let run_test ?(trace=false) name code expected =
  Printf.printf "=== Test: %s (expected %d) ===\n" name expected;
  match (
    let* (decs, defs) = Pipe.LangStage.to_melcore code in
    let* (decs, typed_defs) = Pipe.MelcoreStage.type_check decs defs in
    let norm_defs = Pipe.MelcoreStage.normalize typed_defs in
    let* (types_ctx, core_defs) = Pipe.MelcoreStage.encode decs norm_defs in
    let* (types_ctx, core_defs) = Pipe.CoreStage.type_check types_ctx core_defs in
    let* mono_result = Pipe.CoreStage.monomorphize types_ctx core_defs in
    let* (focused_decs, focused_main, focused_defs) = 
      Pipe.CoreStage.focus types_ctx mono_result in
    
    let* (axil_decs, axil_main, axil_defs) = 
      Pipe.AxilStage.linearize focused_decs focused_main focused_defs in
    let* (asm, _) = Pipe.EmitStage.compile Pipe.EmitStage.AARCH64 axil_main axil_defs in
    let* result = Pipe.EmitStage.eval ~trace:trace ~max_steps:10000 asm in
    
    Printf.printf "Result: %d (expected %d) %s\n\n" result expected 
      (if result = expected then "PASS" else "FAIL");
    Ok ()
  ) with
  | Ok () -> ()
  | Error msg -> Printf.printf "Error: %s\n" msg

let () =
  run_test "nil" code_nil 0;
  run_test "one" code_one 1;
  run_test "two" code_two 2;
  run_test "replicate_1" code_replicate_1 1;
  run_test ~trace:true "replicate" code_replicate 2
