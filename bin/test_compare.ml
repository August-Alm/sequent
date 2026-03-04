(** Minimal test comparing test 19 vs test 20 *)

module Pipe = Sequent.Pipeline
module ACode = Aarch64.Code

let ( let* ) = Result.bind

[@@@warning "-27"]

let test_and_trace ~name ~expected ?(trace=false) (source: string) =
  Printf.printf "\n=== %s ===\n\n" name;
  
  let result =
    let* (decs, defs) = Pipe.LangStage.to_melcore source in
    let* (decs, typed_defs) = Pipe.MelcoreStage.type_check decs defs in
    let norm_defs = Pipe.MelcoreStage.normalize typed_defs in
    let* (types_ctx, core_defs) = Pipe.MelcoreStage.encode decs norm_defs in
    let* (types_ctx, core_defs) = Pipe.CoreStage.type_check types_ctx core_defs in
    let* mono_result = Pipe.CoreStage.monomorphize types_ctx core_defs in
    let* (focused_decs, focused_main, focused_defs) = 
      Pipe.CoreStage.focus types_ctx mono_result in
    let* (_axil_decs, axil_main, axil_defs) = 
      Pipe.AxilStage.linearize focused_decs focused_main focused_defs in
    let* (asm_code, _) = 
      Pipe.EmitStage.compile Pipe.EmitStage.AARCH64 axil_main axil_defs in
    
    Printf.printf "Aarch64 code:\n%s\n" (ACode.Code.list_to_string asm_code);
    
    let* result = Pipe.EmitStage.eval ~trace ~max_steps:5000 asm_code in
    Ok result
  in
  
  match result with
  | Ok actual when actual = expected ->
      Printf.printf "\nResult: %d - PASS (expected %d)\n" actual expected
  | Ok actual ->
      Printf.printf "\nResult: %d - FAIL (expected %d)\n" actual expected
  | Error msg ->
      Printf.printf "\nERROR: %s\n" msg

let test19 = {|
data tuple: type -> type -> type where
  { mk_tuple: {a}{b} a -> b -> tuple(a)(b)
  }

data enum: type where
  { A: enum
  ; B: enum
  }

let map_mk_tuple{a}{b}(f: {c} c -> c)(x: a)(y: b): tuple(a)(b) =
  mk_tuple{a}{b}(f{a}(x))(f{b}(y))

let id{a}(x: a): a = x

let main: int =
  let t = map_mk_tuple{int}{enum}(id)(5)(B) in
  match t with
  { mk_tuple{_}{_}(x)(y) =>
      match y with
      { A => 0
      ; B => x
      }
  }
|}

let test20 = {|
data tuple: type -> type -> type where
  { mk_tuple: {a}{b} a -> b -> tuple(a)(b)
  }

data enum: type where
  { A: enum
  ; B: enum
  }

let map_mk_tuple{a}{b}(f: {c} c -> c)(x: a)(y: b): tuple(a)(b) =
  mk_tuple{a}{b}(f{a}(x))(f{b}(y))

let main: int =
  let f = fun{c}(z: c) => z in
  let t = map_mk_tuple{int}{enum}(f)(5)(B) in
  match t with
  { mk_tuple{_}{_}(x)(y) =>
      match y with
      { A => 0
      ; B => x
      }
  }
|}

let () =
  test_and_trace ~name:"Test 19 (named id)" ~expected:5 test19;
  test_and_trace ~name:"Test 20 (anonymous f)" ~expected:5 ~trace:true test20
