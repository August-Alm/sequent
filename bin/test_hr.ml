(* Test like test 19 but simpler *)
module Pipe = Sequent.Pipeline

let source = {|
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
    let (code, _arg_count) = Sequent.Compile_checked.compile axil_main axil_defs in
    Printf.printf "%d instructions generated\n" (List.length code);
    let* result = Pipe.EmitStage.eval ~trace:false ~max_steps:50000 code in
    Printf.printf "Result: %d (expected: 42)\n" result;
    Ok ()
  in
  match result with
  | Ok () -> ()
  | Error msg -> Printf.printf "Error: %s\n" msg
