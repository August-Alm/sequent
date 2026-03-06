[@@@warning "-33"]

module Pipe = Sequent.Pipeline
module Compile = Sequent.Compile_checked

let ( let* ) = Result.bind

(* Test length on vec, then to_int - the full test *)
let test25_code = "
data nat: type where
  { zero: nat
  ; succ: nat -> nat
  }

data single_nat: nat -> type where
  { single_zero: single_nat(zero)
  ; single_succ: {n: nat} single_nat(n) -> single_nat(succ(n))
  }

data vec: nat -> type where
  { vnil: vec(zero)
  ; vcons: {n: nat} int -> vec(n) -> vec(succ(n))
  }

let length{n: nat}(v: vec(n)): single_nat(n) =
  match v with
  { vnil => single_zero
  ; vcons{m}(_, v') => single_succ{m}(length{m}(v'))
  }

let to_int{n: nat}(k: single_nat(n)): int =
  match k with
  { single_zero => 0
  ; single_succ{m}(k') => 1 + to_int{m}(k')
  }

let main: int =
  let v3 = vcons{succ(succ(zero))}(10, vcons{succ(zero)}(20, vcons{zero}(30, vnil))) in
  to_int{succ(succ(succ(zero)))}(length{succ(succ(succ(zero)))}(v3))
"

let () = 
  Compile.debug_store := true;
  Compile.debug_subst := true;
  print_endline "=== Testing to_int with single_succ^2 ===\n";
  match (
    let* (decs, defs) = Pipe.LangStage.to_melcore test25_code in
    let* (decs, typed_defs) = Pipe.MelcoreStage.type_check decs defs in
    let norm_defs = Pipe.MelcoreStage.normalize typed_defs in
    let* (types_ctx, core_defs) = Pipe.MelcoreStage.encode decs norm_defs in
    let* (types_ctx, core_defs) = Pipe.CoreStage.type_check types_ctx core_defs in
    let* mono_result = Pipe.CoreStage.monomorphize types_ctx core_defs in
    let* (focused_decs, focused_main, focused_defs) = 
      Pipe.CoreStage.focus types_ctx mono_result in
    let* (axil_decs, axil_main, axil_defs) = 
      Pipe.AxilStage.linearize focused_decs focused_main focused_defs in
    let* axil_defs = Pipe.AxilStage.type_check axil_decs axil_defs in
    (* Print AXIL defs too *)
    print_endline "=== AXIL defs ===";
    let defs_list = Sequent.Common.Identifiers.Path.to_list axil_defs in
    List.iter (fun (path, def) ->
      Printf.printf "DEF %s:\n" (Sequent.Common.Identifiers.Path.name path);
      Printf.printf "%s\n\n" (Sequent.Axil.Printing.command_to_string def.Sequent.Axil.Terms.body)
    ) defs_list;
    print_endline "=== AXIL main ===";
    print_endline (Sequent.Axil.Printing.command_to_string axil_main.body);
    print_endline "";
    let asm, _ = Compile.compile axil_main axil_defs in
    (* Print the generated ASM *)
    print_endline "=== Generated ASM ===";
    List.iteri (fun i instr -> 
      Printf.printf "%d: %s\n" (i * 4) (Sequent.Aarch64.Code.Code.to_string instr)
    ) asm;
    print_endline "\n=== Running ===";
    let* result = Pipe.EmitStage.eval ~trace:true ~max_steps:50000 asm in
    Printf.printf "Result: %d (expected 2 for 2 elements)\n" result;
    Ok ()
  ) with
  | Ok () -> ()
  | Error msg -> Printf.eprintf "Error: %s\n" msg
