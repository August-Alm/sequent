(* Minimal test to trace replicate execution *)
module Pipe = Sequent.Pipeline
module Path = Sequent.Common.Identifiers.Path
module APrint = Sequent.Axil.Printing
module ATerms = Sequent.Axil.Terms

(* Simple replicate with tracing *)
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
  ; single_succ{m}(kk) => cons{a}{m}(x)(replicate{a}{m}(x)(kk))
  }

let length{a}{k: nat}(v: vec(a)(k)): int =
  match v with
  { nil{_} => 0
  ; cons{_}{n}(x)(xs) => 1 + length{a}{n}(xs)
  }

let main: int =
  let n2 = single_succ{succ(zero)}(single_succ{zero}(single_zero)) in
  let v = replicate{int}{succ(succ(zero))}(42)(n2) in
  length{int}{succ(succ(zero))}(v)
|}

let ( let* ) = Result.bind

let () =
  Printf.printf "=== Replicate Test ===\n%!";
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
    
    (* Print Axil definitions *)
    Printf.printf "\n=== Axil Definitions ===\n%!";
    List.iter (fun (_, (def: ATerms.definition)) ->
      Printf.printf "--- %s ---\n%s\n\n%!" 
        (Path.name def.path)
        (APrint.command_to_string def.body)
    ) (Path.to_list axil_defs);
    
    Printf.printf "\n=== Axil Main ===\n%!";
    Printf.printf "%s\n\n%!" (APrint.command_to_string axil_main.body);
    
    Printf.printf "\n=== Compiling ===\n%!";
    Sequent.Compile_checked.debug_subst := false;
    Sequent.Compile_checked.debug_store := false;
    let (code, _) = Sequent.Compile_checked.compile axil_main axil_defs in
    Sequent.Compile_checked.debug_subst := false;
    Sequent.Compile_checked.debug_store := false;
    
    Printf.printf "\n=== Generated Code ===\n%!";
    Printf.printf "%s\n" (Sequent.Aarch64.Code.Code.list_to_string code);
    
    Printf.printf "\n=== Running with trace ===\n%!";
    let* result = Pipe.EmitStage.eval ~trace:false ~max_steps:5000 code in
    Printf.printf "\n=== Result: %d (expected: 2) ===\n%!" result;
    Ok result
  in
  match result with
  | Ok _ -> ()
  | Error msg -> Printf.printf "Error: %s\n%!" msg
