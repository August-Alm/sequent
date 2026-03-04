(* Test GADT-indexed recursive construction - mirrors replicate *)
module Pipe = Sequent.Pipeline
module Path = Sequent.Common.Identifiers.Path
module APrint = Sequent.Axil.Printing
module ATerms = Sequent.Axil.Terms
module ACode = Sequent.Aarch64.Code.Code

(* Test: replicate then length then to_int *)
let source = {|
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

data vec: nat -> type where
  { nil: vec(zero)
  ; cons: {n: nat} int -> vec(n) -> vec(succ(n))
  }

let replicate{n: nat}(k: single_nat(n)): vec(n) =
  match k with
  { single_zero => nil
  ; single_succ{m}(kk) => cons{m}(42)(replicate{m}(kk))
  }

let length{k: nat}(v: vec(k)): single_nat(k) =
  match v with
  { nil => single_zero
  ; cons{n}(x)(xs) => single_succ{n}(length{n}(xs))
  }

let main: int =
  let n2 = single_succ{succ(zero)}(single_succ{zero}(single_zero)) in
  let v = replicate{succ(succ(zero))}(n2) in
  let l = length{succ(succ(zero))}(v) in
  to_int{succ(succ(zero))}(l)
|}

let ( let* ) = Result.bind

let () =
  Printf.printf "=== GADT Replicate Test ===\n%!";
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
    
    (* Print Axil IR *)
    Printf.printf "\n=== Axil Main ===\n%!";
    Printf.printf "%s\n\n%!" (APrint.command_to_string axil_main.body);
    
    Printf.printf "=== Axil Definitions ===\n%!";
    List.iter (fun (_, (def: ATerms.definition)) ->
      Printf.printf "--- %s ---\n%s\n\n%!" 
        (Path.name def.path)
        (APrint.command_to_string def.body)
    ) (Path.to_list axil_defs);
    
    Printf.printf "\n=== Compiling ===\n%!";
    let (code, _) = Sequent.Compile_checked.compile axil_main axil_defs in
    
    Printf.printf "\n=== Running ===\n%!";
    Printf.printf "Code length: %d instructions\n" (List.length code);
    let* result = Pipe.EmitStage.eval ~trace:true ~max_steps:200000 code in
    Printf.printf "=== Result: %d (expected: 2) ===\n%!" result;
    Ok result
  in
  match result with
  | Ok _ -> ()
  | Error msg -> Printf.printf "Error: %s\n%!" msg
