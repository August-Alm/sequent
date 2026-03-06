[@@@warning "-33"]
open Common.Identifiers

module Pipe = Sequent.Pipeline
module CPrint = Axil.Printing

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

let to_int{n: nat}(k: single_nat(n)): int =
  match k with
  { single_zero => 0
  ; single_succ{m}(k') => 1 + to_int{m}(k')
  }

data vec: type -> nat -> type where
  { nil: {a} vec(a)(zero)
  ; cons: {a}{n: nat} a -> vec(a)(n) -> vec(a)(succ(n))
  }

let length{a}{n: nat}(v: vec(a)(n)): single_nat(n) =
  match v with
  { nil{_} => single_zero
  ; cons{_}{m}(x)(xs) => single_succ{m}(length{a}{m}(xs))
  }

let main: int =
  let v0 = nil{int} in
  let v1 = cons{int}{zero}(1)(v0) in
  let v2 = cons{int}{succ(zero)}(2)(v1) in
  let l = length{int}{succ(succ(zero))}(v2) in
  to_int{succ(succ(zero))}(l)
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
    
    let* (axil_decs, axil_main, axil_defs) = 
      Pipe.AxilStage.linearize focused_decs focused_main focused_defs in
    
    Printf.printf "=== AXIL DEFINITIONS ===\n\n";
    List.iter (fun (name, (def : Pipe.EmitStage.ATm.definition)) ->
      Printf.printf "--- %s ---\n%s\n\n" (Path.name name) (CPrint.command_to_string def.body)
    ) (Path.to_list axil_defs);
    
    Printf.printf "=== AXIL MAIN ===\n%s\n" (CPrint.command_to_string axil_main.body);
    
    Ok ()
  ) with
  | Ok () -> ()
  | Error msg -> Printf.printf "Error: %s\n" msg
