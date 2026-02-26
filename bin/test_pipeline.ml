(**
  Test suite for the full compilation pipeline.
  
  This test file:
  1. Parses surface syntax strings using Lang.Parse
  2. Desugars to Melcore using Desugar
  3. Type-checks in Melcore using Melcore.Terms
  4. Encodes to Core using Encode
  5. Type-checks in Core using Core.Terms
  6. Runs Monomorphize to generate monomorphic definitions
  7. Focuses to Focused IR
  8. Type-checks in Focused using Focused.Terms
  9. Evaluates using the abstract machine
  
  All test inputs contain a monomorphic "main" function that returns an int.
*)

open Common.Identifiers

module Pipe = Sequent.Pipeline
module MPrint = Melcore.Printing
module CPrint = Core.Printing
module FPrint = Focused.Printing
module FTerms = Focused.Terms
module FMachine = Focused.Semantics

(* Test harness *)
let test_count = ref 0
let pass_count = ref 0

(* ========================================================================= *)
(* Test Runner                                                               *)
(* ========================================================================= *)

let ( let* ) = Result.bind

let run_test ?(trace=false) ~name ~expected (source: string) =
  incr test_count;
  print_endline "════════════════════════════════════════════════════════════════";
  Printf.printf "Test %d: %s\n" !test_count name;
  print_endline "────────────────────────────────────────────────────────────────";
  
  print_endline "Source:";
  Printf.printf "%s\n\n" source;
  
  let result =
    (* Stage 1: Parse and desugar *)
    let* (decs, defs) = Pipe.LangStage.to_melcore source in
    print_endline "1. Parse + Desugar: OK";
    
    (* Stage 2: Melcore type-check *)
    let* (decs, typed_defs) = Pipe.MelcoreStage.type_check decs defs in
    print_endline "2. Melcore type-check: OK";
    
    (* Stage 3: Normalize *)
    let norm_defs = Pipe.MelcoreStage.normalize typed_defs in
    print_endline "3. Normalize: OK";
    
    (* Stage 4: Encode to Core *)
    let* (core_decs, core_defs) = Pipe.MelcoreStage.encode decs norm_defs in
    print_endline "4. Encode to Core: OK";
    (* Debug: print Core defs *)
    Path.to_list core_defs |> List.iter (fun (p, (def: Core.Terms.definition)) ->
      Printf.printf "   %s: %s\n" (Path.name p) (Core.Printing.command_to_string def.body)
    );
    
    (* Stage 5: Core type-check *)
    let core_decs_tbl = List.fold_left (fun acc (dec: Core.Types.CoreTypes.dec) ->
      Path.add dec.name dec acc
    ) Path.emptytbl core_decs in
    let* core_defs = Pipe.CoreStage.type_check core_decs_tbl core_defs in
    print_endline "5. Core type-check: OK";
    
    (* Stage 6: Monomorphize *)
    let* mono_result = Pipe.CoreStage.monomorphize core_defs in
    print_endline "6. Monomorphize: OK";
    Printf.printf "   Generated %d new declarations, %d definitions\n"
      (List.length mono_result.new_declarations)
      (List.length mono_result.definitions);
    (* Debug: print mono definitions *)
    List.iter (fun (def: Core.Terms.definition) ->
      Printf.printf "   Mono %s: %s\n" (Path.name def.path) (Core.Printing.command_to_string def.body)
    ) mono_result.definitions;
    
    (* Stage 7: Focus *)
    let* (focused_decs, focused_main, focused_defs) = 
      Pipe.CoreStage.focus core_decs_tbl mono_result in
    print_endline "7. Focus: OK";
    
    (* Print focused main *)
    print_endline "\nFocused main:";
    Printf.printf "%s\n\n" (FPrint.command_to_string focused_main.body);

    (* Print focused defs for debugging *)
    let def_list = Path.to_list focused_defs in
    if List.length def_list > 0 then begin
      print_endline "Focused definitions:";
      List.iter (fun (_, (def: FTerms.definition)) ->
        Printf.printf "  %s:\n%s\n\n" (Path.name def.path) (FPrint.command_to_string def.body)
      ) def_list
    end;
    
    (* Stage 8: Focused type-check *)
    let* _ = Pipe.FocusedStage.type_check focused_decs focused_defs in
    print_endline "8. Focused type-check: OK";
    
    (* Stage 9: Evaluate *)
    let* (final_cmd, final_env, steps) = 
      Pipe.FocusedStage.eval ~trace focused_main focused_defs in
    Printf.printf "9. Evaluate: OK (%d steps)\n" steps;
    
    (* Extract result using the semantics helper *)
    (match FMachine.get_result (final_cmd, final_env) with
    | Some (FMachine.IntVal n) -> Ok n
    | Some _ -> Error "Final result is not an int"
    | None -> Error ("Machine did not halt with a result. Final: " ^ FPrint.command_to_string final_cmd))
  in
  
  print_newline ();
  (match result with
  | Ok actual ->
      Printf.printf "Result: %d\n" actual;
      if actual = expected then begin
        Printf.printf "PASS ✓ (expected %d)\n" expected;
        incr pass_count
      end else
        Printf.printf "FAIL ✗ (expected %d, got %d)\n" expected actual
  | Error msg ->
      Printf.printf "FAIL ✗: %s\n" msg);
  print_newline ()

(* ========================================================================= *)
(* Test Cases                                                                *)
(* ========================================================================= *)

let () =
  print_endline "\n╔══════════════════════════════════════════════════════════════╗";
  print_endline "║              FULL PIPELINE TEST SUITE                        ║";
  print_endline "╚══════════════════════════════════════════════════════════════╝\n";

  (* Test 1: Simple literal return *)
  run_test
    ~name:"Simple literal return"
    ~expected:42
    {|
let main: int = 42
    |};

  (* Test 2: Simple arithmetic *)
  run_test
    ~name:"Simple addition"
    ~expected:7
    {|
let main: int = 3 + 4
    |};

  (* Test 3: Nested arithmetic *)
  run_test
    ~name:"Nested arithmetic"
    ~expected:10
    {|
let main: int = (2 + 3) + (1 + 4)
    |};

  (* Test 4: Subtraction *)
  run_test
    ~name:"Subtraction"
    ~expected:5
    {|
let main: int = 10 - 5
    |};

  (* Test 5: Mixed arithmetic *)
  run_test
    ~name:"Mixed arithmetic"
    ~expected:8
    {|
let main: int = (10 + 5) - 7
    |};

  (* Test 6: Ifz - zero case *)
  run_test
    ~name:"Ifz zero case"
    ~expected:1
    {|
let main: int = ifz(0) then 1 else 2
    |};

  (* Test 7: Ifz - nonzero case *)
  run_test
    ~name:"Ifz nonzero case"
    ~expected:2
    {|
let main: int = ifz(5) then 1 else 2
    |};

  (* Test 8: Let binding *)
  run_test
    ~name:"Let binding"
    ~expected:10
    {|
let main: int =
  let x = 4 in
  let y = 6 in
  x + y
    |};

  (* Test 9: Function application *)
  run_test
    ~name:"Function application"
    ~expected:15
    {|
let double(x: int): int = x + x

let main: int = double(7) + 1
    |};

  (* Test 10: Recursive function - simple countdown *)
  run_test
    ~name:"Recursive countdown"
    ~expected:0
    {|
let countdown(n: int): int =
  ifz(n) then 0 else countdown(n - 1)

let main: int = countdown(5)
    |};

  (* Test 11: Recursive sum *)
  run_test
    ~name:"Recursive sum"
    ~expected:15
    {|
let sum(n: int): int =
  ifz(n) then 0 else n + sum(n - 1)

let main: int = sum(5)
    |};

  (* Test 12: Simple data type - bool *)
  run_test
    ~name:"Bool data type"
    ~expected:1
    {|
data bool: type where
  { true: bool
  ; false: bool
  }

let bool_to_int(b: bool): int =
  match b with
  { true => 1
  ; false => 0
  }

let main: int = bool_to_int(true)
    |};

  (* Test 13: Bool negation *)
  run_test
    ~name:"Bool negation"
    ~expected:0
    {|
data bool: type where
  { true: bool
  ; false: bool
  }

let not(b: bool): bool =
  match b with
  { true => false
  ; false => true
  }

let bool_to_int(b: bool): int =
  match b with
  { true => 1
  ; false => 0
  }

let main: int = bool_to_int(not(true))
    |};

  (* Test 14: Option type - none case *)
  run_test
    ~name:"Option none"
    ~expected:0
    {|
data option: type -> type where
  { none: {a: type} option(a)
  ; some: {a: type} a -> option(a)
  }

let get_or_zero(opt: option(int)): int =
  match opt with
  { none{_} => 0
  ; some{_}(x) => x
  }

let main: int = get_or_zero(none{int})
    |};

  (* Test 15: Option type - some case *)
  run_test
    ~name:"Option some"
    ~expected:42
    {|
data option: type -> type where
  { none: {a: type} option(a)
  ; some: {a: type} a -> option(a)
  }

let get_or_zero(opt: option(int)): int =
  match opt with
  { none{_} => 0
  ; some{_}(x) => x
  }

let main: int = get_or_zero(some{int}(42))
    |};

  (* Test 16: Pair type *)
  run_test
    ~name:"Pair type"
    ~expected:6
    {|
data pair: type -> type -> type where
  { mk_pair: {a}{b} a -> b -> pair(a)(b)
  }

let fst{a}{b}(p: pair(a)(b)): a =
  match p with
  { mk_pair{_}{_}(x)(y) => x
  }

let snd{a}{b}(p: pair(a)(b)): b =
  match p with
  { mk_pair{_}{_}(x)(y) => y
  }

let main: int =
  let p = mk_pair{int}{int}(1)(2) in
  let q = mk_pair{int}{int}(3)(5) in
  fst{int}{int}(p) + snd{int}{int}(q)
    |};
  
  (* Test 17: Fibonacci *)
  run_test
    ~name:"Fibonacci"
    ~expected:8
    {|
let fib(n: int): int =
  ifz(n) then 0 else ifz(n - 1) then 1
  else fib(n - 1) + fib(n - 2)

let main: int = fib(6)
    |};

  (* Test 18: Complex *)
  run_test
    ~name:"Complex test with multiple features"
    ~expected:10
    {|
data option: type -> type where
  { none: {a} option(a)
  ; some: {a} a -> option(a)
  }

code stream: type -> type where
  { state: {a} stream(a) -> a
  ; next: {a} stream(a) -> option(stream(a))
  }

code algebra: type -> type -> type where
  { nil: {b}{c} algebra(b)(c) -> c
  ; cons: {b}{c} algebra(b)(c) -> b -> c -> c
  }

code foldable: type -> type where
  { fold: {d}{r} foldable(d) -> algebra(d)(r) -> r
  }

let ints_from(i: int): stream(int) =
  new { state => i
      ; next => some{stream(int)}(ints_from(i + 1))
      }

let nats: stream(int) = ints_from(0)

let take{e}(s: stream(e))(n: int): foldable(e) =
  new foldable(e)
  { fold{e}{t}(alg) =>
      ifz(n) then
        nil{e}{t}(alg)
      else
        match next{e}(s) with
        { none{_} => nil{e}{t}(alg)
        ; some{_}(s') =>
            let rest = take{e}(s')(n - 1) in
            let folded_rest = fold{e}{t}(rest)(alg) in
            cons{e}{t}(alg)(state{e}(s))(folded_rest)
        }
  }

let sum(l: foldable(int)): int =
  let alg =
    new algebra(int)(int)
    { nil => 0
    ; cons(h)(t) => h + t
    } in
  fold{int}{int}(l)(alg)

let main: int =
  let tetractys = take{int}(nats)(5) in
  sum(tetractys)
    |};

  (* Final Summary *)
  print_endline "════════════════════════════════════════════════════════════════";
  Printf.printf "Results: %d/%d tests passed\n" !pass_count !test_count;
  print_endline "════════════════════════════════════════════════════════════════"
