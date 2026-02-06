(**
  Test file for Lang to Core conversion pipeline
  
  This tests the complete workflow:
  1. Parse surface syntax to Lang terms
  2. Type check with Lang type checker
  3. Convert typed_terms to Core producer terms
  4. Verify Core type checking (when implemented)
*)

open Lang
open Sequent

let print_separator () =
  print_endline "\n========================================\n"

let test_case name input =
  print_endline ("=== " ^ name ^ " ===\n");
  try
    (* Step 1: Parse surface syntax to Lang terms *)
    print_endline "Step 1: Parsing...";
    let ast_defs = Parse.parse_defs_string input in
    let defs = Syntax.to_definitions ast_defs in
    print_endline (Printf.sprintf "  ✓ Parsed %d type definitions and %d term definitions" 
      (List.length defs.Terms.type_defs) 
      (List.length defs.Terms.term_defs));
    
    (* Step 2: Type check with Lang type checker *)
    print_endline "\nStep 2: Type checking with Lang...";
    let typed_defs = Terms.check_all defs in
    print_endline (Printf.sprintf "  ✓ Type checked %d term definitions" 
      (List.length typed_defs.Terms.term_defs));
    
    (* Step 3: Convert to Core definitions *)
    print_endline "\nStep 3: Converting to Core definitions...";
    let core_defs = Convert.convert_definitions typed_defs in
    print_endline (Printf.sprintf "  ✓ Converted %d type definitions and %d term definitions" 
      (List.length core_defs.Core.Terms.type_defs)
      (List.length core_defs.Core.Terms.term_defs));
    
    (* Display the converted Core definitions before type checking *)
    print_endline "\n  Core type definitions:";
    (* Print type definitions with xtor details *)
    List.iter (fun (_, (type_def, _kind)) ->
      match type_def with
      | Common.Types.Data td ->
        print_endline (Common.Types.data_to_string false td ^ "\n")
      | Common.Types.Code td ->
        print_endline (Common.Types.code_to_string false td ^ "\n")
      | Common.Types.Prim (prim, _) ->
        print_endline (Common.Identifiers.Path.name prim ^ " --- primitive\n")
    ) core_defs.Core.Terms.type_defs;
    print_endline "\n  Core term definitions:";
    List.iter (fun (_path, core_td) ->
      let def_str = Core.Terms.term_def_to_string core_td in
      print_endline "";
      List.iter (fun line -> 
        print_endline ("  " ^ line)
      ) (String.split_on_char '\n' def_str)
    ) core_defs.Core.Terms.term_defs;
    
    (* Step 4: Type check Core definitions *)
    print_endline "\nStep 4: Type checking in Core...";
    Core.Terms.check_definitions core_defs;
    print_endline "  ✓ Core type checking passed";
    
    (* Display the converted Core definitions again *)
    print_endline "\n  Core definitions after type checking:";
    List.iter (fun (_path, core_td) ->
      let def_str = Core.Terms.term_def_to_string core_td in
      print_endline "";
      List.iter (fun line -> 
        print_endline ("  " ^ line)
      ) (String.split_on_char '\n' def_str)
    ) core_defs.Core.Terms.term_defs;
    
    print_endline "\n✓ All steps completed successfully!\n";
    print_separator ()
    
  with
  | Failure msg -> 
      print_endline (Printf.sprintf "\n✗ Failed: %s\n" msg);
      print_separator ()
  | e -> 
      print_endline (Printf.sprintf "\n✗ Unexpected error: %s\n" (Printexc.to_string e));
      print_separator ()

let () =
  print_endline "╔════════════════════════════════════════╗";
  print_endline "║  Lang → Core Conversion Test Suite    ║";
  print_endline "╚════════════════════════════════════════╝\n";
  
  (* Test 1: Simple nat constant *)
  test_case "Test 1: Nat constant" "
data nat: type where 
  { zero: nat
  ; succ: nat -> nat
  }

let my_zero: nat = zero
  ";
  
  (* Test 2: Identity function with nat *)
  test_case "Test 2: Identity function" "
data nat: type where 
  { zero: nat
  ; succ: nat -> nat
  }

let id(x: nat): nat = x
  ";
  
  (* Test 3: Lambda abstraction *)
  test_case "Test 3: Lambda abstraction with nat" "
data nat: type where 
  { zero: nat
  ; succ: nat -> nat
  }

let make_zero: nat -> nat = fun(x: nat) => zero
  ";
  
  (* Test 4: Let binding *)
  test_case "Test 4: Let binding" "
data nat: type where 
  { zero: nat
  ; succ: nat -> nat
  }

let with_let: nat = 
  let x = zero in
  let y = succ(x) in
  y
  ";
  
  (* Test 5: Polymorphic identity *)
  test_case "Test 5: Polymorphic identity" "
let poly_id{a}(x: a): a = x
  ";
  
  (* Test 6: Data type with constructor *)
  test_case "Test 6: Data type with constructor" "
data bool: type where 
  { true: bool
  ; false: bool
  }

let my_true: bool = true
  ";
  
  (* Test 7: Pattern matching *)
  test_case "Test 7: Pattern matching" "
data bool: type where 
  { true: bool
  ; false: bool
  }

let not(b: bool): bool = 
  match b with
  { true => false
  ; false => true
  }
  ";
  
  (* Test 8: Codata type with destructor *)
  test_case "Test 8: Codata type with destructor" "
code stream: type -> type where
  { head: {a} stream(a) -> a
  ; tail: {a} stream(a) -> stream(a)
  }

let const_stream{a}(x: a): stream(a) = 
  new stream(a)
  { head{_} => x
  ; tail{_} => const_stream{a}(x)
  }
  ";
  
  (* Test 9: Nested pattern matching *)
  test_case "Test 9: Nested pattern matching" "
data nat: type where 
  { zero: nat
  ; succ: nat -> nat
  }

data bool: type where 
  { true: bool
  ; false: bool
  }

let is_zero(n: nat): bool = 
  match n with
  { zero => true
  ; succ(m) => false
  }
  ";
  
  (* Test 10: mutual recursion *)
  test_case "Test 10: Mutual recursion" "
data bool: type where 
  { true: bool
  ; false: bool
  }

data nat: type where
  { zero: nat
  ; succ: nat -> nat
  }

let is_even (n: nat): bool = 
  match n with
  { zero => true
  ; succ(m) => is_odd(m)
  }

let is_odd (n: nat): bool =
  match n with
  { zero => false
  ; succ(m) => is_even(m)
  }
  ";  

  (* Test 11: Partial application *)
  test_case "Test 11: Partial application" "
data nat: type where
  { zero: nat
  ; succ: nat -> nat
  }

let add(x: nat)(y: nat): nat = 
  match x with
  { zero => y
  ; succ(m) => succ(add(m)(y))
  }

let add_one: nat -> nat = add(succ(zero))
  ";

  (* Test 12: Multi-argument function *)
  test_case "Test 12: Multi-argument function fully applied" "
data nat: type where
  { zero: nat
  ; succ: nat -> nat
  }

let add(x: nat)(y: nat): nat = 
  match x with
  { zero => y
  ; succ(m) => succ(add(m)(y))
  }

let three: nat = add(succ(zero))(succ(succ(zero)))
  ";

  (* Test 13: Top-level constant reference *)
  test_case "Test 13: Top-level constant reference" "
data nat: type where
  { zero: nat
  ; succ: nat -> nat
  }

let my_zero: nat = zero

let another_zero: nat = my_zero
  ";

  (* Test 14: Many lets *)
  test_case "Test 14: Many lets" "
data nat: type where
  { zero: nat
  ; succ: nat -> nat
  }

let add(x: nat)(y: nat): nat = 
  match x with
  { zero => y
  ; succ(m) => succ(add(m)(y))
  }

let foo(a: nat): nat =
  let f = add(a) in
  let one = succ(zero) in
  f(one)
  ";

  print_endline "╔════════════════════════════════════════╗";
  print_endline "║  Test Suite Complete                   ║";
  print_endline "╚════════════════════════════════════════╝";
