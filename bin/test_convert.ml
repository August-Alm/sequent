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
    
    (* Step 3: Convert typed_terms to Core producer terms *)
    print_endline "\nStep 3: Converting to Core terms...";
    List.iter (fun (path, typed_td) ->
      let name = Common.Identifiers.Path.name path in
      print_endline (Printf.sprintf "  Converting definition: %s" name);
      let core_producer = Convert.convert typed_td.Terms.body in
      print_endline (Printf.sprintf "  ✓ Converted to Core producer:");
      
      (* Use the proper pretty-printer *)
      let producer_str = Core.Terms.producer_to_string ~depth:2 core_producer in
      print_endline (Printf.sprintf "    %s" producer_str)
    ) typed_defs.Terms.term_defs;
    
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
data nat: type where 
  { zero: nat
  ; succ: nat -> nat
  }

code stream: type -> type where
  { head: {a} stream(a) -> a
  ; tail: {a} stream(a) -> stream(a)
  }

let const_stream(x: nat): stream(nat) = 
  new stream(nat)
  { head{_}(self) => x
  ; tail{_}(self) => self
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
  
  print_endline "╔════════════════════════════════════════╗";
  print_endline "║  Test Suite Complete                   ║";
  print_endline "╚════════════════════════════════════════╝";
