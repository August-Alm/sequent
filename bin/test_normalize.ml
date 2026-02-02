(**
  Test file for full compilation pipeline: Lang → Core → Cut
  
  This tests the complete workflow:
  1. Parse surface syntax to Lang terms
  2. Type check with Lang type checker
  3. Convert typed_terms to Core definitions
  4. Type check Core definitions
  5. Normalize Core to Cut definitions (naming, shrinking, collapsing, linearization)
  6. Type check Cut definitions
*)

open Lang
open Sequent

let print_separator () =
  print_endline "\n========================================\n"

(** Build a basic extern environment with primitive operations *)
let build_extern_env () : Cut.Terms.extern_env =
  let open Common.Types.Prim in
  let open Common.Identifiers in
  let int_ty = Cut.Types.TyPrim (int_sym, Cut.Types.KStar) in
  [ (* Integer literal: () -> (v: ext int) *)
    (Path.of_string "lit", 
     ([], [[Ident.mk "v", Cut.Types.Ext int_ty]]))
  ; (* Addition: (v1: ext int, v2: ext int) -> (result: ext int) *)
    (Path.of_string "add",
     ([Cut.Types.Ext int_ty; Cut.Types.Ext int_ty], [[Ident.mk "result", Cut.Types.Ext int_ty]]))
  ; (* If-zero: (v: ext int) -> () | () (two branches, both with no bindings) *)
    (Path.of_string "ifz",
     ([Cut.Types.Ext int_ty], [[]; []]))
  ]

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
    
    (* Display Core definitions *)
    print_endline "\n  Core term definitions:";
    List.iter (fun (path, core_td) ->
      let def_str = Core.Terms.term_def_to_string core_td in
      print_endline "";
      List.iter (fun line -> 
        print_endline ("    " ^ line)
      ) (String.split_on_char '\n' def_str)
    ) core_defs.Core.Terms.term_defs;
    
    (* Step 4: Type check Core definitions *)
    print_endline "\nStep 4: Type checking in Core...";
    Core.Terms.check_definitions core_defs;
    print_endline "  ✓ Core type checking passed";
    
    (* Step 5: Normalize Core to Cut definitions *)
    print_endline "\nStep 5: Normalizing to Cut (Pass A + Pass B)...";
    let cut_defs = Normalization.normalize_definitions core_defs in
    print_endline (Printf.sprintf "  ✓ Normalized to %d signatures and %d definitions" 
      (List.length cut_defs.Cut.Terms.signatures)
      (List.length cut_defs.Cut.Terms.program));
    
    (* Display Cut signatures *)
    print_endline "\n  Cut signatures:";
    List.iter (fun (ty_sym, (sig_def, _kind)) ->
      let ty_name = Common.Identifiers.Path.name ty_sym in
      print_endline (Printf.sprintf "    signature %s = {" ty_name);
      List.iter (fun (msig: Cut.Types.method_sig) ->
        let method_name = Common.Identifiers.Path.name msig.symbol in
        let prod_str = String.concat ", " (List.map Cut.Types.Pretty.typed_param_to_string msig.producers) in
        let cons_str = String.concat ", " (List.map Cut.Types.Pretty.typed_param_to_string msig.consumers) in
        let sig_str = if prod_str = "" && cons_str = "" then "()" 
                     else if cons_str = "" then "(" ^ prod_str ^ ")" 
                     else "(" ^ prod_str ^ " | " ^ cons_str ^ ")" in
        print_endline (Printf.sprintf "      %s%s" method_name sig_str)
      ) sig_def.Cut.Types.methods;
      print_endline "    }"
    ) cut_defs.Cut.Terms.signatures;
    
    (* Display Cut program *)
    print_endline "\n  Cut program:";
    List.iter (fun (label, gamma, stmt) ->
      let label_str = Cut.Terms.Label.to_string label in
      let gamma_str = Cut.Terms.string_of_typ_env gamma in
      print_endline (Printf.sprintf "\n    define %s(%s) =" label_str gamma_str);
      let stmt_str = Cut.Terms.string_of_statement ~indent:3 stmt in
      List.iter (fun line ->
        print_endline line
      ) (String.split_on_char '\n' stmt_str)
    ) cut_defs.Cut.Terms.program;
    
    (* Step 6: Type check Cut definitions *)
    print_endline "\n\nStep 6: Type checking in Cut...";
    let extern_env = build_extern_env () in
    Cut.Terms.check_program 
      cut_defs.Cut.Terms.signatures 
      extern_env
      cut_defs.Cut.Terms.program;
    print_endline "  ✓ Cut type checking passed";
    
    print_endline "\n✓ All steps completed successfully!\n";
    print_separator ()
    
  with
  | Cut.Terms.TypeError msg ->
      print_endline (Printf.sprintf "\n✗ Cut type error: %s\n" msg);
      print_separator ()
  | Failure msg -> 
      print_endline (Printf.sprintf "\n✗ Failed: %s\n" msg);
      print_separator ()
  | e -> 
      print_endline (Printf.sprintf "\n✗ Unexpected error: %s\n" (Printexc.to_string e));
      Printexc.print_backtrace stdout;
      print_separator ()

let () =
  print_endline "╔════════════════════════════════════════╗";
  print_endline "║  Lang → Core → Cut Test Suite         ║";
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
  
  (* Test 3b: Lambda abstraction, non-value *)
  test_case "Test 3b: Lambda abstraction with nat, non-value" "
data nat: type where 
  { zero: nat
  ; succ: nat -> nat
  }

let make_zero(y: nat): nat -> nat = fun(x: nat) => zero
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
  
  (* Test 10: Mutual recursion *)
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

  print_endline "╔════════════════════════════════════════╗";
  print_endline "║  Test Suite Complete                   ║";
  print_endline "╚════════════════════════════════════════╝";
