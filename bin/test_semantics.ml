(**
  Test file for full compilation pipeline with execution: Lang → Core → Cut → Semantics
  
  This tests the complete workflow:
  1. Parse surface syntax to Lang terms
  2. Type check with Lang type checker
  3. Convert typed_terms to Core definitions
  4. Type check Core definitions
  5. Normalize Core to Cut definitions (naming, shrinking, collapsing, linearization)
  6. Type check Cut definitions
  7. Execute Cut program with abstract machine semantics
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
  ; (* Return: (v: ext int) -> () (terminates and prints value) *)
    (Path.of_string "return",
     ([Cut.Types.Ext int_ty], []))
  ]

let test_case name input expected_output =
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
    
    (* Step 7: Execute with abstract machine semantics *)
    print_endline "\nStep 7: Executing with abstract machine...";
    (match cut_defs.Cut.Terms.program with
    | [] -> print_endline "  ✗ No program to execute"
    | (label, gamma, _) :: _ ->
      print_endline (Printf.sprintf "  Starting execution from label: %s" (Cut.Terms.Label.to_string label));
      print_endline (Printf.sprintf "  Parameters: %s" (Cut.Terms.string_of_typ_env gamma));
      
      (* Create a simple return continuation that prints the result *)
      let return_branches = 
        (* Get the nat signature to know which branches we need *)
        let nat_sig = List.find_opt (fun (sym, _) ->
          Common.Identifiers.Path.name sym = "nat"
        ) cut_defs.Cut.Terms.signatures in
        match nat_sig with
        | Some (_, (sig_def, _)) ->
          (* Create branches for each constructor that prints the constructor name *)
          List.map (fun (msig: Cut.Types.method_sig) ->
            let symbol = msig.Cut.Types.symbol in
            let symbol_name = Common.Identifiers.Path.name symbol in
            (* Create a dummy terminate statement by using extern return with proper variable *)
            (* We need to pass a variable that will be in the environment *)
            (* For now, create a statement that just does extern return {} which terminates *)
            let return_sym = Common.Identifiers.Path.of_string ("return_" ^ symbol_name) in
            let stmt = Cut.Terms.Extern (return_sym, [], []) in
            (symbol, stmt)
          ) sig_def.Cut.Types.methods
        | None -> []
      in
      
      (* Create initial environment with the return continuation *)
      let initial_env = List.map (fun (var, _ty) ->
        (var, Cut.Semantics.Consumer ([], return_branches))
      ) gamma in
      
      let final_config = Cut.Semantics.eval_program ~max_steps:1000 cut_defs.Cut.Terms.program label initial_env in
      print_endline (Printf.sprintf "  Final configuration: %s" (Cut.Semantics.config_to_string final_config));
      print_endline (Printf.sprintf "  ✓ Execution completed"));
    
    (* Check expected output if provided *)
    (match expected_output with
     | Some expected ->
       print_endline (Printf.sprintf "\nExpected output: %s" expected);
       print_endline "  (Note: Output verification not yet implemented)"
     | None -> ());
    
    print_endline "\n✓ All steps completed successfully!\n";
    print_separator ()
    
  with
  | Cut.Semantics.RuntimeError msg ->
      print_endline (Printf.sprintf "\n✗ Runtime error: %s\n" msg);
      print_separator ()
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
  print_endline "║  Lang → Core → Cut → Semantics Test   ║";
  print_endline "╚════════════════════════════════════════╝\n";
  
  (* Test 1: Simple nat constant *)
  test_case "Test 1: Nat constant" "
data nat: type where 
  { zero: nat
  ; succ: nat -> nat
  }

let my_zero: nat = zero
  " None;

  (* Test 2: Integer addition *)
  test_case "Test 2: Integer addition" "
let test_add: int = 3 + 5
  " None
