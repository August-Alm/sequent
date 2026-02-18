(* Test runner for simple.ml: Fun → Source → Target → Collapsed pipeline *)

open Sequent.Simple
open Common.Identifiers

(* ========================================================================= *)
(* Fun Type Definitions                                                      *)
(* ========================================================================= *)

(* Unit type in Fun: one nullary constructor *)
let unit_tpe : Fun.tpe = Fun.Data [[]]

(* Bool type in Fun: two nullary constructors *)
let _bool_tpe : Fun.tpe = Fun.Data [[]; []]

(* Function type constructor *)
let ( @-> ) (a : Fun.tpe) (b : Fun.tpe) : Fun.tpe = Fun.Fun (a, b)

(* ========================================================================= *)
(* Test Harness                                                              *)
(* ========================================================================= *)

(** Run a test case through the full pipeline:
    1. Start with Fun term
    2. Encode to Source
    3. Cut with return continuation
    4. Transform and Collapse
    5. Type check
*)
let run_test (name : string) (ctx : Encode.ctx) (term : Fun.term) =
  Printf.printf "\n%s\n" name;
  Printf.printf "────────────────────────────────────────────────────────────────\n";
  try
    (* Show the original Fun term *)
    Printf.printf "Fun Term: %s\n" (Fun.show_term term);
    
    (* Infer the type of the Fun term *)
    let fun_tpe = Encode.infer_exn ctx term in
    let tpe' = Encode.encode_tpe fun_tpe in
    Printf.printf "Fun Type: %s\n" (Fun.show_tpe fun_tpe);
    Printf.printf "Source Type: %s\n" (show_tpe tpe');
    
    (* Encode the term to Source *)
    let encoded = Encode.encode_term ctx term in
    Printf.printf "\nSource Term:\n  %s\n" (Source.show_term encoded);
    
    (* Create a return continuation and cut *)
    let ret = Ident.fresh () in
    let cmd = match tpe' with
      | Int ->
          Source.CutInt (encoded, Source.MuInt (ret, Source.RetInt ret))
      | Pos sig_ -> 
          Source.CutPos (sig_, encoded, Source.MuRhsPos (sig_, ret, Source.Ret (sig_, ret)))
      | Neg sig_ -> 
          Source.CutNeg (sig_, encoded, Source.MuRhsNeg (sig_, ret, Source.Ret (sig_, ret)))
    in
    Printf.printf "\nSource Command:\n  %s\n" (Source.show_command cmd);
    
    (* Transform and Collapse *)
    let collapsed = Collapse.from_source cmd in
    Printf.printf "\nCollapsed:\n  %s\n" (Collapsed.show_command collapsed);
    
    (* Type check *)
    match Collapsed.typecheck collapsed with
    | Ok () -> Printf.printf "\nTypecheck: PASS ✓\n"
    | Error e -> Printf.printf "\nTypecheck: FAIL: %s\n" (Collapsed.show_error e)
  with
  | Failure msg -> Printf.printf "FAIL (transform): %s\n" msg
  | e -> Printf.printf "EXCEPTION: %s\n" (Printexc.to_string e)

(* ========================================================================= *)
(* Test 1: Unit value                                                        *)
(* ========================================================================= *)

(** Unit constructor: Ctor(Unit, 0, []) *)
let test_unit () =
  let term = Fun.Ctor ([[]], 0, []) in
  run_test "Test 1 (unit value)" Ident.emptytbl term

(* ========================================================================= *)
(* Test 2: Identity function                                                 *)
(* ========================================================================= *)

(** λx:Unit. x *)
let test_identity () =
  let x = Ident.mk "x" in
  let term = Fun.Lam (x, unit_tpe, Fun.Var x) in
  run_test "Test 2 (identity λx.x)" Ident.emptytbl term

(* ========================================================================= *)
(* Test 3: Constant function                                                 *)
(* ========================================================================= *)

(** λx:Unit. λy:Unit. x *)
let test_const () =
  let x = Ident.mk "x" in
  let y = Ident.mk "y" in
  let term = Fun.Lam (x, unit_tpe, Fun.Lam (y, unit_tpe, Fun.Var x)) in
  run_test "Test 3 (const λx.λy.x)" Ident.emptytbl term

(* ========================================================================= *)
(* Test 4: Function application                                              *)
(* ========================================================================= *)

(** (λx:Unit. x) () *)
let test_app () =
  let x = Ident.mk "x" in
  let id = Fun.Lam (x, unit_tpe, Fun.Var x) in
  let unit_val = Fun.Ctor ([[]], 0, []) in
  let term = Fun.App (id, unit_val) in
  run_test "Test 4 (app (λx.x) ())" Ident.emptytbl term

(* ========================================================================= *)
(* Test 5: Boolean true                                                      *)
(* ========================================================================= *)

(** Ctor(Bool, 0, []) - true *)
let test_bool_true () =
  let term = Fun.Ctor ([[];[]], 0, []) in
  run_test "Test 5 (bool true)" Ident.emptytbl term

(* ========================================================================= *)
(* Test 6: Case expression                                                   *)
(* ========================================================================= *)

(** case true of { true ⇒ (); false ⇒ () } *)
let test_case () =
  let bool_sig = [[];[]] in
  let true_val = Fun.Ctor (bool_sig, 0, []) in
  let unit_val = Fun.Ctor ([[]], 0, []) in
  let term = Fun.Case (bool_sig, true_val, [
    ([], unit_val);  (* true branch *)
    ([], unit_val)   (* false branch *)
  ]) in
  run_test "Test 6 (case true of ...)" Ident.emptytbl term

(* ========================================================================= *)
(* Test 7: Higher-order function                                             *)
(* ========================================================================= *)

(** λf:(Unit→Unit). f () *)
let test_higher_order () =
  let f = Ident.mk "f" in
  let fun_tpe = unit_tpe @-> unit_tpe in
  let unit_val = Fun.Ctor ([[]], 0, []) in
  let term = Fun.Lam (f, fun_tpe, Fun.App (Fun.Var f, unit_val)) in
  run_test "Test 7 (λf. f ())" Ident.emptytbl term

(* ========================================================================= *)
(* Test 8: Nested application                                                *)
(* ========================================================================= *)

(** (λf. f ()) (λx. x) *)
let test_nested_app () =
  let f = Ident.mk "f" in
  let x = Ident.mk "x" in
  let fun_tpe = unit_tpe @-> unit_tpe in
  let unit_val = Fun.Ctor ([[]], 0, []) in
  let apply_f = Fun.Lam (f, fun_tpe, Fun.App (Fun.Var f, unit_val)) in
  let id = Fun.Lam (x, unit_tpe, Fun.Var x) in
  let term = Fun.App (apply_f, id) in
  run_test "Test 8 ((λf. f ()) (λx. x))" Ident.emptytbl term

(* ========================================================================= *)
(* Test 9: Pair type (data with args)                                        *)
(* ========================================================================= *)

(** Pair((), ()) where Pair : Unit × Unit → PairType *)
let test_pair () =
  let pair_sig = [[unit_tpe; unit_tpe]] in  (* one ctor with two Unit args *)
  let unit_val = Fun.Ctor ([[]], 0, []) in
  let term = Fun.Ctor (pair_sig, 0, [unit_val; unit_val]) in
  run_test "Test 9 (pair ((), ()))" Ident.emptytbl term

(* ========================================================================= *)
(* Test 10: Case with binding                                                *)
(* ========================================================================= *)

(** case Pair((), ()) of { Pair(x, y) ⇒ x } *)
let test_case_binding () =
  let pair_sig = [[unit_tpe; unit_tpe]] in
  let unit_val = Fun.Ctor ([[]], 0, []) in
  let pair_val = Fun.Ctor (pair_sig, 0, [unit_val; unit_val]) in
  let x = Ident.mk "x" in
  let y = Ident.mk "y" in
  let term = Fun.Case (pair_sig, pair_val, [
    ([x; y], Fun.Var x)
  ]) in
  run_test "Test 10 (case Pair((),()) of Pair(x,y) ⇒ x)" Ident.emptytbl term

(* ========================================================================= *)
(* Test 11: Cocase (lazy/thunk)                                              *)
(* ========================================================================= *)

(** cocase { force(k) ⇒ () } - a thunk that returns unit when forced *)
let test_cocase () =
  let k = Ident.mk "k" in
  let thunk_sig = [[unit_tpe]] in  (* one dtor: force() → Unit *)
  let unit_val = Fun.Ctor ([[]], 0, []) in
  let term = Fun.Cocase (thunk_sig, [
    ([k], unit_val)  (* force(k) ⇒ () *)
  ]) in
  run_test "Test 11 (cocase { force(k) ⇒ () })" Ident.emptytbl term

(* ========================================================================= *)
(* Test 12: Destructor application (forcing a thunk)                         *)
(* ========================================================================= *)

(** (cocase { force(k) ⇒ () }).force() *)
let test_dtor () =
  let k = Ident.mk "k" in
  let thunk_sig = [[unit_tpe]] in
  let unit_val = Fun.Ctor ([[]], 0, []) in
  let thunk = Fun.Cocase (thunk_sig, [([k], unit_val)]) in
  let term = Fun.Dtor (thunk_sig, 0, [thunk]) in  (* subject only, no extra args *)
  run_test "Test 12 (thunk.force())" Ident.emptytbl term

(* ========================================================================= *)
(* Test 13: Integer literal                                                  *)
(* ========================================================================= *)

(** 42 *)
let test_lit () =
  let term = Fun.Lit 42 in
  run_test "Test 13 (lit 42)" Ident.emptytbl term

(* ========================================================================= *)
(* Test 14: Addition                                                         *)
(* ========================================================================= *)

(** add(1, 2) *)
let test_add () =
  let term = Fun.Add (Fun.Lit 1, Fun.Lit 2) in
  run_test "Test 14 (add 1 2)" Ident.emptytbl term

(* ========================================================================= *)
(* Test 15: Nested addition                                                  *)
(* ========================================================================= *)

(** add(add(1, 2), 3) *)
let test_nested_add () =
  let term = Fun.Add (Fun.Add (Fun.Lit 1, Fun.Lit 2), Fun.Lit 3) in
  run_test "Test 15 (add (add 1 2) 3)" Ident.emptytbl term

(* ========================================================================= *)
(* Test 16: Identity on Int                                                  *)
(* ========================================================================= *)

(** λx:Int. x *)
let test_int_identity () =
  let x = Ident.mk "x" in
  let term = Fun.Lam (x, Fun.Int, Fun.Var x) in
  run_test "Test 16 (λx:Int. x)" Ident.emptytbl term

(* ========================================================================= *)
(* Test 17: Execute (λx:Int. x+1)(9) with Machine                            *)
(* ========================================================================= *)

(** (λx:Int. x + 1)(9) — compile and execute, expect result 10 *)
let test_machine_add_one () =
  Printf.printf "\nTest 17 (machine execution: (λx:Int. x+1)(9))\n";
  Printf.printf "────────────────────────────────────────────────────────────────\n";
  let x = Ident.mk "x" in
  (* Build the Fun term: (λx:Int. x + 1)(9) *)
  let body = Fun.Add (Fun.Var x, Fun.Lit 1) in
  let lam = Fun.Lam (x, Fun.Int, body) in
  let term = Fun.App (lam, Fun.Lit 9) in
  Printf.printf "Fun Term: %s\n" (Fun.show_term term);
  
  (* Encode to Source *)
  let encoded = Encode.encode_term Ident.emptytbl term in
  Printf.printf "Source Term:\n  %s\n" (Source.show_term encoded);
  
  (* Cut with return continuation (Int type) *)
  let ret = Ident.fresh () in
  let cmd = Source.CutInt (encoded, Source.MuInt (ret, Source.RetInt ret)) in
  Printf.printf "Source Command:\n  %s\n" (Source.show_command cmd);
  
  (* Collapse *)
  let collapsed = Collapse.from_source cmd in
  Printf.printf "Collapsed:\n  %s\n" (Collapsed.show_command collapsed);
  
  (* Execute with Machine *)
  let (final_cfg, steps) = Machine.eval ~trace:true collapsed in
  Printf.printf "\nMachine finished in %d steps\n" steps;
  
  match Machine.get_result final_cfg with
  | Some (Machine.IntVal n) ->
      Printf.printf "Result: %d\n" n;
      if n = 10 then Printf.printf "PASS ✓\n"
      else Printf.printf "FAIL: expected 10, got %d\n" n
  | Some v ->
      Printf.printf "FAIL: expected IntVal 10, got %s\n" (Machine.pp_value v)
  | None ->
      Printf.printf "FAIL: no result (stuck or wrong terminal command)\n"

(* ========================================================================= *)
(* Main                                                                      *)
(* ========================================================================= *)

let () =
  Printf.printf "\n";
  Printf.printf "╔══════════════════════════════════════════════════════════════╗\n";
  Printf.printf "║         Fun → Source → Target → Collapsed Pipeline          ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════════════╝\n";
  Printf.printf "\n";
  test_unit ();
  test_identity ();
  test_const ();
  test_app ();
  test_bool_true ();
  test_case ();
  test_higher_order ();
  test_nested_app ();
  test_pair ();
  test_case_binding ();
  test_cocase ();
  test_dtor ();
  test_lit ();
  test_add ();
  test_nested_add ();
  test_int_identity ();
  test_machine_add_one ();
  Printf.printf "\n"
