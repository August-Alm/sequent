(** Test file for lib/common/types.ml functionality *)

open Common.Identifiers
open Common.Types

(* ========================================================================= *)
(* Test 1: Normalize a recursive signature (List) *)
(* ========================================================================= *)

let test_list_signature () =
  Printf.printf "=== Test 1: Recursive List Signature ===\n";
  
  (* Create identifiers *)
  let a_id = Ident.mk "a" in
  let list_id = Ident.mk "list" in
  let cons_id = Ident.mk "cons" in
  let nil_id = Ident.mk "nil" in
  
  let list_path = Path.of_ident list_id in
  let cons_path = Path.of_ident cons_id in
  let nil_path = Path.of_ident nil_id in
  
  (* Build the list signature in GADT style:
     type _ list = Nil : 'a list | Cons : 'a * 'a list -> 'a list
     Each xtor universally quantifies its own 'a. *)
  let cons_a = Ident.mk "a" in  (* Cons's own 'a *)
  let nil_a = Ident.mk "a" in   (* Nil's own 'a *)
  
  let rec list_sgn_lazy = lazy {
    name = list_path;
    parameters = [(a_id, Star)];  (* Arity: list takes one type arg *)
    xtors = [
      (* Cons : 'a * 'a list -> 'a list *)
      { name = cons_path
      ; parameters = [(cons_a, Star)]  (* Cons binds its own 'a *)
      ; existentials = []
      ; arguments = [Lhs (Rigid cons_a); Lhs (App (Sym (list_path, list_sgn_lazy), [Rigid cons_a]))]
      ; main = App (Sym (list_path, list_sgn_lazy), [Rigid cons_a])
      };
      (* Nil : 'a list *)
      { name = nil_path
      ; parameters = [(nil_a, Star)]  (* Nil binds its own 'a *)
      ; existentials = []
      ; arguments = []
      ; main = App (Sym (list_path, list_sgn_lazy), [Rigid nil_a])
      }
    ]
  } in
  
  (* Kind context: a has kind Star *)
  let kctx = Ident.add a_id Star Ident.emptytbl in
  
  (* Normalize: App(list_sgn, Int) *)
  let list_int = App (Sym (list_path, list_sgn_lazy), [Ext Int]) in
  let normalized = whnf kctx [] list_int in
  
  (match normalized with
  | Sgn sg ->
      Printf.printf "Normalized list(int) to signature with %d xtors\n" (List.length sg.xtors);
      List.iter (fun x -> Printf.printf "  - %s\n" (Path.name x.name)) sg.xtors;
      Printf.printf "Test 1 PASSED\n"
  | _ -> 
      Printf.printf "Test 1 FAILED: expected Sgn, got something else\n");
  Printf.printf "\n"

(* ========================================================================= *)
(* Test 2: GADT filtering - expr signature *)
(* ========================================================================= *)

let test_gadt_filtering () =
  Printf.printf "=== Test 2: GADT Filtering (expr) ===\n";
  
  (* 
     type _ expr =
       | Lit : int -> int expr
       | Var : string -> 'a expr
  *)
  
  let t_id = Ident.mk "t" in
  let expr_id = Ident.mk "expr" in
  let lit_id = Ident.mk "lit" in
  let var_id = Ident.mk "var" in
  let string_id = Ident.mk "string" in  (* We'll fake a string type *)
  
  let expr_path = Path.of_ident expr_id in
  let lit_path = Path.of_ident lit_id in
  let var_path = Path.of_ident var_id in
  let string_path = Path.of_ident string_id in
  
  (* Fake string signature (empty, just for testing) *)
  let string_sgn_lazy = lazy {
    name = string_path;
    parameters = [];
    xtors = []
  } in
  
  (* GADT style:
     type _ expr = Lit : int -> int expr | Var : string -> 'a expr *)
  let var_a = Ident.mk "a" in  (* Var's own 'a *)
  
  let rec expr_sgn_lazy = lazy {
    name = expr_path;
    parameters = [(t_id, Star)];  (* Arity: expr takes one type arg *)
    xtors = [
      (* Lit : int -> int expr  (no type params, concrete return) *)
      { name = lit_path
      ; parameters = []  (* Lit has no type params *)
      ; existentials = []
      ; arguments = [Lhs (Ext Int)]
      ; main = App (Sym (expr_path, expr_sgn_lazy), [Ext Int])
      };
      (* Var : string -> 'a expr  (universally quantifies 'a) *)
      { name = var_path
      ; parameters = [(var_a, Star)]  (* Var binds its own 'a *)
      ; existentials = []
      ; arguments = [Lhs (Sgn (Lazy.force string_sgn_lazy))]
      ; main = App (Sym (expr_path, expr_sgn_lazy), [Rigid var_a])
      }
    ]
  } in
  
  (* Kind context: t has kind Star *)
  let kctx = Ident.add t_id Star Ident.emptytbl in
  
  (* Test 2a: expr[int] should have both Lit and Var *)
  let expr_int = App (Sym (expr_path, expr_sgn_lazy), [Ext Int]) in
  let normalized_int = whnf kctx [] expr_int in
  
  (match normalized_int with
  | Sgn sg ->
      Printf.printf "expr(int) has %d xtors: " (List.length sg.xtors);
      List.iter (fun x -> Printf.printf "%s " (Path.name x.name)) sg.xtors;
      Printf.printf "\n";
      if List.length sg.xtors = 2 then
        Printf.printf "  expr(int) PASSED: has both constructors\n"
      else
        Printf.printf "  expr(int) FAILED: expected 2 xtors\n"
  | _ -> Printf.printf "  expr(int) FAILED: not a Sgn\n");
  
  (* Test 2b: expr[string] should only have Var (Lit returns int expr, not string expr) *)
  let expr_string = App (Sym (expr_path, expr_sgn_lazy), [Sgn (Lazy.force string_sgn_lazy)]) in
  let normalized_string = whnf kctx [] expr_string in
  
  (match normalized_string with
  | Sgn sg ->
      Printf.printf "expr(string) has %d xtors: " (List.length sg.xtors);
      List.iter (fun x -> Printf.printf "%s " (Path.name x.name)) sg.xtors;
      Printf.printf "\n";
      if List.length sg.xtors = 1 then
        Printf.printf "  expr(string) PASSED: Lit filtered out\n"
      else
        Printf.printf "  expr(string) FAILED: expected 1 xtor (Var only)\n"
  | _ -> Printf.printf "  expr(string) FAILED: not a Sgn\n");
  
  Printf.printf "\n"


(* ========================================================================= *)
(* Test 4: Validate existentials don't escape (via kind checking) *)
(* ========================================================================= *)

let test_existential_escape () =
  Printf.printf "=== Test 4: Existential Escape Validation ===\n";
  
  (* Good: existential doesn't appear in main *)
  let pack_id = Ident.mk "pack" in
  let pack_path = Path.of_ident pack_id in
  let ex_id = Ident.mk "ex" in
  
  let good_sgn = Sgn {
    name = pack_path;
    parameters = [];
    xtors = [{
      name = pack_path;
      parameters = [];
      existentials = [(ex_id, Star)];
      arguments = [Lhs (Rigid ex_id)];  (* ex appears in args (OK) *)
      main = Ext Int  (* ex does NOT appear in main (OK) *)
    }]
  } in
  
  let kctx = Ident.emptytbl in
  (match infer_kind kctx good_sgn with
  | Ok Star -> Printf.printf "  Good sgn (ex in args only): PASSED\n"
  | Ok _ -> Printf.printf "  Good sgn: FAILED - wrong kind\n"
  | Error _ -> Printf.printf "  Good sgn: FAILED - unexpected error\n");
  
  (* Bad: existential escapes into main *)
  let bad_sgn = Sgn {
    name = pack_path;
    parameters = [];
    xtors = [{
      name = pack_path;
      parameters = [];
      existentials = [(ex_id, Star)];
      arguments = [Lhs (Rigid ex_id)];
      main = Rigid ex_id  (* ex DOES appear in main (BAD!) *)
    }]
  } in
  
  (match infer_kind kctx bad_sgn with
  | Ok _ -> Printf.printf "  Bad sgn (ex in main): FAILED - should have been rejected\n"
  | Error (ExistentialEscape _) -> Printf.printf "  Bad sgn (ex escapes): PASSED - correctly rejected\n"
  | Error _ -> Printf.printf "  Bad sgn: FAILED - wrong error type\n");
  
  Printf.printf "\n"

(* ========================================================================= *)
(* Main *)
(* ========================================================================= *)

let () =
  Printf.printf "Testing Common.Types\n\n";
  test_list_signature ();
  test_gadt_filtering ();
  test_existential_escape ();
  Printf.printf "All tests completed.\n"
