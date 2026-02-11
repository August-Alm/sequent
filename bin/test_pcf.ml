open Sequent.Pcf
open Common.Identifiers

(* Test harness *)
let test_count = ref 0
let pass_count = ref 0

let run_test ~name ~manual_repr (term: Pcf.term) =
  incr test_count;
  print_endline "════════════════════════════════════════════════════════════════";
  Printf.printf "Test %d: %s\n" !test_count name;
  print_endline "────────────────────────────────────────────────────────────────";
  
  (* 1. Print manual and pretty-printed representation *)
  print_endline "PCF Term:";
  Printf.printf "  Manual:  %s\n" manual_repr;
  Printf.printf "  Pretty:  %s\n" (Pcf.pp_term term);
  print_newline ();
  
  (* 2. Type-check PCF term *)
  print_endline "PCF Type-check:";
  let pcf_ty =
    try
      let ty = Pcf.infer_typ Ident.emptytbl term in
      Printf.printf "  Type: %s\n" (Pcf.pp_typ ty);
      Some ty
    with e ->
      Printf.printf "  Exception: %s\n" (Printexc.to_string e);
      None
  in
  print_newline ();
  
  match pcf_ty with
  | None -> 
      print_endline "FAIL: PCF type-check failed\n"
  | Some pcf_ty ->
      (* 3. Encode type and term *)
      print_endline "Seq Encoding:";
      let seq_ty = Encode.map_typ pcf_ty in
      let seq_term = Encode.map_term Ident.emptytbl term in
      Printf.printf "  Type: %s\n" (Seq.pp_typ seq_ty);
      Printf.printf "  Term: %s\n" (Seq.pp_term seq_term);
      print_newline ();
      
      (* 4. Type-check Seq term *)
      print_endline "Seq Type-check:";
      (try
        let chiral_ty = Seq.infer_typ Ident.emptytbl seq_term in
        Printf.printf "  Chiral type: %s\n"
          (match chiral_ty with
           | Seq.Lhs ty -> "Lhs " ^ Seq.pp_typ ty
           | Seq.Rhs ty -> "Rhs " ^ Seq.pp_typ ty);
        print_endline "PASS ✓";
        incr pass_count
      with e ->
        Printf.printf "  Exception: %s\n" (Printexc.to_string e);
        print_endline "FAIL: Seq type-check failed");
      print_newline ()

let () =
  print_endline "\n╔══════════════════════════════════════════════════════════════╗";
  print_endline "║                    PCF Encoding Tests                        ║";
  print_endline "╚══════════════════════════════════════════════════════════════╝\n";

  (* ══════════════════════════════════════════════════════════════════
     Test 1: Int -> Int (Pos -> Pos)
     Identity on integers: λx:Int. x
     ══════════════════════════════════════════════════════════════════ *)
  let x = Ident.mk "x" in
  let id_int = Pcf.Lam (x, Pcf.Int, Pcf.Var x) in
  run_test 
    ~name:"Pos -> Pos: λx:Int. x"
    ~manual_repr:"λx:Int. x"
    id_int;

  (* ══════════════════════════════════════════════════════════════════
     Test 2: Int -> (Int -> Int) (Pos -> Neg)
     Constant function factory: λx:Int. λy:Int. x
     ══════════════════════════════════════════════════════════════════ *)
  let x = Ident.mk "x" in
  let y = Ident.mk "y" in
  let const = Pcf.Lam (x, Pcf.Int, Pcf.Lam (y, Pcf.Int, Pcf.Var x)) in
  run_test
    ~name:"Pos -> Neg: λx:Int. λy:Int. x"
    ~manual_repr:"λx:Int. λy:Int. x"
    const;

  (* ══════════════════════════════════════════════════════════════════
     Test 3: (Int -> Int) -> Int (Neg -> Pos)
     Apply function to 0: λf:(Int -> Int). f 0
     ══════════════════════════════════════════════════════════════════ *)
  let f = Ident.mk "f" in
  let apply_to_zero = Pcf.Lam (f, Pcf.Arrow (Pcf.Int, Pcf.Int),
    Pcf.App (Pcf.Var f, Pcf.Lit 0)) in
  run_test
    ~name:"Neg -> Pos: λf:(Int -> Int). f 0"
    ~manual_repr:"λf:(Int -> Int). f 0"
    apply_to_zero;

  (* ══════════════════════════════════════════════════════════════════
     Test 4: (Int -> Int) -> (Int -> Int) (Neg -> Neg)
     Compose with successor: λf:(Int -> Int). λx:Int. f (x + 1)
     ══════════════════════════════════════════════════════════════════ *)
  let f = Ident.mk "f" in
  let x = Ident.mk "x" in
  let compose_succ = Pcf.Lam (f, Pcf.Arrow (Pcf.Int, Pcf.Int),
    Pcf.Lam (x, Pcf.Int,
      Pcf.App (Pcf.Var f, Pcf.Add (Pcf.Var x, Pcf.Lit 1)))) in
  run_test
    ~name:"Neg -> Neg: λf:(Int -> Int). λx:Int. f (x + 1)"
    ~manual_repr:"λf:(Int -> Int). λx:Int. f (x + 1)"
    compose_succ;

  (* ══════════════════════════════════════════════════════════════════
     Test 5: Arithmetic - addition
     ══════════════════════════════════════════════════════════════════ *)
  let add_example = Pcf.Add (Pcf.Lit 1, Pcf.Lit 2) in
  run_test
    ~name:"Arithmetic: 1 + 2"
    ~manual_repr:"1 + 2"
    add_example;

  (* ══════════════════════════════════════════════════════════════════
     Test 6: Conditional - ifz
     ══════════════════════════════════════════════════════════════════ *)
  let ifz_example = Pcf.Ifz (Pcf.Lit 0, Pcf.Lit 42, Pcf.Lit 0) in
  run_test
    ~name:"Conditional: ifz 0 then 42 else 0"
    ~manual_repr:"ifz 0 then 42 else 0"
    ifz_example;

  (* ══════════════════════════════════════════════════════════════════
     Test 7: Application - (λx:Int. x + 1) 5
     ══════════════════════════════════════════════════════════════════ *)
  let x = Ident.mk "x" in
  let succ = Pcf.Lam (x, Pcf.Int, Pcf.Add (Pcf.Var x, Pcf.Lit 1)) in
  let app_example = Pcf.App (succ, Pcf.Lit 5) in
  run_test
    ~name:"Application: (λx:Int. x + 1) 5"
    ~manual_repr:"(λx:Int. x + 1) 5"
    app_example;

  (* ══════════════════════════════════════════════════════════════════
     Test 8: Higher-order application - apply function to argument
     ((λf:(Int -> Int). λx:Int. f x) (λy:Int. y + 1)) 10
     ══════════════════════════════════════════════════════════════════ *)
  let f = Ident.mk "f" in
  let x = Ident.mk "x" in
  let y = Ident.mk "y" in
  let apply_fn = Pcf.Lam (f, Pcf.Arrow (Pcf.Int, Pcf.Int),
    Pcf.Lam (x, Pcf.Int, Pcf.App (Pcf.Var f, Pcf.Var x))) in
  let inc = Pcf.Lam (y, Pcf.Int, Pcf.Add (Pcf.Var y, Pcf.Lit 1)) in
  let ho_app = Pcf.App (Pcf.App (apply_fn, inc), Pcf.Lit 10) in
  run_test
    ~name:"Higher-order: ((λf. λx. f x) (λy. y + 1)) 10"
    ~manual_repr:"((λf:(Int -> Int). λx:Int. f x) (λy:Int. y + 1)) 10"
    ho_app;

  (* Summary *)
  print_endline "════════════════════════════════════════════════════════════════";
  Printf.printf "Results: %d/%d tests passed\n" !pass_count !test_count;
  if !pass_count = !test_count then
    print_endline "All tests PASSED ✓"
  else
    print_endline "Some tests FAILED ✗";
  print_endline "════════════════════════════════════════════════════════════════"
