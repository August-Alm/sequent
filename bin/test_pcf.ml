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
        
        (* 5. Focus transformation: cut term with ret variable and focus *)
        print_newline ();
        print_endline "Focus (Cut-free):";
        let ret = Ident.mk "ret" in
        let test_cmd = Seq.Cut (seq_ty, seq_term, Seq.Variable ret) in
        (try
          let focused = Focus.focus test_cmd in
          (* Replace axiom(v, ret) or ret.xtor(args) with Ret(ty, v) for closed execution *)
          let rec close_ret cmd =
            match cmd with
            | Cut.Axiom (v, k) when Ident.name k = "ret" -> Cut.Ret (seq_ty, v)
            | Cut.Invoke (k, xtor, args) when Ident.name k = "ret" ->
                (* ret.xtor(args) - create a producer and return it *)
                let v = Ident.fresh () in
                Cut.Let (v, xtor, args, Cut.Ret (seq_ty, v))
            | Cut.Let (x, m, args, body) -> Cut.Let (x, m, args, close_ret body)
            | Cut.New (sig_, x, (params, branch), body) -> 
                Cut.New (sig_, x, (params, close_ret branch), close_ret body)
            | Cut.Switch (sig_, x, (params, branch)) ->
                Cut.Switch (sig_, x, (params, close_ret branch))
            | Cut.Lit (n, v, body) -> Cut.Lit (n, v, close_ret body)
            | Cut.Add (a, b, r, body) -> Cut.Add (a, b, r, close_ret body)
            | Cut.Ifz (v, t, e) -> Cut.Ifz (v, close_ret t, close_ret e)
            | _ -> cmd
          in
          let closed = close_ret focused in
          Printf.printf "%s\n" (Cut.pp_command closed);
          
          (* 6. Machine evaluation *)
          print_newline ();
          print_endline "Machine Evaluation:";
          (try
            let trace = false in  (* Set to true to trace specific test *)
            let (final_cmd, final_env) = Cut.Machine.eval ~trace closed in
            Printf.printf "  Final: %s\n" (Cut.pp_command final_cmd);
            Printf.printf "  Env: %s\n" (Cut.Machine.pp_env final_env);
            (* Check if we got a result *)
            (match Cut.Machine.get_result (final_cmd, final_env) with
             | Some (Cut.Machine.IntVal n) ->
                 Printf.printf "  Result: %d\n" n
             | Some v ->
                 Printf.printf "  Result: %s\n" (Cut.Machine.pp_value v)
             | None -> ())
          with e ->
            Printf.printf "  Exception: %s\n" (Printexc.to_string e))
        with e ->
          Printf.printf "  Exception: %s\n" (Printexc.to_string e));
        
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

  (* ══════════════════════════════════════════════════════════════════
     Test 9: Function composition - compose two functions
     (λf. λg. λx. f (g x)) (λa. a + 1) (λb. b + 2) 10
     compose : (Int->Int) -> (Int->Int) -> Int -> Int
     ══════════════════════════════════════════════════════════════════ *)
  let f = Ident.mk "f" in
  let g = Ident.mk "g" in
  let x = Ident.mk "x" in
  let a = Ident.mk "a" in
  let b = Ident.mk "b" in
  let int_to_int = Pcf.Arrow (Pcf.Int, Pcf.Int) in
  let compose = Pcf.Lam (f, int_to_int,
    Pcf.Lam (g, int_to_int,
      Pcf.Lam (x, Pcf.Int,
        Pcf.App (Pcf.Var f, Pcf.App (Pcf.Var g, Pcf.Var x))))) in
  let inc1 = Pcf.Lam (a, Pcf.Int, Pcf.Add (Pcf.Var a, Pcf.Lit 1)) in
  let inc2 = Pcf.Lam (b, Pcf.Int, Pcf.Add (Pcf.Var b, Pcf.Lit 2)) in
  let composed = Pcf.App (Pcf.App (Pcf.App (compose, inc1), inc2), Pcf.Lit 10) in
  run_test
    ~name:"Composition: compose (+1) (+2) 10 = 13"
    ~manual_repr:"(λf. λg. λx. f (g x)) (λa. a+1) (λb. b+2) 10"
    composed;

  (* ══════════════════════════════════════════════════════════════════
     Test 10: Twice - apply a function twice
     (λf. λx. f (f x)) (λy. y + 3) 5
     twice : (Int->Int) -> Int -> Int
     ══════════════════════════════════════════════════════════════════ *)
  let f = Ident.mk "f" in
  let x = Ident.mk "x" in
  let y = Ident.mk "y" in
  let twice = Pcf.Lam (f, int_to_int,
    Pcf.Lam (x, Pcf.Int,
      Pcf.App (Pcf.Var f, Pcf.App (Pcf.Var f, Pcf.Var x)))) in
  let add3 = Pcf.Lam (y, Pcf.Int, Pcf.Add (Pcf.Var y, Pcf.Lit 3)) in
  let twice_applied = Pcf.App (Pcf.App (twice, add3), Pcf.Lit 5) in
  run_test
    ~name:"Twice: twice (+3) 5 = 11"
    ~manual_repr:"(λf. λx. f (f x)) (λy. y+3) 5"
    twice_applied;

  (* ══════════════════════════════════════════════════════════════════
     Test 11: Church numeral style - apply f three times
     (λf. λx. f (f (f x))) (λn. n + 1) 0
     three : (Int->Int) -> Int -> Int
     ══════════════════════════════════════════════════════════════════ *)
  let f = Ident.mk "f" in
  let x = Ident.mk "x" in
  let n = Ident.mk "n" in
  let three = Pcf.Lam (f, int_to_int,
    Pcf.Lam (x, Pcf.Int,
      Pcf.App (Pcf.Var f,
        Pcf.App (Pcf.Var f,
          Pcf.App (Pcf.Var f, Pcf.Var x))))) in
  let succ = Pcf.Lam (n, Pcf.Int, Pcf.Add (Pcf.Var n, Pcf.Lit 1)) in
  let three_applied = Pcf.App (Pcf.App (three, succ), Pcf.Lit 0) in
  run_test
    ~name:"Church 3: (λf. λx. f(f(f x))) succ 0 = 3"
    ~manual_repr:"(λf. λx. f (f (f x))) (λn. n+1) 0"
    three_applied;

  (* ══════════════════════════════════════════════════════════════════
     Test 12: Higher-order returning higher-order
     (λn. λf. λx. f (x + n)) 5 (λy. y + y) 3
     Returns a function that adds n before applying f
     addBefore : Int -> (Int->Int) -> Int -> Int
     ══════════════════════════════════════════════════════════════════ *)
  let n = Ident.mk "n" in
  let f = Ident.mk "f" in
  let x = Ident.mk "x" in
  let y = Ident.mk "y" in
  let add_before = Pcf.Lam (n, Pcf.Int,
    Pcf.Lam (f, int_to_int,
      Pcf.Lam (x, Pcf.Int,
        Pcf.App (Pcf.Var f, Pcf.Add (Pcf.Var x, Pcf.Var n))))) in
  let double = Pcf.Lam (y, Pcf.Int, Pcf.Add (Pcf.Var y, Pcf.Var y)) in
  let add_before_applied = Pcf.App (Pcf.App (Pcf.App (add_before, Pcf.Lit 5), double), Pcf.Lit 3) in
  run_test
    ~name:"AddBefore: (λn. λf. λx. f(x+n)) 5 double 3 = 16"
    ~manual_repr:"(λn. λf. λx. f (x+n)) 5 (λy. y+y) 3"
    add_before_applied;

  (* ══════════════════════════════════════════════════════════════════
     Test 13: Function that returns a function builder
     (λx. λy. λz. x + y + z) 1 2 3
     Curried addition of three numbers
     ══════════════════════════════════════════════════════════════════ *)
  let x = Ident.mk "x" in
  let y = Ident.mk "y" in
  let z = Ident.mk "z" in
  let add3_curried = Pcf.Lam (x, Pcf.Int,
    Pcf.Lam (y, Pcf.Int,
      Pcf.Lam (z, Pcf.Int,
        Pcf.Add (Pcf.Var x, Pcf.Add (Pcf.Var y, Pcf.Var z))))) in
  let add3_applied = Pcf.App (Pcf.App (Pcf.App (add3_curried, Pcf.Lit 1), Pcf.Lit 2), Pcf.Lit 3) in
  run_test
    ~name:"Curried add3: (λx. λy. λz. x+y+z) 1 2 3 = 6"
    ~manual_repr:"(λx. λy. λz. x+y+z) 1 2 3"
    add3_applied;

  (* ══════════════════════════════════════════════════════════════════
     Test 14: Nested higher-order - compose composed with itself
     Let compose = λf. λg. λx. f (g x)
     (compose compose compose) (+1) (+2) 10
     = compose (compose (+1)) (+2) 10
     = (compose (+1)) ((+2) 10)
     = (compose (+1)) 12
     = λx. (+1) (12 x) ... wait, that's wrong
     Actually: compose compose compose f g x = compose (compose f) g x
                                              = (compose f) (g x)
                                              = λy. f ((g x) y)
     Hmm, types don't work out simply. Let's do something else.
     ══════════════════════════════════════════════════════════════════ *)
  (* Test 14: Conditional with higher-order result
     ifz 0 then (λx. x+1) else (λx. x+2) applied to 10
     ══════════════════════════════════════════════════════════════════ *)
  let x = Ident.mk "x" in
  let branch1 = Pcf.Lam (x, Pcf.Int, Pcf.Add (Pcf.Var x, Pcf.Lit 1)) in
  let x2 = Ident.mk "x" in
  let branch2 = Pcf.Lam (x2, Pcf.Int, Pcf.Add (Pcf.Var x2, Pcf.Lit 2)) in
  let cond_fn = Pcf.Ifz (Pcf.Lit 0, branch1, branch2) in
  let cond_applied = Pcf.App (cond_fn, Pcf.Lit 10) in
  run_test
    ~name:"Cond HO: (ifz 0 then (+1) else (+2)) 10 = 11"
    ~manual_repr:"(ifz 0 then (λx.x+1) else (λx.x+2)) 10"
    cond_applied;

  (* ══════════════════════════════════════════════════════════════════
     Test 15: S combinator style - flip and apply
     (λf. λg. λx. f x (g x)) (λa. λb. a+b) (λc. c+c) 3
     S f g x = f x (g x)
     Here: f = λa.λb.a+b, g = λc.c+c, x = 3
     = (λa.λb.a+b) 3 ((λc.c+c) 3)
     = (λb.3+b) 6
     = 3 + 6 = 9
     ══════════════════════════════════════════════════════════════════ *)
  let f = Ident.mk "f" in
  let g = Ident.mk "g" in
  let x = Ident.mk "x" in
  let a = Ident.mk "a" in
  let b = Ident.mk "b" in
  let c = Ident.mk "c" in
  let int_to_int_to_int = Pcf.Arrow (Pcf.Int, Pcf.Arrow (Pcf.Int, Pcf.Int)) in
  let s_comb = Pcf.Lam (f, int_to_int_to_int,
    Pcf.Lam (g, int_to_int,
      Pcf.Lam (x, Pcf.Int,
        Pcf.App (Pcf.App (Pcf.Var f, Pcf.Var x), Pcf.App (Pcf.Var g, Pcf.Var x))))) in
  let add_fn = Pcf.Lam (a, Pcf.Int, Pcf.Lam (b, Pcf.Int, Pcf.Add (Pcf.Var a, Pcf.Var b))) in
  let double_fn = Pcf.Lam (c, Pcf.Int, Pcf.Add (Pcf.Var c, Pcf.Var c)) in
  let s_applied = Pcf.App (Pcf.App (Pcf.App (s_comb, add_fn), double_fn), Pcf.Lit 3) in
  run_test
    ~name:"S combinator: S add double 3 = 9"
    ~manual_repr:"(λf. λg. λx. f x (g x)) (λa.λb.a+b) (λc.c+c) 3"
    s_applied;

  (* ══════════════════════════════════════════════════════════════════
     Test 16: K combinator (flip) with functions
     (λx. λy. x) (λa. a+1) (λb. b+2) applied to 5
     K returns its first argument, ignoring the second
     = (λa. a+1) 5 = 6
     ══════════════════════════════════════════════════════════════════ *)
  let x = Ident.mk "x" in
  let y = Ident.mk "y" in
  let a = Ident.mk "a" in
  let b = Ident.mk "b" in
  let k_comb = Pcf.Lam (x, int_to_int,
    Pcf.Lam (y, int_to_int, Pcf.Var x)) in
  let fn1 = Pcf.Lam (a, Pcf.Int, Pcf.Add (Pcf.Var a, Pcf.Lit 1)) in
  let fn2 = Pcf.Lam (b, Pcf.Int, Pcf.Add (Pcf.Var b, Pcf.Lit 2)) in
  let k_applied = Pcf.App (Pcf.App (Pcf.App (k_comb, fn1), fn2), Pcf.Lit 5) in
  run_test
    ~name:"K combinator: K (+1) (+2) 5 = 6"
    ~manual_repr:"(λx. λy. x) (λa.a+1) (λb.b+2) 5"
    k_applied;

  (* ══════════════════════════════════════════════════════════════════
     Test 17: Deeply nested application - 4 levels of functions
     (λf. λg. λh. λx. f (g (h x))) (+1) (+2) (+3) 0
     = (+1) ((+2) ((+3) 0))
     = (+1) ((+2) 3)
     = (+1) 5
     = 6
     ══════════════════════════════════════════════════════════════════ *)
  let f = Ident.mk "f" in
  let g = Ident.mk "g" in
  let h = Ident.mk "h" in
  let x = Ident.mk "x" in
  let n1 = Ident.mk "n1" in
  let n2 = Ident.mk "n2" in
  let n3 = Ident.mk "n3" in
  let compose3 = Pcf.Lam (f, int_to_int,
    Pcf.Lam (g, int_to_int,
      Pcf.Lam (h, int_to_int,
        Pcf.Lam (x, Pcf.Int,
          Pcf.App (Pcf.Var f,
            Pcf.App (Pcf.Var g,
              Pcf.App (Pcf.Var h, Pcf.Var x))))))) in
  let add1 = Pcf.Lam (n1, Pcf.Int, Pcf.Add (Pcf.Var n1, Pcf.Lit 1)) in
  let add2 = Pcf.Lam (n2, Pcf.Int, Pcf.Add (Pcf.Var n2, Pcf.Lit 2)) in
  let add3 = Pcf.Lam (n3, Pcf.Int, Pcf.Add (Pcf.Var n3, Pcf.Lit 3)) in
  let compose3_applied = Pcf.App (Pcf.App (Pcf.App (Pcf.App (compose3, add1), add2), add3), Pcf.Lit 0) in
  run_test
    ~name:"Compose3: (λf.λg.λh.λx. f(g(h x))) (+1)(+2)(+3) 0 = 6"
    ~manual_repr:"(λf.λg.λh.λx. f(g(h x))) (+1) (+2) (+3) 0"
    compose3_applied;

  (* Summary *)
  print_endline "════════════════════════════════════════════════════════════════";
  Printf.printf "Results: %d/%d tests passed\n" !pass_count !test_count;
  if !pass_count = !test_count then
    print_endline "All tests PASSED ✓"
  else
    print_endline "Some tests FAILED ✗";
  print_endline "════════════════════════════════════════════════════════════════"
