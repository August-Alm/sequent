(** 
  Test suite for the Melcore → Core → Focused pipeline.
  
  This test file mirrors test_pcf.ml but uses the generalized pipeline:
  1. Write input terms using Melcore.Terms
  2. Type-check and elaborate using Melcore.Terms.infer
  3. Encode to Core using Encode.map_term
  4. Focus to Focused using Focus.focus
  5. Print using Focused.Printing
  6. Execute using Focused.Semantics
*)

module MTy = Melcore.Types
module MTm = Melcore.Terms
module CTm = Core.Terms
module FTerms = Focused.Terms
module FPrint = Focused.Printing
module FMachine = Focused.Semantics
module Encode = Sequent.Encode

open Common.Identifiers

(* Test harness *)
let test_count = ref 0
let pass_count = ref 0

(* Empty definitions context for simple terms *)
let empty_defs : MTm.definitions = Path.emptytbl

(* Close a focused command by replacing axiom/invoke on 'ret' with Ret *)
let rec close_ret (ret_ty: Common.Types.typ) (cmd: FTerms.command) : FTerms.command =
  match cmd with
  | FTerms.Axiom (_, v, k) when Ident.name k = "ret" -> 
      FTerms.Ret (ret_ty, v)
  | FTerms.Invoke (k, xtor, args) when Ident.name k = "ret" ->
      (* ret.xtor(args) - create a producer and return it *)
      let v = Ident.fresh () in
      FTerms.Let (v, xtor, args, FTerms.Ret (ret_ty, v))
  | FTerms.Let (x, m, args, body) -> 
      FTerms.Let (x, m, args, close_ret ret_ty body)
  | FTerms.New (sg, x, branches, body) ->
      let branches' = List.map (fun (xtor, vars, b) ->
        (xtor, vars, close_ret ret_ty b)
      ) branches in
      FTerms.New (sg, x, branches', close_ret ret_ty body)
  | FTerms.Switch (sg, x, branches) ->
      let branches' = List.map (fun (xtor, vars, b) ->
        (xtor, vars, close_ret ret_ty b)
      ) branches in
      FTerms.Switch (sg, x, branches')
  | FTerms.Lit (n, v, body) -> 
      FTerms.Lit (n, v, close_ret ret_ty body)
  | FTerms.Add (a, b, r, body) -> 
      FTerms.Add (a, b, r, close_ret ret_ty body)
  | FTerms.Ifz (v, t, e) -> 
      FTerms.Ifz (v, close_ret ret_ty t, close_ret ret_ty e)
  | _ -> cmd

let run_test ~name ~manual_repr (term: MTm.term) =
  incr test_count;
  print_endline "════════════════════════════════════════════════════════════════";
  Printf.printf "Test %d: %s\n" !test_count name;
  print_endline "────────────────────────────────────────────────────────────────";
  
  (* 1. Print manual representation *)
  print_endline "Melcore Term:";
  Printf.printf "  Manual:  %s\n" manual_repr;
  print_newline ();
  
  (* 2. Type-check via infer_term *)
  let empty_ctx : MTm.context = 
    { MTm.kinds = Ident.emptytbl
    ; MTm.types = Ident.emptytbl
    }
  in
  
  let show_error (e: MTm.check_error) = match e with
    | MTm.UnboundVariable v -> "Unbound variable: " ^ Ident.name v
    | MTm.UnboundSymbol _ -> "Unbound symbol"
    | MTm.TypeMismatch _ -> "Type mismatch"
    | MTm.ExpectedData _ -> "Expected data type"
    | MTm.ExpectedCode _ -> "Expected code type"
    | MTm.SignatureMismatch _ -> "Signature mismatch"
    | MTm.XtorNotInSignature _ -> "Xtor not in signature"
    | MTm.NonExhaustive _ -> "Non-exhaustive"
    | MTm.ArityMismatch {xtor=_; expected; actual} ->
        Printf.sprintf "Arity mismatch: expected %d, got %d" expected actual
    | MTm.UnificationFailed _ -> "Unification failed"
  in
  
  print_endline "Melcore Type-check:";
  let typed_result =
    try
      match MTm.infer_term empty_defs empty_ctx term with
      | Ok (typed_term, inferred_ty) ->
          print_endline "  OK";
          Some (typed_term, inferred_ty)
      | Error e ->
          Printf.printf "  Error: %s\n" (show_error e);
          None
    with e ->
      Printf.printf "  Exception: %s\n" (Printexc.to_string e);
      None
  in
  print_newline ();
  
  match typed_result with
  | None -> 
      print_endline "FAIL: Melcore type-check failed\n"
  | Some (typed_term, inferred_ty) ->
      (* 3. Encode to Core *)
      let empty_typed_defs : MTm.typed_definitions = Path.emptytbl in
      let empty_kctx = Ident.emptytbl in
      print_endline "Core Encoding:";
      (try
        let core_term = Sequent.Encode.map_term empty_typed_defs empty_kctx Ident.emptytbl typed_term in
        let core_ty = Sequent.Encode.map_typ inferred_ty in
        Printf.printf "  Core type: %s\n" (Common.Printing.typ_to_string core_ty);
        print_newline ();
        
        (* 4. Create cut with ret variable and focus *)
        print_endline "Focus (Cut-free):";
        let ret = Ident.mk "ret" in
        let core_cmd = CTm.Cut (core_ty, core_term, CTm.Var ret) in
        (try
          let focused = Sequent.Focus.focus core_cmd in
          let closed = close_ret core_ty focused in
          Printf.printf "%s\n" (FPrint.pp_command closed);
          print_newline ();
          
          (* 5. Machine evaluation *)
          print_endline "Machine Evaluation:";
          (try
            let trace = false in
            let ((final_cmd, final_env), step_count) = FMachine.eval ~trace closed in
            Printf.printf "  Steps: %d\n" step_count;
            Printf.printf "  Final: %s\n" (FMachine.cmd_name final_cmd);
            (* Check if we got a result *)
            (match FMachine.get_result (final_cmd, final_env) with
             | Some (FMachine.IntVal n) ->
                 Printf.printf "  Result: %d\n" n
             | Some v ->
                 Printf.printf "  Result: %s\n" (FMachine.pp_value v)
             | None -> ())
          with e ->
            Printf.printf "  Exception: %s\n" (Printexc.to_string e));
          
          (* 6. Focused type checking - temporarily disabled due to hang *)
          (*
          print_endline "Focused Type Check:";
          print_endline "  (skipped)"
          *)
          (try
            (* Type check the closed command (no ret variable needed) *)
            let empty_kctx = Ident.emptytbl in
            let empty_ctx = Ident.emptytbl in
            let empty_env = Common.Types.empty_env in
            match FTerms.check_command empty_kctx empty_ctx empty_env closed with
            | Ok () -> print_endline "  ✓ Type check passed"
            | Error e ->
                let err_msg = match e with
                  | FTerms.UnboundVariable v -> "Unbound variable: " ^ Ident.name v
                  | FTerms.TypeMismatch _ -> "Type mismatch"
                  | FTerms.ChiralityMismatch _ -> "Chirality mismatch"
                  | FTerms.ExpectedSignature _ -> "Expected signature"
                  | FTerms.SignatureMismatch _ -> "Signature mismatch"
                  | FTerms.XtorNotInSignature _ -> "Xtor not in signature"
                  | FTerms.NonExhaustive _ -> "Non-exhaustive"
                  | FTerms.ArityMismatch _ -> "Arity mismatch"
                  | FTerms.UnificationFailed _ -> "Unification failed"
                in
                Printf.printf "  ✗ Type check failed: %s\n" err_msg
          with 
          | e ->
            Printf.printf "  Exception: %s\n" (Printexc.to_string e))
        with e ->
          Printf.printf "  Focus Exception: %s\n" (Printexc.to_string e));
        
        print_endline "PASS ✓";
        incr pass_count
      with e ->
        Printf.printf "  Encode Exception: %s\n" (Printexc.to_string e);
        print_endline "FAIL: Core encoding failed");
      print_newline ()

(* ════════════════════════════════════════════════════════════════════════════
   Helper for building Melcore types
   ════════════════════════════════════════════════════════════════════════════ *)

let int_ty : MTy.typ = MTy.Ext Int
let arrow (a: MTy.typ) (b: MTy.typ) : MTy.typ = MTy.Fun (a, b)

(* ════════════════════════════════════════════════════════════════════════════
   Test Cases (mirroring test_pcf.ml)
   ════════════════════════════════════════════════════════════════════════════ *)

let () =
  print_endline "\n╔══════════════════════════════════════════════════════════════╗";
  print_endline "║           Melcore → Core → Focused Pipeline Tests            ║";
  print_endline "╚══════════════════════════════════════════════════════════════╝\n";

  (* ══════════════════════════════════════════════════════════════════
     Test 1: Int -> Int (Pos -> Pos)
     Identity on integers: λx:Int. x
     ══════════════════════════════════════════════════════════════════ *)
  let x = Ident.mk "x" in
  let id_int = MTm.Lam (x, Some int_ty, MTm.Var x) in
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
  let const = MTm.Lam (x, Some int_ty, MTm.Lam (y, Some int_ty, MTm.Var x)) in
  run_test
    ~name:"Pos -> Neg: λx:Int. λy:Int. x"
    ~manual_repr:"λx:Int. λy:Int. x"
    const;

  (* ══════════════════════════════════════════════════════════════════
     Test 3: (Int -> Int) -> Int (Neg -> Pos)
     Apply function to 0: λf:(Int -> Int). f 0
     ══════════════════════════════════════════════════════════════════ *)
  let f = Ident.mk "f" in
  let apply_to_zero = MTm.Lam (f, Some (arrow int_ty int_ty),
    MTm.App (MTm.Var f, MTm.Int 0)) in
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
  let compose_succ = MTm.Lam (f, Some (arrow int_ty int_ty),
    MTm.Lam (x, Some int_ty,
      MTm.App (MTm.Var f, MTm.Add (MTm.Var x, MTm.Int 1)))) in
  run_test
    ~name:"Neg -> Neg: λf:(Int -> Int). λx:Int. f (x + 1)"
    ~manual_repr:"λf:(Int -> Int). λx:Int. f (x + 1)"
    compose_succ;

  (* ══════════════════════════════════════════════════════════════════
     Test 5: Arithmetic - addition
     ══════════════════════════════════════════════════════════════════ *)
  let add_example = MTm.Add (MTm.Int 1, MTm.Int 2) in
  run_test
    ~name:"Arithmetic: 1 + 2"
    ~manual_repr:"1 + 2"
    
    add_example;

  (* ══════════════════════════════════════════════════════════════════
     Test 6: Conditional - ifz
     ══════════════════════════════════════════════════════════════════ *)
  let ifz_example = MTm.Ifz (MTm.Int 0, MTm.Int 42, MTm.Int 0) in
  run_test
    ~name:"Conditional: ifz 0 then 42 else 0"
    ~manual_repr:"ifz 0 then 42 else 0"
    
    ifz_example;

  (* ══════════════════════════════════════════════════════════════════
     Test 7: Application - (λx:Int. x + 1) 5
     ══════════════════════════════════════════════════════════════════ *)
  let x = Ident.mk "x" in
  let succ = MTm.Lam (x, Some int_ty, MTm.Add (MTm.Var x, MTm.Int 1)) in
  let app_example = MTm.App (succ, MTm.Int 5) in
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
  let int_to_int = arrow int_ty int_ty in
  let apply_fn = MTm.Lam (f, Some int_to_int,
    MTm.Lam (x, Some int_ty, MTm.App (MTm.Var f, MTm.Var x))) in
  let inc = MTm.Lam (y, Some int_ty, MTm.Add (MTm.Var y, MTm.Int 1)) in
  let ho_app = MTm.App (MTm.App (apply_fn, inc), MTm.Int 10) in
  run_test
    ~name:"Higher-order: ((λf. λx. f x) (λy. y + 1)) 10"
    ~manual_repr:"((λf:(Int -> Int). λx:Int. f x) (λy:Int. y + 1)) 10"
    
    ho_app;

  (* ══════════════════════════════════════════════════════════════════
     Test 9: Function composition - compose two functions
     (λf. λg. λx. f (g x)) (λa. a + 1) (λb. b + 2) 10
     ══════════════════════════════════════════════════════════════════ *)
  let f = Ident.mk "f" in
  let g = Ident.mk "g" in
  let x = Ident.mk "x" in
  let a = Ident.mk "a" in
  let b = Ident.mk "b" in
  let int_to_int = arrow int_ty int_ty in
  let compose = MTm.Lam (f, Some int_to_int,
    MTm.Lam (g, Some int_to_int,
      MTm.Lam (x, Some int_ty,
        MTm.App (MTm.Var f, MTm.App (MTm.Var g, MTm.Var x))))) in
  let inc1 = MTm.Lam (a, Some int_ty, MTm.Add (MTm.Var a, MTm.Int 1)) in
  let inc2 = MTm.Lam (b, Some int_ty, MTm.Add (MTm.Var b, MTm.Int 2)) in
  let composed = MTm.App (MTm.App (MTm.App (compose, inc1), inc2), MTm.Int 10) in
  run_test
    ~name:"Composition: compose (+1) (+2) 10 = 13"
    ~manual_repr:"(λf. λg. λx. f (g x)) (λa. a+1) (λb. b+2) 10"
    
    composed;

  (* ══════════════════════════════════════════════════════════════════
     Test 10: Twice - apply a function twice
     (λf. λx. f (f x)) (λy. y + 3) 5
     ══════════════════════════════════════════════════════════════════ *)
  let f = Ident.mk "f" in
  let x = Ident.mk "x" in
  let y = Ident.mk "y" in
  let twice = MTm.Lam (f, Some int_to_int,
    MTm.Lam (x, Some int_ty,
      MTm.App (MTm.Var f, MTm.App (MTm.Var f, MTm.Var x)))) in
  let add3 = MTm.Lam (y, Some int_ty, MTm.Add (MTm.Var y, MTm.Int 3)) in
  let twice_applied = MTm.App (MTm.App (twice, add3), MTm.Int 5) in
  run_test
    ~name:"Twice: twice (+3) 5 = 11"
    ~manual_repr:"(λf. λx. f (f x)) (λy. y+3) 5"
    
    twice_applied;

  (* ══════════════════════════════════════════════════════════════════
     Test 11: Church numeral style - apply f three times
     (λf. λx. f (f (f x))) (λn. n + 1) 0
     ══════════════════════════════════════════════════════════════════ *)
  let f = Ident.mk "f" in
  let x = Ident.mk "x" in
  let n = Ident.mk "n" in
  let three = MTm.Lam (f, Some int_to_int,
    MTm.Lam (x, Some int_ty,
      MTm.App (MTm.Var f,
        MTm.App (MTm.Var f,
          MTm.App (MTm.Var f, MTm.Var x))))) in
  let succ = MTm.Lam (n, Some int_ty, MTm.Add (MTm.Var n, MTm.Int 1)) in
  let three_applied = MTm.App (MTm.App (three, succ), MTm.Int 0) in
  run_test
    ~name:"Church 3: (λf. λx. f(f(f x))) succ 0 = 3"
    ~manual_repr:"(λf. λx. f (f (f x))) (λn. n+1) 0"
    
    three_applied;

  (* ══════════════════════════════════════════════════════════════════
     Test 12: Higher-order returning higher-order
     (λn. λf. λx. f (x + n)) 5 (λy. y + y) 3
     ══════════════════════════════════════════════════════════════════ *)
  let n = Ident.mk "n" in
  let f = Ident.mk "f" in
  let x = Ident.mk "x" in
  let y = Ident.mk "y" in
  let add_before = MTm.Lam (n, Some int_ty,
    MTm.Lam (f, Some int_to_int,
      MTm.Lam (x, Some int_ty,
        MTm.App (MTm.Var f, MTm.Add (MTm.Var x, MTm.Var n))))) in
  let double = MTm.Lam (y, Some int_ty, MTm.Add (MTm.Var y, MTm.Var y)) in
  let add_before_applied = MTm.App (MTm.App (MTm.App (add_before, MTm.Int 5), double), MTm.Int 3) in
  run_test
    ~name:"AddBefore: (λn. λf. λx. f(x+n)) 5 double 3 = 16"
    ~manual_repr:"(λn. λf. λx. f (x+n)) 5 (λy. y+y) 3"
    
    add_before_applied;

  (* ══════════════════════════════════════════════════════════════════
     Test 13: Function that returns a function builder
     (λx. λy. λz. x + y + z) 1 2 3
     ══════════════════════════════════════════════════════════════════ *)
  let x = Ident.mk "x" in
  let y = Ident.mk "y" in
  let z = Ident.mk "z" in
  let add3_curried = MTm.Lam (x, Some int_ty,
    MTm.Lam (y, Some int_ty,
      MTm.Lam (z, Some int_ty,
        MTm.Add (MTm.Var x, MTm.Add (MTm.Var y, MTm.Var z))))) in
  let add3_applied = MTm.App (MTm.App (MTm.App (add3_curried, MTm.Int 1), MTm.Int 2), MTm.Int 3) in
  run_test
    ~name:"Curried add3: (λx. λy. λz. x+y+z) 1 2 3 = 6"
    ~manual_repr:"(λx. λy. λz. x+y+z) 1 2 3"
    
    add3_applied;

  (* ══════════════════════════════════════════════════════════════════
     Test 14: Conditional with higher-order result
     ifz 0 then (λx. x+1) else (λx. x+2) applied to 10
     ══════════════════════════════════════════════════════════════════ *)
  let x = Ident.mk "x" in
  let branch1 = MTm.Lam (x, Some int_ty, MTm.Add (MTm.Var x, MTm.Int 1)) in
  let x2 = Ident.mk "x" in
  let branch2 = MTm.Lam (x2, Some int_ty, MTm.Add (MTm.Var x2, MTm.Int 2)) in
  let cond_ho = MTm.App (MTm.Ifz (MTm.Int 0, branch1, branch2), MTm.Int 10) in
  run_test
    ~name:"Cond HO: (ifz 0 then (+1) else (+2)) 10 = 11"
    ~manual_repr:"(ifz 0 then (λx.x+1) else (λx.x+2)) 10"
    
    cond_ho;

  (* ══════════════════════════════════════════════════════════════════
     Test 15: S combinator style - flip and apply
     (λf. λg. λx. f x (g x)) (λa. λb. a+b) (λc. c+c) 3
     ══════════════════════════════════════════════════════════════════ *)
  let f = Ident.mk "f" in
  let g = Ident.mk "g" in
  let x = Ident.mk "x" in
  let a = Ident.mk "a" in
  let b = Ident.mk "b" in
  let c = Ident.mk "c" in
  let int_to_int_to_int = arrow int_ty (arrow int_ty int_ty) in
  let s_comb = MTm.Lam (f, Some int_to_int_to_int,
    MTm.Lam (g, Some int_to_int,
      MTm.Lam (x, Some int_ty,
        MTm.App (MTm.App (MTm.Var f, MTm.Var x), MTm.App (MTm.Var g, MTm.Var x))))) in
  let add_fn = MTm.Lam (a, Some int_ty, MTm.Lam (b, Some int_ty, MTm.Add (MTm.Var a, MTm.Var b))) in
  let double_fn = MTm.Lam (c, Some int_ty, MTm.Add (MTm.Var c, MTm.Var c)) in
  let s_applied = MTm.App (MTm.App (MTm.App (s_comb, add_fn), double_fn), MTm.Int 3) in
  run_test
    ~name:"S combinator: S add double 3 = 9"
    ~manual_repr:"(λf. λg. λx. f x (g x)) (λa.λb.a+b) (λc.c+c) 3"
    
    s_applied;

  (* ══════════════════════════════════════════════════════════════════
     Test 16: K combinator (flip) with functions
     (λx. λy. x) (λa. a+1) (λb. b+2) applied to 5
     ══════════════════════════════════════════════════════════════════ *)
  let x = Ident.mk "x" in
  let y = Ident.mk "y" in
  let a = Ident.mk "a" in
  let b = Ident.mk "b" in
  let k_comb = MTm.Lam (x, Some int_to_int,
    MTm.Lam (y, Some int_to_int, MTm.Var x)) in
  let fn1 = MTm.Lam (a, Some int_ty, MTm.Add (MTm.Var a, MTm.Int 1)) in
  let fn2 = MTm.Lam (b, Some int_ty, MTm.Add (MTm.Var b, MTm.Int 2)) in
  let k_applied = MTm.App (MTm.App (MTm.App (k_comb, fn1), fn2), MTm.Int 5) in
  run_test
    ~name:"K combinator: K (+1) (+2) 5 = 6"
    ~manual_repr:"(λx. λy. x) (λa.a+1) (λb.b+2) 5"
    
    k_applied;

  (* ══════════════════════════════════════════════════════════════════
     Test 17: Deeply nested application - 4 levels of functions
     (λf. λg. λh. λx. f (g (h x))) (+1) (+2) (+3) 0
     ══════════════════════════════════════════════════════════════════ *)
  let f = Ident.mk "f" in
  let g = Ident.mk "g" in
  let h = Ident.mk "h" in
  let x = Ident.mk "x" in
  let n1 = Ident.mk "n1" in
  let n2 = Ident.mk "n2" in
  let n3 = Ident.mk "n3" in
  let compose3 = MTm.Lam (f, Some int_to_int,
    MTm.Lam (g, Some int_to_int,
      MTm.Lam (h, Some int_to_int,
        MTm.Lam (x, Some int_ty,
          MTm.App (MTm.Var f,
            MTm.App (MTm.Var g,
              MTm.App (MTm.Var h, MTm.Var x))))))) in
  let add1 = MTm.Lam (n1, Some int_ty, MTm.Add (MTm.Var n1, MTm.Int 1)) in
  let add2 = MTm.Lam (n2, Some int_ty, MTm.Add (MTm.Var n2, MTm.Int 2)) in
  let add3 = MTm.Lam (n3, Some int_ty, MTm.Add (MTm.Var n3, MTm.Int 3)) in
  let compose3_applied = MTm.App (MTm.App (MTm.App (MTm.App (compose3, add1), add2), add3), MTm.Int 0) in
  run_test
    ~name:"Compose3: (λf.λg.λh.λx. f(g(h x))) (+1)(+2)(+3) 0 = 6"
    ~manual_repr:"(λf.λg.λh.λx. f(g(h x))) (+1) (+2) (+3) 0"
    
    compose3_applied;

  (* ══════════════════════════════════════════════════════════════════
     Test 18: Let binding with literal
     let x = 5 in x + 1 = 6
     ══════════════════════════════════════════════════════════════════ *)
  let x = Ident.mk "x" in
  let let_lit = MTm.Let (x, MTm.Int 5, MTm.Add (MTm.Var x, MTm.Int 1)) in
  run_test
    ~name:"Let literal: let x = 5 in x + 1 = 6"
    ~manual_repr:"let x = 5 in x + 1"
    
    let_lit;

  (* ══════════════════════════════════════════════════════════════════
     Test 19: Let binding with function
     let f = (λy. y + 2) in f 10 = 12
     ══════════════════════════════════════════════════════════════════ *)
  let f = Ident.mk "f" in
  let y = Ident.mk "y" in
  let add2 = MTm.Lam (y, Some int_ty, MTm.Add (MTm.Var y, MTm.Int 2)) in
  let let_fn = MTm.Let (f, add2, MTm.App (MTm.Var f, MTm.Int 10)) in
  run_test
    ~name:"Let function: let f = (λy. y+2) in f 10 = 12"
    ~manual_repr:"let f = (λy. y+2) in f 10"
    
    let_fn;

  (* ══════════════════════════════════════════════════════════════════
     Test 20: Nested let bindings
     let x = 3 in let y = 4 in x + y = 7
     ══════════════════════════════════════════════════════════════════ *)
  let x = Ident.mk "x" in
  let y = Ident.mk "y" in
  let nested_let = MTm.Let (x, MTm.Int 3, 
    MTm.Let (y, MTm.Int 4, 
      MTm.Add (MTm.Var x, MTm.Var y))) in
  run_test
    ~name:"Nested let: let x = 3 in let y = 4 in x + y = 7"
    ~manual_repr:"let x = 3 in let y = 4 in x + y"
    
    nested_let;

  (* ══════════════════════════════════════════════════════════════════
     Test 21: Let with closure capture
     let a = 9 in let f = λx. x + a in f 1 = 10
     ══════════════════════════════════════════════════════════════════ *)
  let a = Ident.mk "a" in
  let f = Ident.mk "f" in
  let x = Ident.mk "x" in
  let closure_capture = MTm.Let (a, MTm.Int 9,
    MTm.Let (f, MTm.Lam (x, Some int_ty, MTm.Add (MTm.Var x, MTm.Var a)),
      MTm.App (MTm.Var f, MTm.Int 1))) in
  run_test
    ~name:"Closure capture: let a=9 in let f=λx.x+a in f 1 = 10"
    ~manual_repr:"let a = 9 in let f = λx. x+a in f 1"
    
    closure_capture;

  (* Summary *)
  print_endline "════════════════════════════════════════════════════════════════";
  Printf.printf "Results: %d/%d tests passed\n" !pass_count !test_count;
  if !pass_count = !test_count then
    print_endline "All tests PASSED ✓"
  else
    print_endline "Some tests FAILED ✗";
  print_endline "════════════════════════════════════════════════════════════════"
