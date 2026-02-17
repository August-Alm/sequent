(** 
  Test suite for parsing → desugaring → melcore pipeline.
  
  This test file:
  1. Parses surface syntax strings using Lang.Parse
  2. Desugars to Melcore using Desugar
  3. Pretty-prints the result using Melcore.Printing
  4. Type-checks in Melcore using Melcore.Terms
*)

module Parse = Lang.Parse
module Syntax = Lang.Syntax
module MTy = Melcore.Types
module MTm = Melcore.Terms
module MPrint = Melcore.Printing

open Common.Identifiers

(* Test harness *)
let test_count = ref 0
let pass_count = ref 0

let run_test ~name (source: string) =
  incr test_count;
  print_endline "════════════════════════════════════════════════════════════════";
  Printf.printf "Test %d: %s\n" !test_count name;
  print_endline "────────────────────────────────────────────────────────────────";
  
  (* 1. Parse *)
  print_endline "Source:";
  Printf.printf "%s\n\n" source;
  
  print_endline "Parsing:";
  let parsed =
    try
      let defs = Parse.parse_defs_string source in
      print_endline "  OK";
      Some defs
    with e ->
      Printf.printf "  Parse error: %s\n" (Printexc.to_string e);
      None
  in
  print_newline ();
  
  match parsed with
  | None -> 
      print_endline "FAIL: Parse error\n"
  | Some ast_defs ->
      (* Print parsed AST *)
      print_endline "Parsed AST:";
      Printf.printf "%s\n\n" (Syntax.defs_to_string ast_defs);
      
      (* 2. Desugar *)
      print_endline "Desugaring:";
      let desugared =
        try
          let defs = Sequent.Desugar.desugar ast_defs in
          print_endline "  OK";
          Some defs
        with e ->
          Printf.printf "  Desugar error: %s\n" (Printexc.to_string e);
          None
      in
      print_newline ();
      
      match desugared with
      | None ->
          print_endline "FAIL: Desugar error\n"
      | Some result ->
          let melcore_defs = result.Sequent.Desugar.term_defs in
          (* 3. Pretty-print Melcore *)
          print_endline "Melcore (pretty-printed):";
          Path.to_list melcore_defs
          |> List.iter (fun (_, def) ->
              Printf.printf "%s\n\n" (MPrint.term_def_to_string def));
          
          (* 4. Type-check each definition *)
          print_endline "Type-checking:";
          let all_ok = ref true in
          
          let show_error (e: MTm.check_error) = match e with
            | MTm.UnboundVariable v -> "Unbound variable: " ^ Ident.name v
            | MTm.UnboundSymbol p -> "Unbound symbol: " ^ Path.name p
            | MTm.TypeMismatch {expected; actual} ->
                Printf.sprintf "Type mismatch: expected %s, got %s"
                  (MPrint.typ_to_string expected)
                  (MPrint.typ_to_string actual)
            | MTm.ExpectedData ty ->
                "Expected data type, got: " ^ MPrint.typ_to_string ty
            | MTm.ExpectedCode ty ->
                "Expected code type, got: " ^ MPrint.typ_to_string ty
            | MTm.SignatureMismatch _ -> "Signature mismatch"
            | MTm.XtorNotInSignature _ -> "Xtor not in signature"
            | MTm.NonExhaustive _ -> "Non-exhaustive"
            | MTm.ArityMismatch {xtor=_; expected; actual} ->
                Printf.sprintf "Arity mismatch: expected %d, got %d" expected actual
            | MTm.UnificationFailed (t1, t2) ->
                Printf.sprintf "Unification failed: %s ≠ %s"
                  (MPrint.typ_to_string t1)
                  (MPrint.typ_to_string t2)
          in
          
          Path.to_list melcore_defs
          |> List.iter (fun (_, (def: MTm.term_def)) ->
              Printf.printf "  Checking %s: %!" (Path.name def.name);
              
              try
                match MTm.check_definition melcore_defs def with
                | Ok _typed_def ->
                    print_endline "OK ✓"
                | Error e ->
                    Printf.printf "Error: %s\n" (show_error e);
                    all_ok := false
              with e ->
                Printf.printf "Exception: %s\n" (Printexc.to_string e);
                all_ok := false);
          
          print_newline ();
          if !all_ok then begin
            print_endline "PASS ✓";
            incr pass_count
          end else
            print_endline "FAIL: Type-check errors";
          print_newline ()

(* Run a single expression test (without definitions) *)
let run_expr_test ~name ~expected_type (source: string) =
  incr test_count;
  print_endline "════════════════════════════════════════════════════════════════";
  Printf.printf "Test %d: %s\n" !test_count name;
  print_endline "────────────────────────────────────────────────────────────────";
  
  (* 1. Parse expression *)
  print_endline "Source:";
  Printf.printf "  %s\n\n" source;
  
  print_endline "Parsing expression:";
  let parsed =
    try
      let expr = Parse.parse_expr_string source in
      print_endline "  OK";
      Some expr
    with e ->
      Printf.printf "  Parse error: %s\n" (Printexc.to_string e);
      None
  in
  print_newline ();
  
  match parsed with
  | None -> 
      print_endline "FAIL: Parse error\n"
  | Some ast_expr ->
      (* Print parsed AST *)
      print_endline "Parsed:";
      Printf.printf "  %s\n\n" (Syntax.ast_to_string 0 ast_expr);
      
      (* 2. Desugar with empty type defs *)
      print_endline "Desugaring:";
      let empty_ast_defs = { Syntax.type_defs = []; term_defs = [] } in
      let desugared =
        try
          let term = Sequent.Desugar.desugar_term empty_ast_defs ast_expr in
          print_endline "  OK";
          Some term
        with e ->
          Printf.printf "  Desugar error: %s\n" (Printexc.to_string e);
          None
      in
      print_newline ();
      
      match desugared with
      | None ->
          print_endline "FAIL: Desugar error\n"
      | Some melcore_term ->
          (* 3. Pretty-print *)
          print_endline "Melcore:";
          Printf.printf "  %s\n\n" (MPrint.term_to_string melcore_term);
          
          (* 4. Type-check *)
          print_endline "Type-checking:";
          let empty_defs : MTm.definitions = Path.emptytbl in
          let empty_ctx = { MTm.kinds = Ident.emptytbl; MTm.types = Ident.emptytbl } in
          
          let show_error (e: MTm.check_error) = match e with
            | MTm.UnboundVariable v -> "Unbound variable: " ^ Ident.name v
            | MTm.UnboundSymbol p -> "Unbound symbol: " ^ Path.name p
            | MTm.TypeMismatch _ -> "Type mismatch"
            | MTm.ExpectedData _ -> "Expected data type"
            | MTm.ExpectedCode _ -> "Expected code type"
            | MTm.SignatureMismatch _ -> "Signature mismatch"
            | MTm.XtorNotInSignature _ -> "Xtor not in signature"
            | MTm.NonExhaustive _ -> "Non-exhaustive"
            | MTm.ArityMismatch _ -> "Arity mismatch"
            | MTm.UnificationFailed _ -> "Unification failed"
          in
          
          (try
            match MTm.infer_term empty_defs empty_ctx melcore_term with
            | Ok (_typed_term, inferred_ty) ->
                Printf.printf "  Inferred: %s\n" (MPrint.typ_to_string inferred_ty);
                Printf.printf "  Expected: %s\n" expected_type;
                print_endline "  OK ✓";
                print_newline ();
                print_endline "PASS ✓";
                incr pass_count
            | Error e ->
                Printf.printf "  Error: %s\n" (show_error e);
                print_newline ();
                print_endline "FAIL: Type-check error"
          with e ->
            Printf.printf "  Exception: %s\n" (Printexc.to_string e);
            print_newline ();
            print_endline "FAIL: Exception during type-check");
          print_newline ()

(* ════════════════════════════════════════════════════════════════════════════
   Test Cases
   ════════════════════════════════════════════════════════════════════════════ *)

let () =
  print_endline "\n╔══════════════════════════════════════════════════════════════╗";
  print_endline "║       Parsing → Desugaring → Melcore Pipeline Tests          ║";
  print_endline "╚══════════════════════════════════════════════════════════════╝\n";

  (* ══════════════════════════════════════════════════════════════════
     Expression Tests (simple expressions without definitions)
     ══════════════════════════════════════════════════════════════════ *)

  run_expr_test
    ~name:"Integer literal"
    ~expected_type:"int"
    "42";

  run_expr_test
    ~name:"Addition"
    ~expected_type:"int"
    "1 + 2";

  run_expr_test
    ~name:"Nested addition"
    ~expected_type:"int"
    "(1 + 2) + 3";

  run_expr_test
    ~name:"Identity function"
    ~expected_type:"int -> int"
    "fun (x: int) => x";

  run_expr_test
    ~name:"Constant function"
    ~expected_type:"int -> int -> int"
    "fun (x: int)(y: int) => x";

  run_expr_test
    ~name:"Addition function"
    ~expected_type:"int -> int -> int"
    "fun (x: int)(y: int) => x + y";

  run_expr_test
    ~name:"Let expression"
    ~expected_type:"int"
    "let x = 5 in x + 1";

  run_expr_test
    ~name:"Nested let"
    ~expected_type:"int"
    "let x = 5 in let y = 10 in x + y";

  run_expr_test
    ~name:"Lambda application"
    ~expected_type:"int"
    "(fun (x: int) => x + 1)(5)";

  run_expr_test
    ~name:"Higher-order function"
    ~expected_type:"(int -> int) -> int -> int"
    "fun (f: int -> int)(x: int) => f(x)";

  (* ══════════════════════════════════════════════════════════════════
     Definition Tests (top-level definitions)
     ══════════════════════════════════════════════════════════════════ *)

  run_test
    ~name:"Simple identity definition"
    {|
let id(x: int): int = x
    |};

  run_test
    ~name:"Add function"
    {|
let add(x: int)(y: int): int = x + y
    |};

  run_test
    ~name:"Compose function"
    {|
let compose(f: int -> int)(g: int -> int)(x: int): int =
  f(g(x))
    |};

  run_test
    ~name:"Multiple definitions"
    {|
let double(x: int): int = x + x

let quadruple(x: int): int = double(double(x))
    |};

  (* ══════════════════════════════════════════════════════════════════
     User-Defined Types Tests
     ══════════════════════════════════════════════════════════════════ *)

  run_test
    ~name:"Simple nat data type"
    {|
data nat: type where
  { zero: nat
  ; succ: nat -> nat
  }

let iszero(n: nat): nat =
  match n with
    { zero => zero
    ; succ(m) => succ(m)
    }
    |};

  run_test
    ~name:"Bool data type with if-then-else"
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

let and(x: bool)(y: bool): bool =
  match x with
    { true => y
    ; false => false
    }
    |};

  run_test
    ~name:"Polymorphic list type"
    {|
data list: type -> type where
  { nil: {a: type} list(a)
  ; cons: {a: type} a -> list(a) -> list(a)
  }

let head{a: type}(default: a)(xs: list(a)): a =
  match xs with
    { nil{b} => default
    ; cons{b}(x)(rest) => x
    }
    |};

  run_test
    ~name:"Option/Maybe type"
    {|
data option: type -> type where
  { none: {a: type} option(a)
  ; some: {a: type} a -> option(a)
  }

let map{a: type}{b: type}(f: a -> b)(opt: option(a)): option(b) =
  match opt with
    { none{x} => none{b}
    ; some{x}(val) => some{b}(f(val))
    }
    |};

  run_test
    ~name:"GADT: typed expressions"
    {|
data expr: type -> type where
  { lit: int -> expr(int)
  ; add: expr(int) -> expr(int) -> expr(int)
  ; ifthenelse: {a: type} expr(bool) -> expr(a) -> expr(a) -> expr(a)
  }

data bool: type where
  { true: bool
  ; false: bool
  }

let eval_bool(e: expr(bool)): bool =
  match e with
    { ifthenelse{a}(cond)(t)(f) =>
        match eval_bool(cond) with
          { true => eval_bool(t)
          ; false => eval_bool(f)
          }
    }

let eval_int(e: expr(int)): int =
  match e with
    { lit(n) => n
    ; add(x)(y) => eval_int(x) + eval_int(y)
    ; ifthenelse{a}(cond)(t)(f) =>
        match eval_bool(cond) with
          { true => eval_int(t)
          ; false => eval_int(f)
          }
    }
    |};

  run_test
    ~name:"Codata: infinite stream"
    {|
code stream: type -> type where
  { head: {a: type} stream(a) -> a
  ; tail: {a: type} stream(a) -> stream(a)
  }

let repeat{a: type}(x: a): stream(a) =
  new stream(a)
    { head => x
    ; tail => repeat{a}(x)
    }
    |};

  (* ══════════════════════════════════════════════════════════════════
     Summary
     ══════════════════════════════════════════════════════════════════ *)

  print_endline "════════════════════════════════════════════════════════════════";
  Printf.printf "Results: %d/%d tests passed\n" !pass_count !test_count;
  if !pass_count = !test_count then
    print_endline "All tests PASSED ✓"
  else
    print_endline "Some tests FAILED";
  print_endline "════════════════════════════════════════════════════════════════\n"
