open Lang

let test_case name input =
  print_endline ("=== " ^ name ^ " ===");
  try
    let ast_defs = Parse.parse_defs_string input in
    let defs = Syntax.to_definitions ast_defs in
    print_endline (Printf.sprintf "Parsed %d type definitions and %d term definitions" 
      (List.length defs.type_defs) (List.length defs.term_defs));
    
    (* Debug: Show what definitions we have *)
    if name = "Test 4: Codata" then begin
      print_endline "\nType definitions:";
      List.iter (fun (path, _) -> 
        print_endline ("  " ^ Common.Identifiers.Path.name path)
      ) defs.type_defs;
      print_endline "\nTerm definitions:";
      List.iter (fun (path, (td : Terms.term_def)) -> 
        print_endline ("  " ^ Common.Identifiers.Path.name path ^ " : " ^ 
          Types.typ_to_string false td.return_type)
      ) defs.term_defs;
      print_endline ""
    end;
    
    let _typed_defs : Terms.typed_definitions = Terms.check_all defs in
    print_endline "✓ All definitions type check successfully!\n"
  with
  | Failure msg -> 
      print_endline ("✗ Type checking failed: " ^ msg ^ "\n")
  | e -> 
      print_endline ("✗ Error: " ^ Printexc.to_string e ^ "\n")

let () =
  print_endline "=== OCaml Sequent Calculus Type Checker Tests ===\n";
  
  (* Test 1: Simple recursive function *)
  test_case "Test 1: Simple Recursion" "

data nat: type where 
  { zero: nat
  ; succ: nat -> nat
  }

let factorial (n: nat): nat =
  match n with
  { zero => succ(zero)
  ; succ(m) => succ(factorial(m))
  }
";

  (* Test 2: Mutual recursion *)
  test_case "Test 2: Mutual Recursion" "

data nat: type where 
  { zero: nat
  ; succ: nat -> nat
  }

data bool: type where 
  { true: bool
  ; false: bool
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

  (* Test 3: Polymorphic function *)
  test_case "Test 3: Polymorphic Identity" "
let identity{a}(x: a): a = x
";

  (* Test 4: Simple codata *)
  test_case "Test 4: Codata" "

code callback: type -> type where
  { call: {a} callback(a) -> a
  }

let make_callback{a}(value: a): callback(a) =
  new callback(a)
  { call{_}(self) => value
  }
";

  (* Test 5: Polymorphic List *)
  test_case "Test 5: Polymorphic List" "

data list: type -> type where
  { nil: {a} list(a)
  ; cons: {a} a -> list(a) -> list(a)
  }

let singleton{a}(x: a): list(a) =
  cons{a}(x)(nil{a})
";

  (* Test 6: List map and fold *)
  test_case "Test 6: List map and fold" "

data list: type -> type where
  { nil: {a} list(a)
  ; cons: {a} a -> list(a) -> list(a)
  }

let map{a}{b}(f: a -> b)(xs: list(a)): list(b) =
  match xs with
  { nil{a} => nil{b}
  ; cons{a}(x)(rest) => cons{b}(f(x))(map{a}{b}(f)(rest))
  }

let fold{s}{a}(foo: s -> a -> s)(state: s)(xs: list(a)): s =
  match xs with
  { nil{a} => state
  ; cons{a}(x)(rest) =>
    let new_state = foo(state)(x) in
    fold{s}{a}(foo)(new_state)(rest)
  }
";

  (* Test 7: Stream repeat *)
  test_case "Test 7: Stream Repeat" "

code stream: type -> type where
  { head: {a} stream(a) -> a
  ; tail: {a} stream(a) -> stream(a)
  }

let repeat{a}(x: a): stream(a) =
  new
  { head{_}(self) => x
  ; tail{_}(self) => repeat{a}(x)
  }
";

  print_endline "=== All Tests Completed ==="
