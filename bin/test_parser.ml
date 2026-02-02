(** Simple test of the parser *)

open Lang

let () =
  print_endline "Testing parser...";
  
  (* Test simple expressions *)
  let test_cases = [
    ("42", "integer literal");
    ("x", "variable");
    ("fun x => x", "simple lambda");
    ("fun(x: int) => x", "annotated lambda");
    ("fun{a}(x: a) => x", "polymorphic identity, implicit kind");
    ("(fun{a: type}(x: a) => x)(42)", "lambda application");
    ("foo{int}(fun{a}(x: a) => x)(baz)", "lambda as argument");
    ("let x = 5 in x", "let binding");
    ("f(x)", "function application");
    ("f{int}", "instantiation");
    ("match x with { nil{a} => 0; cons{a}(h)(t) => h }", "match expression");
    ("--- this is a comment\n42", "line comment");
    ("new { fst(_) => 1; snd(_) => 2 }", "new code expression");
    ("new pair(int)(int) { fst(_) => 1; snd(_) => 2 }", "annotated new code expression");
  ] in
  
  List.iter (fun (input, desc) ->
    try
      let _ast = Parse.parse_expr_string input in
      Printf.printf "✓ %s: '%s'\n" desc input
    with
    | Failure msg -> Printf.printf "✗ %s: '%s' - %s\n" desc input msg
    | _ -> Printf.printf "✗ %s: '%s' - unknown error\n" desc input
  ) test_cases;
  
  (* Test top-level definitions *)
  print_endline "\nTesting top-level definitions...";
  let defs_input = "
    type endo = {a} a -> a
    
    data list: type -> type where
      { nil: {a} list(a)
      ; cons: {a} a -> list(a) -> list(a)
      }
    
    code pair: type -> type -> type where
      { fst: {a} {b} pair(a)(b) -> a
      ; snd: {a} {b} pair(a)(b) -> b
      }
    
    let identity{a}(x: a): a = x
    
    let map{a}{b}(f: a -> b)(xs: list(a)): list(b) =
      match xs with
      { nil{a} => nil{b}
      ; cons{a}(x)(rest) => cons{b}(f(x))(map{a}{b}(f)(rest))
      }
  " in
  (try
    let defs = Parse.parse_defs_string defs_input in
    let type_count = List.length defs.type_defs in
    let term_count = List.length defs.term_defs in
    Printf.printf "✓ Parsed %d type definitions and %d term definitions\n" 
      type_count term_count
  with
  | Failure msg -> Printf.printf "✗ Failed to parse definitions: %s\n" msg
  | _ -> Printf.printf "✗ Failed to parse definitions: unknown error\n");
  
  (* Test round-trip: parse -> to_string -> parse *)
  print_endline "\nTesting round-trip conversion...";
  let roundtrip_cases = [
    ("42", "integer");
    ("x", "variable");
    ("fun{a: type}(x: a) => x", "typed lambda");
    ("f(x)(y)", "multiple applications");
    ("match x with { nil{a} => 0; cons{a}(h)(t) => h }", "match");
  ] in
  
  List.iter (fun (input, desc) ->
    try
      let ast1 = Parse.parse_expr_string input in
      let str = Syntax.ast_to_string 0 ast1 in
      let _ast2 = Parse.parse_expr_string str in
      Printf.printf "✓ Round-trip %s: %s\n" desc str
    with
    | Failure msg -> Printf.printf "✗ Round-trip %s failed: %s\n" desc msg
    | _ -> Printf.printf "✗ Round-trip %s failed: unknown error\n" desc
  ) roundtrip_cases;
  
  (* Test round-trip for definitions *)
  print_endline "\nTesting round-trip for definitions...";
  (try
    let defs1 = Parse.parse_defs_string defs_input in
    let defs_str = Syntax.defs_to_string defs1 in
    print_endline "Generated definitions:";
    print_endline "---";
    print_endline defs_str;
    print_endline "---";
    let defs2 = Parse.parse_defs_string defs_str in
    Printf.printf "✓ Round-trip succeeded: %d type defs, %d term defs\n"
      (List.length defs2.type_defs) (List.length defs2.term_defs)
  with
  | Failure msg -> Printf.printf "✗ Round-trip definitions failed: %s\n" msg
  | _ -> Printf.printf "✗ Round-trip definitions failed: unknown error\n");
  
  (* Test conversion to internal representation *)
  print_endline "\nTesting conversion to internal terms...";
  let simple_defs_input = "
    data nat: type where {
      zero: nat;
      succ: nat -> nat
    }
    
    code stream: type -> type where {
      head: {a} stream(a) -> a;
      tail: {a} stream(a) -> stream(a)
    }
  " in
  (try
    let ast_defs = Parse.parse_defs_string simple_defs_input in
    
    (* Test converting a simple term *)
    let simple_term = Parse.parse_expr_string "fun{a: type}(x: a) => x" in
    let _term = Syntax.to_term ast_defs simple_term in
    Printf.printf "✓ Converted polymorphic identity function\n";
    
    (* Test with constructors *)
    let ctor_term = Parse.parse_expr_string "succ(zero)" in
    let _term2 = Syntax.to_term ast_defs ctor_term in
    Printf.printf "✓ Converted term with constructors\n";
    
    (* Test with match *)
    let match_term = Parse.parse_expr_string "match zero with { zero => 0; succ(n) => 1 }" in
    let _term3 = Syntax.to_term ast_defs match_term in
    Printf.printf "✓ Converted match expression\n"
  with
  | Failure msg -> Printf.printf "✗ Conversion failed: %s\n" msg
  | _ -> Printf.printf "✗ Conversion failed: unknown error\n");
  
  (* Test term definitions and references *)
  print_endline "\nTesting term references...";
  let term_refs_input = "
data nat: type where
  { zero: nat
  ; succ: nat -> nat
  }

let foo (x: nat): nat = succ(x)

let bar (y: nat): nat = foo(succ(y))
" in
  (try
    let module P = Common.Identifiers.Path in
    let module I = Common.Identifiers.Ident in
    let ast_defs = Parse.parse_defs_string term_refs_input in
    let defs = Syntax.to_definitions ast_defs in
    
    let rec show_term t = match t with
      | Terms.TmVar id -> Printf.sprintf "TmVar(%s)" (I.name id)
      | Terms.TmSym path -> Printf.sprintf "TmSym(%s)" (P.name path)
      | Terms.TmInt n -> Printf.sprintf "TmInt(%d)" n
      | Terms.TmAdd (t1, t2) -> Printf.sprintf "TmAdd(%s, %s)" (show_term t1) (show_term t2)
      | Terms.TmApp (t1, t2) -> Printf.sprintf "TmApp(%s, %s)" (show_term t1) (show_term t2)
      | Terms.TmIns (t, _ty) -> Printf.sprintf "TmIns(%s, _)" (show_term t)
      | Terms.TmLam (id, _ty, body) -> 
          Printf.sprintf "TmLam(%s, _, %s)" (I.name id) (show_term body)
      | Terms.TmAll ((id, _), body) -> 
          Printf.sprintf "TmAll(%s, %s)" (I.name id) (show_term body)
      | Terms.TmLet (id, bound, body) -> 
          Printf.sprintf "TmLet(%s, %s, %s)" (I.name id) (show_term bound) (show_term body)
      | Terms.TmMatch (scrut, _clauses) -> Printf.sprintf "TmMatch(%s, ...)" (show_term scrut)
      | Terms.TmNew (_ty, _clauses) -> "TmNew(...)"
      | Terms.TmCtor (xtor, _ty_args, term_args) -> 
          Printf.sprintf "TmCtor(%s, [%s])" 
            (P.name xtor.symbol)
            (String.concat "; " (List.map show_term term_args))
      | Terms.TmDtor (xtor, _ty_args, term_args) -> 
          Printf.sprintf "TmDtor(%s, [%s])" 
            (P.name xtor.symbol)
            (String.concat "; " (List.map show_term term_args))
    in
    
    List.iter (fun (_path, (td : Terms.term_def)) ->
      Printf.printf "✓ Term def: %s\n" (P.name td.Terms.name);
      Printf.printf "    Body: %s\n" (show_term td.Terms.body)
    ) defs.term_defs;
    
    (* Check that bar references foo as TmSym *)
    let bar_def = snd (List.find (fun (_p, (td : Terms.term_def)) -> 
      P.name td.Terms.name = "bar"
    ) defs.term_defs) in
    let contains_foo_sym t =
      let rec check = function
        | Terms.TmSym p when P.name p = "foo" -> true
        | Terms.TmApp (t1, t2) -> check t1 || check t2
        | Terms.TmIns (t, _) -> check t
        | Terms.TmLam (_, _, body) -> check body
        | Terms.TmAll (_, body) -> check body
        | Terms.TmLet (_, bound, body) -> check bound || check body
        | Terms.TmMatch (scrut, clauses) -> 
            check scrut || List.exists (fun (_, _, _, body) -> check body) clauses
        | Terms.TmNew (_, clauses) -> 
            List.exists (fun (_, _, _, body) -> check body) clauses
        | Terms.TmCtor (_, _, args) -> List.exists check args
        | Terms.TmDtor (_, _, args) -> List.exists check args
        | _ -> false
      in check t
    in
    if contains_foo_sym bar_def.body then
      Printf.printf "✓ Bar correctly references foo as TmSym\n"
    else
      Printf.printf "✗ Bar does not reference foo as TmSym\n"
  with
  | Failure msg -> Printf.printf "✗ Term references test failed: %s\n" msg
  | Not_found -> Printf.printf "✗ Could not find bar definition\n"
  | _ -> Printf.printf "✗ Term references test failed: unknown error\n");
  
  print_endline "\nDone!"
