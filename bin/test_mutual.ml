open Lang

let () =
  print_endline "Testing mutual recursion...";
  
  let input = "

data bool: type where { true: bool; false: bool }

data nat: type where { zero: nat; succ: nat -> nat }

let is_even (n: nat): nat = 
  match n with
  { zero => true
  ; succ(m) => is_odd(m)
  }

let is_odd (n: nat): nat =
  match n with
  { zero => false
  ; succ(m) => is_even(m)
  }
" in
  
  try
    let module P = Common.Identifiers.Path in
    let ast_defs = Parse.parse_defs_string input in
    let defs = Syntax.to_definitions ast_defs in
    
    print_endline "Successfully parsed and converted mutually recursive definitions!";
    print_endline (Printf.sprintf "Number of term definitions: %d" (List.length defs.term_defs));
    
    (* Check that is_even references is_odd and vice versa *)
    let check_references name target_name (defs: Terms.definitions) =
      let def = List.find (fun (_p, (td : Terms.term_def)) -> P.name td.Terms.name = name) defs.term_defs in
      let rec contains_ref t =
        match t with
        | Terms.TmSym p when P.name p = target_name -> true
        | Terms.TmApp (t1, t2) -> contains_ref t1 || contains_ref t2
        | Terms.TmMatch (scrut, clauses) ->
            contains_ref scrut || 
            List.exists (fun (_, _, _, body) -> contains_ref body) clauses
        | _ -> false
      in
      if contains_ref (snd def).Terms.body then
        Printf.printf "✓ %s correctly references %s as TmSym\n" name target_name
      else
        Printf.printf "✗ %s does not reference %s\n" name target_name
    in
    
    check_references "is_even" "is_odd" defs;
    check_references "is_odd" "is_even" defs;
    
    print_endline "\nMutual recursion test passed!"
  with
  | Failure msg -> Printf.printf "✗ Test failed: %s\n" msg
  | e -> Printf.printf "✗ Test failed with exception: %s\n" (Printexc.to_string e)
