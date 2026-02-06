(** Test for the simple (untyped) transformation from Source to Target language *)

open Sequent.Simple
open Common.Identifiers

(* ========================================================================= *)
(* Pretty Printing Helpers                                                   *)
(* ========================================================================= *)

let pp_var (x : Ident.t) : string = Ident.name x

let rec pp_source_command : Source.command -> string = function
  | Source.CutPos (_, lhs, rhs) ->
    Printf.sprintf "CutPos(%s, %s)" (pp_source_term lhs) (pp_source_term rhs)
  | Source.CutNeg (_, lhs, rhs) ->
    Printf.sprintf "CutNeg(%s, %s)" (pp_source_term lhs) (pp_source_term rhs)
  | Source.End -> "End"

and pp_source_term : Source.term -> string = function
  | Source.Variable x -> Printf.sprintf "Var(%s)" (pp_var x)
  | Source.Constructor (_, idx, args) ->
    Printf.sprintf "Ctor(%d, [%s])" idx (pp_source_term_list args)
  | Source.Match (_, branches) ->
    Printf.sprintf "Match([%s])" (pp_source_branches branches)
  | Source.Comatch (_, branches) ->
    Printf.sprintf "Comatch([%s])" (pp_source_branches branches)
  | Source.Destructor (_, idx, args) ->
    Printf.sprintf "Dtor(%d, [%s])" idx (pp_source_term_list args)
  | Source.MuLhsPos (_, x, cmd) ->
    Printf.sprintf "μ+L(%s).%s" (pp_var x) (pp_source_command cmd)
  | Source.MuRhsPos (_, x, cmd) ->
    Printf.sprintf "μ+R(%s).%s" (pp_var x) (pp_source_command cmd)
  | Source.MuLhsNeg (_, a, cmd) ->
    Printf.sprintf "μ-L(%s).%s" (pp_var a) (pp_source_command cmd)
  | Source.MuRhsNeg (_, a, cmd) ->
    Printf.sprintf "μ-R(%s).%s" (pp_var a) (pp_source_command cmd)

and pp_source_term_list (terms : Source.term list) : string =
  String.concat ", " (List.map pp_source_term terms)

and pp_source_branches (branches : Source.branch list) : string =
  String.concat ", " (List.map pp_source_branch branches)

and pp_source_branch (Source.Clause (params, body)) : string =
  let params_str = String.concat ", " (List.map pp_var params) in
  Printf.sprintf "{ (%s) => %s }" params_str (pp_source_command body)

let rec pp_target_command : Target.command -> string = function
  | Target.LetConstructor (_, idx, args, x, cont) ->
    Printf.sprintf "let %s = Ctor(%d, [%s]) in %s" 
      (pp_var x) idx (String.concat ", " (List.map pp_var args)) (pp_target_command cont)
  | Target.LetMatch (_, branches, x, cont) ->
    Printf.sprintf "let %s = Match([%s]) in %s" 
      (pp_var x) (pp_target_branches branches) (pp_target_command cont)
  | Target.LetComatch (_, branches, a, cont) ->
    Printf.sprintf "let %s = Comatch([%s]) in %s"
      (pp_var a) (pp_target_branches branches) (pp_target_command cont)
  | Target.LetDestructor (_, idx, args, a, cont) ->
    Printf.sprintf "let %s = Dtor(%d, [%s]) in %s" 
      (pp_var a) idx (String.concat ", " (List.map pp_var args)) (pp_target_command cont)
  | Target.CutConstructor (_, idx, args, v) ->
    Printf.sprintf "CutCtor(%d, [%s], %s)" idx (String.concat ", " (List.map pp_var args)) (pp_var v)
  | Target.CutMatch (_, v, branches) ->
    Printf.sprintf "CutMatch(%s, [%s])" (pp_var v) (pp_target_branches branches)
  | Target.CutComatch (_, branches, v) ->
    Printf.sprintf "CutComatch([%s], %s)" (pp_target_branches branches) (pp_var v)
  | Target.CutDestructor (_, v, idx, args) ->
    Printf.sprintf "CutDtor(%s, %d, [%s])" (pp_var v) idx (String.concat ", " (List.map pp_var args))
  | Target.End -> "End"

and pp_target_branches (branches : Target.branch list) : string =
  String.concat ", " (List.map pp_target_branch branches)

and pp_target_branch (Target.Clause (params, body)) : string =
  let params_str = String.concat ", " (List.map pp_var params) in
  Printf.sprintf "{ (%s) => %s }" params_str (pp_target_command body)

(* ========================================================================= *)
(* Test Examples                                                             *)
(* ========================================================================= *)

(* A simple signature for a type with two constructors, each with 0 args *)
let bool_sig : signature = [ []; [] ]  (* True, False - no parameters *)

(* A signature for a type with one constructor that takes one argument *)
let box_sig : signature = [ [Lhs (Pos bool_sig)] ]  (* Box(x) *)

(* Test 1: Simple variable cut - CutPos(x, y) where both are variables *)
let test1 () =
  print_endline "\n=== Test 1: CutPos(Var(x), Var(y)) ===";
  let x = Ident.mk "x" in
  let y = Ident.mk "y" in
  let src = Source.CutPos (bool_sig, Source.Variable x, Source.Variable y) in
  print_endline ("Source: " ^ pp_source_command src);
  let result = Transform.transform_command src Sub.empty in
  print_endline ("Target: " ^ pp_target_command result)

(* Test 2: Constructor matched against a Match term *)
let test2 () =
  print_endline "\n=== Test 2: CutPos(Ctor(0), Match) ===";
  (* CutPos(True, match { case True => End; case False => End }) *)
  let branch0 = Source.Clause ([], Source.End) in
  let branch1 = Source.Clause ([], Source.End) in
  let branches = [branch0; branch1] in
  let src =
    Source.CutPos (bool_sig, 
      Source.Constructor (bool_sig, 0, []),
      Source.Match (bool_sig, branches))
  in
  print_endline ("Source: " ^ pp_source_command src);
  let result = Transform.transform_command src Sub.empty in
  print_endline ("Target: " ^ pp_target_command result)

(* Test 3: Mu abstraction - μ+R binds a variable *)
let test3 () =
  print_endline "\n=== Test 3: CutPos(Var(x), μ+R(α).CutPos(Ctor(0), Var(α))) ===";
  (* In context with one variable x:
     CutPos(x, μ+R α. CutPos(True, α))
     This should substitute x for α *)
  let x = Ident.mk "x" in
  let alpha = Ident.mk "α" in
  let inner_cmd =
    Source.CutPos (bool_sig,
      Source.Constructor (bool_sig, 0, []),
      Source.Variable alpha)
  in
  let src =
    Source.CutPos (bool_sig,
      Source.Variable x,
      Source.MuRhsPos (bool_sig, alpha, inner_cmd))
  in
  print_endline ("Source: " ^ pp_source_command src);
  let result = Transform.transform_command src Sub.empty in
  print_endline ("Target: " ^ pp_target_command result)

(* Test 4: Two mu abstractions meeting *)
let test4 () =
  print_endline "\n=== Test 4: CutPos(μ+L(x).End, μ+R(α).End) ===";
  let x = Ident.mk "x" in
  let alpha = Ident.mk "α" in
  let src =
    Source.CutPos (bool_sig,
      Source.MuLhsPos (bool_sig, x, Source.End),
      Source.MuRhsPos (bool_sig, alpha, Source.End))
  in
  print_endline ("Source: " ^ pp_source_command src);
  let result = Transform.transform_command src Sub.empty in
  print_endline ("Target: " ^ pp_target_command result)

(* Test 5: Constructor with arguments *)
let test5 () =
  print_endline "\n=== Test 5: CutPos(Box(True), Match) ===";
  (* CutPos(Box(True), match { case Box(z) => End }) *)
  let z = Ident.mk "z" in
  let inner_branch = Source.Clause ([z], Source.End) in
  let branches = [inner_branch] in
  let src =
    Source.CutPos (box_sig,
      Source.Constructor (box_sig, 0, 
        [Source.Constructor (bool_sig, 0, [])]),
      Source.Match (box_sig, branches))
  in
  print_endline ("Source: " ^ pp_source_command src);
  let result = Transform.transform_command src Sub.empty in
  print_endline ("Target: " ^ pp_target_command result)

(* Test 6: Negative type - Comatch and Destructor *)
let test6 () =
  print_endline "\n=== Test 6: CutNeg(Comatch, Dtor(0)) (negative cut) ===";
  (* A negative type with one destructor taking no arguments *)
  let neg_sig : signature = [ [] ] in
  let branch = Source.Clause ([], Source.End) in
  let branches = [branch] in
  let src =
    Source.CutNeg (neg_sig,
      Source.Comatch (neg_sig, branches),
      Source.Destructor (neg_sig, 0, []))
  in
  print_endline ("Source: " ^ pp_source_command src);
  let result = Transform.transform_command src Sub.empty in
  print_endline ("Target: " ^ pp_target_command result)

(* ========================================================================= *)
(* Main                                                                      *)
(* ========================================================================= *)

let () =
  print_endline "========================================";
  print_endline "Testing Simple Source -> Target Transform";
  print_endline "========================================";
  test1 ();
  test2 ();
  test3 ();
  test4 ();
  test5 ();
  test6 ();
  print_endline "\n========================================";
  print_endline "All tests completed!";
  print_endline "========================================"
