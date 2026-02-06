(** Test for the playground transformation from Source to Target language *)

open Sequent.Playground

(* ========================================================================= *)
(* Pretty Printing Helpers                                                   *)
(* ========================================================================= *)

let rec name_to_int : type ctx a. (ctx, a) name -> int = function
  | Z -> 0
  | S n -> 1 + name_to_int n

let rec pp_source_command : type ctx. ctx Source.command -> string = function
  | Source.CutPos (_, lhs, rhs) ->
    Printf.sprintf "CutPos(%s, %s)" (pp_source_term lhs) (pp_source_term rhs)
  | Source.CutNeg (_, lhs, rhs) ->
    Printf.sprintf "CutNeg(%s, %s)" (pp_source_term lhs) (pp_source_term rhs)
  | Source.End -> "End"

and pp_source_term : type ctx. ctx Source.term -> string = function
  | Source.Variable n -> Printf.sprintf "Var(%d)" (name_to_int n)
  | Source.Constructor (_, idx, args) ->
    Printf.sprintf "Ctor(%d, [%s])" idx (pp_source_term_list args)
  | Source.Match (_, branches) ->
    Printf.sprintf "Match([%s])" (pp_source_branches branches)
  | Source.Comatch (_, branches) ->
    Printf.sprintf "Comatch([%s])" (pp_source_branches branches)
  | Source.Destructor (_, idx, args) ->
    Printf.sprintf "Dtor(%d, [%s])" idx (pp_source_term_list args)
  | Source.MuLhsPos (_, cmd) ->
    Printf.sprintf "μ+L.%s" (pp_source_command cmd)
  | Source.MuRhsPos (_, cmd) ->
    Printf.sprintf "μ+R.%s" (pp_source_command cmd)
  | Source.MuLhsNeg (_, cmd) ->
    Printf.sprintf "μ-L.%s" (pp_source_command cmd)
  | Source.MuRhsNeg (_, cmd) ->
    Printf.sprintf "μ-R.%s" (pp_source_command cmd)

and pp_source_term_list : type ctx. ctx Source.term_list -> string = function
  | Source.TLNil -> ""
  | Source.TLCons (t, Source.TLNil) -> pp_source_term t
  | Source.TLCons (t, rest) -> pp_source_term t ^ ", " ^ pp_source_term_list rest

and pp_source_branches : type ctx. ctx Source.branch_list -> string = function
  | Source.BLNil -> ""
  | Source.BLCons (Source.Clause (_, body), Source.BLNil) ->
    Printf.sprintf "{ %s }" (pp_source_command body)
  | Source.BLCons (Source.Clause (_, body), rest) ->
    Printf.sprintf "{ %s }, %s" (pp_source_command body) (pp_source_branches rest)

let rec pp_target_command : type ctx. ctx Target.command -> string = function
  | Target.LetConstructor (_, idx, _, cont) ->
    Printf.sprintf "let x = Ctor(%d) in %s" idx (pp_target_command cont)
  | Target.LetMatch (_, branches, cont) ->
    Printf.sprintf "let x = Match([%s]) in %s" 
      (pp_target_branches branches) (pp_target_command cont)
  | Target.LetComatch (_, branches, cont) ->
    Printf.sprintf "let x = Comatch([%s]) in %s"
      (pp_target_branches branches) (pp_target_command cont)
  | Target.LetDestructor (_, idx, _, cont) ->
    Printf.sprintf "let x = Dtor(%d) in %s" idx (pp_target_command cont)
  | Target.CutConstructor (_, idx, _, v) ->
    Printf.sprintf "CutCtor(%d, Var(%d))" idx (name_to_int v)
  | Target.CutMatch (_, v, branches) ->
    Printf.sprintf "CutMatch(Var(%d), [%s])" (name_to_int v) (pp_target_branches branches)
  | Target.CutComatch (_, branches, v) ->
    Printf.sprintf "CutComatch([%s], Var(%d))" (pp_target_branches branches) (name_to_int v)
  | Target.CutDestructor (_, v, idx, _) ->
    Printf.sprintf "CutDtor(Var(%d), %d)" (name_to_int v) idx
  | Target.End -> "End"

and pp_target_branches : type ctx. ctx Target.branch_list -> string = function
  | Target.BLNil -> ""
  | Target.BLCons (Target.Clause (_, body), Target.BLNil) ->
    Printf.sprintf "{ %s }" (pp_target_command body)
  | Target.BLCons (Target.Clause (_, body), rest) ->
    Printf.sprintf "{ %s }, %s" (pp_target_command body) (pp_target_branches rest)

(* ========================================================================= *)
(* Test Examples                                                             *)
(* ========================================================================= *)

(* A simple signature for a type with two constructors, each with 0 args *)
let bool_sig : signature = [ []; [] ]  (* True, False - no parameters *)

(* A signature for a type with one constructor that takes one argument *)
let box_sig : signature = [ [Lhs (Pos bool_sig)] ]  (* Box(x) *)

(* Test 1: Simple variable cut - CutPos(x, y) where both are variables *)
let test1 () =
  print_endline "\n=== Test 1: CutPos(Var(0), Var(1)) ===";
  (* Context has two variables *)
  let src : ('a * ('b * unit)) Source.command = 
    Source.CutPos (bool_sig, Source.Variable Z, Source.Variable (S Z))
  in
  print_endline ("Source: " ^ pp_source_command src);
  let result = Transform.transform_command src Keep in
  print_endline ("Target: " ^ pp_target_command result)

(* Test 2: Constructor matched against a Match term *)
let test2 () =
  print_endline "\n=== Test 2: CutPos(Ctor(0), Match) ===";
  (* CutPos(True, match { case True => End; case False => End }) *)
  let branch0 : (unit, unit) Source.branch = Source.Clause (AppNil, Source.End) in
  let branch1 : (unit, unit) Source.branch = Source.Clause (AppNil, Source.End) in
  let branches = Source.BLCons (branch0, Source.BLCons (branch1, Source.BLNil)) in
  let src : unit Source.command =
    Source.CutPos (bool_sig, 
      Source.Constructor (bool_sig, 0, Source.TLNil),
      Source.Match (bool_sig, branches))
  in
  print_endline ("Source: " ^ pp_source_command src);
  let result = Transform.transform_command src Keep in
  print_endline ("Target: " ^ pp_target_command result)

(* Test 3: Mu abstraction - μ+R binds a variable *)
let test3 () =
  print_endline "\n=== Test 3: CutPos(Var(0), μ+R.CutPos(Ctor(0), Var(0))) ===";
  (* In context with one variable x:
     CutPos(x, μ+R α. CutPos(True, α))
     This should substitute x for α *)
  let inner_cmd : ('a * ('b * unit)) Source.command =
    Source.CutPos (bool_sig,
      Source.Constructor (bool_sig, 0, Source.TLNil),
      Source.Variable Z)  (* α, the bound variable *)
  in
  let src : ('b * unit) Source.command =
    Source.CutPos (bool_sig,
      Source.Variable Z,  (* x *)
      Source.MuRhsPos (bool_sig, inner_cmd))
  in
  print_endline ("Source: " ^ pp_source_command src);
  let result = Transform.transform_command src Keep in
  print_endline ("Target: " ^ pp_target_command result)

(* Test 4: Two mu abstractions meeting *)
let test4 () =
  print_endline "\n=== Test 4: CutPos(μ+L.End, μ+R.End) ===";
  let src : unit Source.command =
    Source.CutPos (bool_sig,
      Source.MuLhsPos (bool_sig, Source.End),
      Source.MuRhsPos (bool_sig, Source.End))
  in
  print_endline ("Source: " ^ pp_source_command src);
  let result = Transform.transform_command src Keep in
  print_endline ("Target: " ^ pp_target_command result)

(* Test 5: Constructor with arguments *)
let test5 () =
  print_endline "\n=== Test 5: CutPos(Box(True), Match) ===";
  (* CutPos(Box(True), match { case Box(x) => End }) *)
  (* The inner branch binds one parameter, so ps = ('a * unit) 
     and the body lives in context (ps ++ ctx) = ('a * unit) since ctx = unit *)
  let inner_branch : (unit, ('a * unit)) Source.branch = 
    Source.Clause (AppCons AppNil, Source.End)
  in
  let branches : unit Source.branch_list = Source.BLCons (inner_branch, Source.BLNil) in
  let src : unit Source.command =
    Source.CutPos (box_sig,
      Source.Constructor (box_sig, 0, 
        Source.TLCons (Source.Constructor (bool_sig, 0, Source.TLNil), Source.TLNil)),
      Source.Match (box_sig, branches))
  in
  print_endline ("Source: " ^ pp_source_command src);
  let result = Transform.transform_command src Keep in
  print_endline ("Target: " ^ pp_target_command result)

(* Test 6: Negative type - Comatch and Destructor *)
let test6 () =
  print_endline "\n=== Test 6: CutNeg(Comatch, Dtor(0)) (negative cut) ===";
  (* A negative type with one destructor taking no arguments *)
  let neg_sig : signature = [ [] ] in
  let branch : (unit, unit) Source.branch = Source.Clause (AppNil, Source.End) in
  let branches = Source.BLCons (branch, Source.BLNil) in
  let src : unit Source.command =
    Source.CutNeg (neg_sig,
      Source.Comatch (neg_sig, branches),
      Source.Destructor (neg_sig, 0, Source.TLNil))
  in
  print_endline ("Source: " ^ pp_source_command src);
  let result = Transform.transform_command src Keep in
  print_endline ("Target: " ^ pp_target_command result)

(* ========================================================================= *)
(* Main                                                                      *)
(* ========================================================================= *)

let () =
  print_endline "========================================";
  print_endline "Testing Source -> Target Transformation";
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
