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
(* Pretty Printing for Collapsed                                             *)
(* ========================================================================= *)

let rec pp_collapsed_command ?(indent=0) : Collapsed.command -> string = 
  let pad = String.make indent ' ' in
  function
  | Collapsed.Let (_, idx, args, x, cont) ->
    Printf.sprintf "let %s = m%d(%s);\n%s%s" 
      (pp_var x) idx (String.concat ", " (List.map pp_var args)) 
      pad (pp_collapsed_command ~indent cont)
  | Collapsed.Switch (_, v, branches) ->
    Printf.sprintf "switch %s {\n%s%s\n%s}" 
      (pp_var v) pad (pp_collapsed_branches ~indent:(indent+2) branches) pad
  | Collapsed.New (_, branches, x, cont) ->
    Printf.sprintf "new %s = {\n%s%s\n%s};\n%s%s"
      (pp_var x) pad (pp_collapsed_branches ~indent:(indent+2) branches) pad
      pad (pp_collapsed_command ~indent cont)
  | Collapsed.Invoke (_, idx, args, v) ->
    Printf.sprintf "invoke %s m%d(%s)" (pp_var v) idx (String.concat ", " (List.map pp_var args))
  | Collapsed.End -> "end"

and pp_collapsed_branches ?(indent=0) (branches : Collapsed.branch list) : string =
  let pad = String.make indent ' ' in
  String.concat ("\n" ^ pad) (List.mapi (pp_collapsed_branch ~indent) branches)

and pp_collapsed_branch ?(indent=0) (idx : int) (Collapsed.Clause (params, body)) : string =
  let params_str = String.concat ", " (List.map pp_var params) in
  Printf.sprintf "m%d(%s) => %s" idx params_str (pp_collapsed_command ~indent body)

(* ========================================================================= *)
(* Test 7: Function (Lambda) - Full Pipeline to Collapsed                    *)
(* ========================================================================= *)

(**
  Hand-encoding the translation of:
  
    let f = λx. x in f 42
    
  In Kore (polarized sequent calculus), this becomes:
  
    Types:
      Cont = pos { ret(cns Int) }         -- continuation expecting Int result  
      Func = neg { app(prd Cont, prd Int) } -- function: takes continuation + arg
    
    The lambda λx.x becomes:
      comatch { app(k, x) => ⟨x | k.ret⟩ }
    
    Application (f 42) becomes:
      ⟨f | app(μ̃r.halt, 42)⟩
    
  In Source language terms (after Lang → Kore style encoding):
  
    CutNeg(Func)(
      comatch { app(k, x) => CutPos(Cont)(x, k.ret) },
      μ̃Rhs(f). CutNeg(Func)(f, app(μ̃Lhs(r).End, 42))
    )
    
  But we need to represent 42 and the continuation properly.
  For simplicity, let's use a Unit type for the argument.
*)

let test7 () =
  print_endline "\n=== Test 7: Lambda (Identity Function) - Full Pipeline ===";
  print_endline "Encoding: let f = λx. x in f ()";
  print_endline "";
  
  (* 
    Type signatures:
    - Unit = pos { unit() }                      -- single nullary constructor
    - Cont = pos { ret(prd Unit) }               -- continuation takes a Unit VALUE (producer)
    - Func = neg { app(cns Cont, prd Unit) }     -- function takes continuation CONSUMER + Unit VALUE
    
    Note the chirality:
    - In Func.app: first arg is cns (consumer of Cont), second is prd (producer of Unit)
    - This means: function receives a continuation to send result to, and a value argument
  *)
  let unit_sig : signature = [ [] ] in                           (* Unit: one constructor, no args *)
  let cont_sig : signature = [ [Lhs (Pos unit_sig)] ] in         (* Cont: ret(prd Unit) *)
  let func_sig : signature = [ [Rhs (Pos cont_sig); Lhs (Pos unit_sig)] ] in  (* Func: app(cns Cont, prd Unit) *)
  
  print_endline "Signatures:";
  print_endline "  Unit = pos { unit() }";
  print_endline "  Cont = pos { ret(prd Unit) }";
  print_endline "  Func = neg { app(cns Cont, prd Unit) }";
  print_endline "";
  
  (*
    The identity lambda: λx. x
    
    As a comatch (codata definition):
      comatch { 
        app(k, x) => ⟨x | k.ret⟩  -- when applied, return x to continuation k
      }
    
    In Source terms:
      Comatch(func_sig, [
        Clause([k, x], CutPos(cont_sig, Variable(x), Destructor(cont_sig, 0, [Variable(k)])))
      ])
    
    Wait - k is a CONSUMER of Cont (cns Cont), so we use it as a covariable.
    And Cont is POSITIVE, so we destruct it? No - Cont is positive, so k receives constructors.
    
    Actually: k : cns (Pos Cont) means k expects to receive a Constructor of Cont.
    To "invoke ret on k", we send Constructor(ret, [x]) to k:
      CutPos(cont_sig, Constructor(cont_sig, 0, [x]), Variable(k))
  *)
  
  let k = Ident.mk "k" in
  let x = Ident.mk "x" in
  
  (* Body of lambda: send ret(x) to continuation k *)
  (* ⟨ret(x) | k⟩ *)
  let lambda_body =
    Source.CutPos (cont_sig,
      Source.Constructor (cont_sig, 0, [Source.Variable x]),  (* ret(x) *)
      Source.Variable k)                                       (* k *)
  in
  
  (* The lambda itself: comatch { app(k, x) => ⟨ret(x) | k⟩ } *)
  let lambda =
    Source.Comatch (func_sig, [
      Source.Clause ([k; x], lambda_body)
    ])
  in
  
  (*
    Application: f ()
    
    We need to apply the function to unit and provide a continuation.
    The continuation just halts: μ̃r. End
    
    ⟨f | app(μ̃r.End, unit())⟩
    
    In Source terms:
      CutNeg(func_sig, 
        Variable(f), 
        Destructor(func_sig, 0, [MuLhsPos(cont_sig, r, End), Constructor(unit_sig, 0, [])]))
  *)
  
  let f = Ident.mk "f" in
  let r = Ident.mk "r" in
  
  (* The halt continuation: μ̃r. End *)
  let halt_cont = Source.MuLhsPos (cont_sig, r, Source.End) in
  
  (* The unit value: unit() *)
  let unit_val = Source.Constructor (unit_sig, 0, []) in
  
  (* Application: ⟨f | app(halt_cont, unit_val)⟩ *)
  let application =
    Source.CutNeg (func_sig,
      Source.Variable f,
      Source.Destructor (func_sig, 0, [halt_cont; unit_val]))
  in
  
  (*
    Full program: let f = λx.x in f ()
    
    ⟨λx.x | μ̃f. ⟨f | app(...)⟩⟩
    
    In Source terms:
      CutNeg(func_sig, lambda, MuRhsNeg(func_sig, f, application))
  *)
  
  let full_program =
    Source.CutNeg (func_sig,
      lambda,
      Source.MuRhsNeg (func_sig, f, application))
  in
  
  print_endline ("Source:\n  " ^ pp_source_command full_program);
  print_endline "";
  
  (* Transform to Target (8-form) *)
  let target = Transform.transform_command full_program Sub.empty in
  print_endline ("Target (8-form):\n  " ^ pp_target_command target);
  print_endline "";
  
  (* Collapse to Mini-Cut (4-form) *)
  let collapsed = Collapse.collapse_command target in
  print_endline ("Collapsed (Mini-Cut 4-form):\n  " ^ pp_collapsed_command ~indent:2 collapsed)

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
  test7 ();
  print_endline "\n========================================";
  print_endline "All tests completed!";
  print_endline "========================================"
