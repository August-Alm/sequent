(** 
  Test file for the full compilation pipeline:
  
    Lang (parse) → Lang (typed) → Kore → Cut (linearized)
    
  Tests the following stages:
  1. Parse Lang source code from strings
  2. Type-check Lang definitions
  3. Polarize Lang to Kore (positive fragment)
  4. Type-check Kore definitions  
  5. Focus Kore to Cut (with linearization)
  6. Type-check Cut program
*)

open Common.Identifiers

module P = Path
module I = Ident

(* ========================================================================= *)
(* Test Infrastructure                                                       *)
(* ========================================================================= *)

type test_result =
  | Pass
  | Fail of string

let run_test (name: string) (f: unit -> test_result) : unit =
  print_endline ("\n=== " ^ name ^ " ===");
  match f () with
  | Pass -> 
    print_endline "✓ PASSED"
  | Fail msg -> 
    print_endline ("✗ FAILED: " ^ msg)

let expect_ok (name: string) (f: unit -> unit) : test_result =
  try
    f ();
    Pass
  with
  | e -> Fail (Printexc.to_string e)

let expect_exn (name: string) (f: unit -> unit) : test_result =
  try
    f ();
    Fail "expected exception but none raised"
  with
  | _ -> Pass

(* ========================================================================= *)
(* Pipeline Steps                                                            *)
(* ========================================================================= *)

(** Parse Lang definitions from string *)
let parse_lang (input: string) : Lang.Syntax.ast_defs =
  Lang.Parse.parse_defs_string input

(** Convert parsed AST to internal representation *)
let to_definitions (ast: Lang.Syntax.ast_defs) : Lang.Terms.definitions =
  Lang.Syntax.to_definitions ast

(** Type-check Lang definitions *)
let typecheck_lang (defs: Lang.Terms.definitions) : Lang.Terms.typed_definitions =
  Lang.Terms.check_all defs

(** Polarize to Kore: extract signatures and build environment *)
let polarize_signatures (defs: Lang.Terms.typed_definitions) : Kore.Types.signatures =
  Sequent.Polarize.signatures defs

(** Translate a single typed term definition to Kore definition *)
let polarize_term_def
    (sgns: Kore.Types.signatures)
    (def: Lang.Terms.typed_term_def)
    : Kore.Terms.definition =
  (* Build the Kore term from the body *)
  let body_term = Sequent.Polarize.map_term sgns def.Lang.Terms.body in
  
  (* The return type (Kore positive) *)
  let ret_ty = Sequent.Polarize.map_type def.Lang.Terms.return_type in
  
  (* Map type parameters *)
  let type_params = List.map (fun (v, k) ->
    (v, Sequent.Polarize.map_kinds k)
  ) def.Lang.Terms.type_args in
  
  (* Map term parameters to chiral types (all producers in positive fragment) *)
  let term_params = List.map (fun (v, ty) ->
    (v, Kore.Types.Lhs (Sequent.Polarize.map_type ty))
  ) def.Lang.Terms.term_args in
  
  (* Generate the continuation variable *)
  let k = I.fresh () in
  
  (* Build body command: ⟨body_term | k⟩ *)
  let body_cmd = Kore.Terms.CutPos (ret_ty, body_term, Kore.Terms.Variable k) in
  
  { Kore.Terms.name = def.Lang.Terms.name
  ; type_params = type_params
  ; term_params = term_params @ [(k, Kore.Types.Rhs ret_ty)]
  ; body = body_cmd
  }

(** Build Kore environment from typed Lang definitions *)
let build_kore_env (defs: Lang.Terms.typed_definitions) : Kore.Terms.Env.t =
  let sgns = polarize_signatures defs in
  let env = { Kore.Terms.Env.empty with signatures = sgns } in
  List.fold_left (fun env (_, def) ->
    let kore_def = polarize_term_def sgns def in
    Kore.Terms.Env.add_definition env kore_def
  ) env defs.Lang.Terms.term_defs

(** Type-check Kore definitions *)
let typecheck_kore (env: Kore.Terms.Env.t) : unit =
  Kore.Terms.check_definitions
    env.Kore.Terms.Env.imports
    env.Kore.Terms.Env.signatures
    env.Kore.Terms.Env.terms

(** Focus Kore to Cut (with linearization) *)
let focus_to_cut (env: Kore.Terms.Env.t) : Cut.Terms.definitions =
  Sequent.Focus.map_env env

(** Type-check Cut program *)
let typecheck_cut (defs: Cut.Terms.definitions) : unit =
  (* Build extern environment from Kore imports *)
  let kore_imports = Kore.Builtins.Ext.imports in
  let extern_env : Cut.Terms.extern_env =
    List.map (fun (path, (imp: Kore.Terms.import)) ->
      let input_tys = List.map Sequent.Focus.map_chiral imp.parameter_types in
      let output_clauses = List.map (fun clause_tys ->
        List.map (fun ct ->
          let v = I.fresh () in
          (v, Sequent.Focus.map_chiral ct)
        ) clause_tys
      ) imp.clauses_types in
      (path, (input_tys, output_clauses))
    ) (P.to_list kore_imports)
  in
  Cut.Terms.check_program defs.signatures extern_env defs.program

(** Full pipeline: string -> Cut definitions *)
let full_pipeline (input: string) : Cut.Terms.definitions =
  let ast = parse_lang input in
  let defs = to_definitions ast in
  let typed = typecheck_lang defs in
  let kore_env = build_kore_env typed in
  typecheck_kore kore_env;
  let cut_defs = focus_to_cut kore_env in
  typecheck_cut cut_defs;
  cut_defs

(* ========================================================================= *)
(* Pretty-printing helpers                                                   *)
(* ========================================================================= *)

let print_kore_env (env: Kore.Terms.Env.t) : unit =
  print_endline "Kore Definitions:";
  List.iter (fun (path, def) ->
    print_endline (Printf.sprintf "  %s:" (P.name path));
    print_endline (Printf.sprintf "    %s" 
      (Kore.Printing.pp_definition ~show_types:true def))
  ) (P.to_list env.Kore.Terms.Env.terms)

let print_cut_program (defs: Cut.Terms.definitions) : unit =
  print_endline "Cut Program:";
  print_endline (Cut.Printing.pp_program ~show_types:true defs.program)

(* ========================================================================= *)
(* Test Cases                                                                *)
(* ========================================================================= *)

(** Test: identity function *)
let test_identity () =
  let input = "
    let id{a}(x: a): a = x
  " in
  run_test "Identity function" (fun () ->
    expect_ok "pipeline" (fun () ->
      let _ = full_pipeline input in ()
    ))

(** Test: boolean type *)
let test_bool () =
  let input = "
    data bool: type where
      { true: bool
      ; false: bool
      }
    
    let not (b: bool): bool =
      match b with
        { true => false
        ; false => true
        }
  " in
  run_test "Boolean negation" (fun () ->
    expect_ok "pipeline" (fun () ->
      let _ = full_pipeline input in ()
    ))

(** Test: natural numbers *)
let test_nat () =
  let input = "
    data nat: type where
      { zero: nat
      ; succ: nat -> nat
      }
    
    data bool: type where
      { true: bool
      ; false: bool
      }
    
    let is_zero (n: nat): bool =
      match n with
        { zero => true
        ; succ(m) => false
        }
  " in
  run_test "Natural numbers" (fun () ->
    expect_ok "pipeline" (fun () ->
      let _ = full_pipeline input in ()
    ))

(** Test: polymorphic pairs *)
let test_pair () =
  let input = "
    data pair: type -> type -> type where
      { mk_pair: {a}{b} a -> b -> pair(a)(b)
      }
    
    let fst{a}{b}(p: pair(a)(b)): a =
      match p with
        { mk_pair{a}{b}(x)(y) => x
        }
    
    let snd{a}{b}(p: pair(a)(b)): b =
      match p with
        { mk_pair{a}{b}(x)(y) => y
        }
  " in
  run_test "Polymorphic pairs" (fun () ->
    try
      let ast = parse_lang input in
      let defs = to_definitions ast in
      let typed = typecheck_lang defs in
      let kore_env = build_kore_env typed in
      Printf.printf "  Kore:\n";
      print_kore_env kore_env;
      typecheck_kore kore_env;
      Printf.printf "  Kore typechecked OK\n";
      let cut_defs = focus_to_cut kore_env in
      Printf.printf "  Cut:\n";
      print_cut_program cut_defs;
      typecheck_cut cut_defs;
      Pass
    with e ->
      Fail (Printexc.to_string e))

(** Test: lists *)
let test_list () =
  let input = "
    data list: type -> type where
      { nil: {a} list(a)
      ; cons: {a} a -> list(a) -> list(a)
      }
    
    data bool: type where
      { true: bool
      ; false: bool
      }
    
    let is_empty{a}(xs: list(a)): bool =
      match xs with
        { nil{a} => true
        ; cons{a}(h)(t) => false
        }
  " in
  run_test "Lists" (fun () ->
    expect_ok "pipeline" (fun () ->
      let _ = full_pipeline input in ()
    ))

(** Test: let binding *)
let test_let () =
  let input = "
    data nat: type where
      { zero: nat
      ; succ: nat -> nat
      }
    
    let double_succ (n: nat): nat =
      let m = succ(n) in
      succ(m)
  " in
  run_test "Let binding" (fun () ->
    expect_ok "pipeline" (fun () ->
      let _ = full_pipeline input in ()
    ))

(** Test: integer literals and arithmetic *)
let test_int_arith () =
  let input = "
    let add_ints (x: int) (y: int): int = x + y
  " in
  run_test "Integer arithmetic" (fun () ->
    expect_ok "pipeline" (fun () ->
      let _ = full_pipeline input in ()
    ))

(** Test: function composition *)
let test_compose () =
  let input = "
    let compose{a}{b}{c}(f: b -> c)(g: a -> b)(x: a): c =
      f(g(x))
  " in
  run_test "Function composition" (fun () ->
    expect_ok "pipeline" (fun () ->
      let _ = full_pipeline input in ()
    ))

(** Test: higher-order function *)
let test_apply () =
  let input = "
    let apply{a}{b}(f: a -> b)(x: a): b =
      f(x)
  " in
  run_test "Higher-order apply" (fun () ->
    expect_ok "pipeline" (fun () ->
      let _ = full_pipeline input in ()
    ))

(** Test: mutual recursion - even/odd *)
let test_mutual () =
  let input = "
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
  " in
  run_test "Mutual recursion" (fun () ->
    expect_ok "pipeline" (fun () ->
      let _ = full_pipeline input in ()
    ))

(** Test: verbose mode with intermediate output *)
let test_verbose () =
  let input = "
    data unit: type where { tt: unit }
    let const{a}(x: a)(u: unit): a = x
  " in
  run_test "Verbose pipeline" (fun () ->
    expect_ok "verbose" (fun () ->
      print_endline "\n--- Verbose Pipeline Test ---";
      
      print_endline "\n[1] Parsing...";
      let ast = parse_lang input in
      print_endline "    Parsed OK";
      
      print_endline "\n[2] Converting to internal representation...";
      let defs = to_definitions ast in
      print_endline "    Converted OK";
      
      print_endline "\n[3] Type-checking Lang...";
      let typed = typecheck_lang defs in
      print_endline "    Type-checked OK";
      
      print_endline "\n[4] Polarizing to Kore...";
      let kore_env = build_kore_env typed in
      print_endline "    Polarized OK";
      print_kore_env kore_env;
      
      print_endline "\n[5] Type-checking Kore...";
      (try 
        typecheck_kore kore_env;
        print_endline "    Type-checked OK"
      with e ->
        print_endline ("    Kore type error: " ^ Kore.Printing.pp_type_check_exn e);
        raise e);
      
      print_endline "\n[6] Focusing to Cut...";
      let cut_defs = focus_to_cut kore_env in
      print_endline "    Focused OK";
      print_cut_program cut_defs;
      
      print_endline "\n[7] Type-checking Cut...";
      (try 
        typecheck_cut cut_defs;
        print_endline "    Type-checked OK"
      with e ->
        print_endline ("    Cut type error: " ^ Cut.Printing.pp_type_check_exn e);
        raise e);
      
      print_endline "\n--- Pipeline Complete ---"
    ))

(* ========================================================================= *)
(* Error Case Tests                                                          *)
(* ========================================================================= *)

(** Test: parse error *)
let test_parse_error () =
  let input = "let x: = 42" in (* missing type *)
  run_test "Parse error" (fun () ->
    expect_exn "parse error" (fun () ->
      let _ = parse_lang input in ()
    ))

(** Test: Lang type error - unbound variable *)
let test_lang_unbound () =
  let input = "
    let foo (x: int): int = y
  " in
  run_test "Lang unbound variable" (fun () ->
    expect_exn "type error" (fun () ->
      let ast = parse_lang input in
      let defs = to_definitions ast in
      let _ = typecheck_lang defs in ()
    ))

(* ========================================================================= *)
(* Main                                                                      *)
(* ========================================================================= *)

let () =
  print_endline "========================================";
  print_endline "  Focus Pipeline Tests";
  print_endline "========================================";
  
  (* Basic tests *)
  test_identity ();
  test_bool ();
  test_nat ();
  test_pair ();
  test_list ();
  test_let ();
  test_int_arith ();
  test_compose ();
  test_apply ();
  test_mutual ();
  
  (* Verbose test with intermediate output *)
  test_verbose ();
  
  (* Error tests *)
  test_parse_error ();
  test_lang_unbound ();
  
  print_endline "\n========================================";
  print_endline "  All tests completed";
  print_endline "========================================"
