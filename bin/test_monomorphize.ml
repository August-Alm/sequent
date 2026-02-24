(**
  Test suite for monomorphization pipeline.
  
  This test file:
  1. Parses surface syntax strings using Lang.Parse
  2. Desugars to Melcore using Desugar
  3. Type-checks in Melcore using Melcore.Terms
  4. Encodes to Core using Encode
  5. Runs Monomorphize to generate monomorphic definitions
  6. Prints results and verifies transformation
*)

module Parse = Lang.Parse
module MTy = Melcore.Types.MelcoreTypes
module MTm = Melcore.Terms
module MPrint = Melcore.Printing
module CTy = Core.Types.CoreTypes
module CB = Core.Types.CoreBase
module CTm = Core.Terms
module Mono = Core.Monomorphization
module MonoX = Core.Monomorphize

open Common.Identifiers

(* Test harness *)
let test_count = ref 0
let pass_count = ref 0

(* ========================================================================= *)
(* Pretty Printing Helpers                                                   *)
(* ========================================================================= *)

let rec pp_core_typ (t: CTy.typ) : string =
  match t with
  | CTy.Base CB.Pos -> "+"
  | CTy.Base CB.Neg -> "-"
  | CTy.Ext Int -> "int"
  | CTy.TVar v -> Ident.name v
  | CTy.TMeta v -> "?" ^ Ident.name v
  | CTy.Forall (a, k, b) -> 
      Printf.sprintf "∀%s:%s.%s" (Ident.name a) (pp_core_typ k) (pp_core_typ b)
  | CTy.Sgn (p, []) -> Path.name p
  | CTy.Sgn (p, args) -> 
      Path.name p ^ "<" ^ String.concat ", " (List.map pp_core_typ args) ^ ">"
  | CTy.PromotedCtor (d, c, args) ->
      Printf.sprintf "%s.%s<%s>" (Path.name d) (Path.name c)
        (String.concat ", " (List.map pp_core_typ args))
  | CTy.Arrow (a, b) -> Printf.sprintf "(%s → %s)" (pp_core_typ a) (pp_core_typ b)

let pp_chiral (ct: CTy.chiral_typ) : string =
  match ct with
  | CB.Prd t -> "Prd(" ^ pp_core_typ t ^ ")"
  | CB.Cns t -> "Cns(" ^ pp_core_typ t ^ ")"

let rec pp_core_term (tm: CTm.term) : string =
  match tm with
  | CTm.Var v -> Ident.name v
  | CTm.Lit n -> string_of_int n
  | CTm.Ctor (dec, xtor, args) ->
      Printf.sprintf "%s.%s(%s)" 
        (Path.name dec.CTy.name) (Path.name xtor)
        (String.concat ", " (List.map pp_core_term args))
  | CTm.Dtor (dec, xtor, args) ->
      Printf.sprintf ".%s.%s(%s)"
        (Path.name dec.CTy.name) (Path.name xtor)
        (String.concat ", " (List.map pp_core_term args))
  | CTm.Match (dec, branches) ->
      Printf.sprintf "match<%s> { %s }"
        (Path.name dec.CTy.name)
        (String.concat "; " (List.map pp_branch branches))
  | CTm.Comatch (dec, branches) ->
      Printf.sprintf "comatch<%s> { %s }"
        (Path.name dec.CTy.name)
        (String.concat "; " (List.map pp_branch branches))
  | CTm.MuPrd (ty, v, cmd) ->
      Printf.sprintf "μ+%s:%s.%s" (Ident.name v) (pp_core_typ ty) (pp_core_cmd cmd)
  | CTm.MuCns (ty, v, cmd) ->
      Printf.sprintf "μ-%s:%s.%s" (Ident.name v) (pp_core_typ ty) (pp_core_cmd cmd)
  | CTm.NewForall (a, k, body_ty, cmd) ->
      Printf.sprintf "NewForall(%s:%s, body:%s, %s)"
        (Ident.name a) (pp_core_typ k) (pp_core_typ body_ty) (pp_core_cmd cmd)
  | CTm.InstantiateDtor ty ->
      Printf.sprintf "InstantiateDtor(%s)" (pp_core_typ ty)

and pp_core_cmd (cmd: CTm.command) : string =
  match cmd with
  | CTm.Cut (ty, l, r) ->
      Printf.sprintf "⟨%s | %s⟩[%s]" (pp_core_term l) (pp_core_term r) (pp_core_typ ty)
  | CTm.Call (p, ty_args, tm_args) ->
      Printf.sprintf "Call(%s{%s}(%s))" 
        (Path.name p)
        (String.concat ", " (List.map pp_core_typ ty_args))
        (String.concat ", " (List.map pp_core_term tm_args))
  | CTm.Add (a, b, r) ->
      Printf.sprintf "Add(%s, %s, %s)" (pp_core_term a) (pp_core_term b) (pp_core_term r)
  | CTm.Sub (a, b, r) ->
      Printf.sprintf "Sub(%s, %s, %s)" (pp_core_term a) (pp_core_term b) (pp_core_term r)
  | CTm.Ifz (cond, t, e) ->
      Printf.sprintf "Ifz(%s, %s, %s)" (pp_core_term cond) (pp_core_cmd t) (pp_core_cmd e)
  | CTm.Ret (ty, t) ->
      Printf.sprintf "Ret[%s](%s)" (pp_core_typ ty) (pp_core_term t)
  | CTm.End -> "End"

and pp_branch ((xtor, ty_vars, tm_vars, cmd): CTm.branch) : string =
  let ty_vars_str = match ty_vars with
    | [] -> ""
    | vs -> "{" ^ String.concat ", " (List.map Ident.name vs) ^ "}"
  in
  let tm_vars_str = match tm_vars with
    | [] -> ""
    | vs -> "(" ^ String.concat ", " (List.map Ident.name vs) ^ ")"
  in
  Printf.sprintf "%s%s%s => %s" (Path.name xtor) ty_vars_str tm_vars_str (pp_core_cmd cmd)

let pp_definition (def: CTm.definition) : string =
  let ty_params_str = match def.type_params with
    | [] -> ""
    | ps -> "{" ^ String.concat ", " (List.map (fun (v, k) -> 
        Ident.name v ^ ":" ^ pp_core_typ k) ps) ^ "}"
  in
  let tm_params_str = match def.term_params with
    | [] -> ""
    | ps -> "(" ^ String.concat ", " (List.map (fun (v, ct) ->
        Ident.name v ^ ":" ^ pp_chiral ct) ps) ^ ")"
  in
  Printf.sprintf "def %s%s%s =\n    %s"
    (Path.name def.path) ty_params_str tm_params_str
    (pp_core_cmd def.body)

let pp_dec (dec: CTy.dec) : string =
  let pol_str = match dec.polarity with CB.Pos -> "data" | CB.Neg -> "codata" in
  let xtors_str = dec.xtors |> List.map (fun (x: CTy.xtor) ->
    let quant_str = match x.quantified with
      | [] -> ""
      | qs -> "{" ^ String.concat ", " (List.map (fun (v, k) ->
          Ident.name v ^ ":" ^ pp_core_typ k) qs) ^ "}"
    in
    let args_str = x.argument_types |> List.map pp_chiral |> String.concat ", " in
    Printf.sprintf "  %s%s(%s) : %s" (Path.name x.name) quant_str args_str (pp_core_typ x.main)
  ) |> String.concat "\n" in
  Printf.sprintf "%s %s where\n%s" pol_str (Path.name dec.name) xtors_str

let show_error (e: MTm.check_error) : string =
  match e with
  | MTm.UnboundVariable v -> "Unbound variable: " ^ Ident.name v
  | MTm.UnboundSymbol p -> "Unbound symbol: " ^ Path.name p
  | MTm.UnboundDeclaration p -> "Unbound declaration: " ^ Path.name p
  | MTm.UnboundXtor (dec, xtor) -> 
      Printf.sprintf "Unbound xtor %s in %s" (Path.name xtor) (Path.name dec)
  | MTm.TypeMismatch {expected; actual} ->
      Printf.sprintf "Type mismatch: expected %s, got %s"
        (MPrint.typ_to_string expected) (MPrint.typ_to_string actual)
  | MTm.ExpectedData ty -> "Expected data type, got: " ^ MPrint.typ_to_string ty
  | MTm.ExpectedCodata ty -> "Expected codata type, got: " ^ MPrint.typ_to_string ty
  | MTm.ExpectedFun ty -> "Expected function type, got: " ^ MPrint.typ_to_string ty
  | MTm.ExpectedForall ty -> "Expected forall type, got: " ^ MPrint.typ_to_string ty
  | MTm.NonExhaustive _ -> "Non-exhaustive"
  | MTm.XtorArityMismatch {xtor; expected; got} ->
      Printf.sprintf "Arity mismatch for %s: expected %d, got %d" (Path.name xtor) expected got
  | MTm.TypeArgArityMismatch {xtor; expected; got} ->
      Printf.sprintf "Type arg arity mismatch for %s: expected %d, got %d" (Path.name xtor) expected got
  | MTm.UnificationFailed (t1, t2) ->
      Printf.sprintf "Unification failed: %s ≠ %s" (MPrint.typ_to_string t1) (MPrint.typ_to_string t2)
  | MTm.KindError _ -> "Kind error"

(* ========================================================================= *)
(* Test Runner                                                               *)
(* ========================================================================= *)

let run_test ~name (source: string) =
  incr test_count;
  print_endline "════════════════════════════════════════════════════════════════";
  Printf.printf "Test %d: %s\n" !test_count name;
  print_endline "────────────────────────────────────────────────────────────────";
  
  let test_passed = ref true in
  let fail reason =
    test_passed := false;
    Printf.printf "  ✗ %s\n" reason
  in
  
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
      fail (Printf.sprintf "Parse error: %s" (Printexc.to_string e));
      None
  in
  print_newline ();
  
  match parsed with
  | None -> ()
  | Some ast_defs ->
      (* 2. Desugar *)
      print_endline "Desugaring:";
      let desugared =
        try
          let defs = Sequent.Desugar.desugar ast_defs in
          print_endline "  OK";
          Some defs
        with e ->
          fail (Printf.sprintf "Desugar error: %s" (Printexc.to_string e));
          None
      in
      print_newline ();
      
      match desugared with
      | None -> ()
      | Some result ->
          let melcore_defs = result.Sequent.Desugar.term_defs in
          let type_defs = result.Sequent.Desugar.type_defs in
          
          (* 3. Type-check Melcore *)
          print_endline "Melcore Type-check:";
          let tc_ctx = MTm.make_tc_context type_defs melcore_defs in
          let typed_defs_result = 
            Path.to_list melcore_defs 
            |> List.fold_left (fun acc (path, def) ->
                match acc with
                | None -> None
                | Some lst ->
                    try
                      match MTm.check_definition tc_ctx def with
                      | Ok typed_def -> Some ((path, typed_def) :: lst)
                      | Error e ->
                          fail (Printf.sprintf "Typecheck %s: %s" 
                            (Path.name path) (show_error e));
                          None
                    with e ->
                      fail (Printf.sprintf "Exception checking %s: %s"
                        (Path.name path) (Printexc.to_string e));
                      None
              ) (Some [])
          in
          (match typed_defs_result with
          | None -> ()
          | Some _ -> print_endline "  OK");
          print_newline ();
          
          match typed_defs_result with
          | None -> ()
          | Some typed_defs ->
              let typed_defs = List.rev typed_defs in
              
              (* 4. Encode to Core *)
              print_endline "Encoding to Core:";
              let core_defs_result =
                try
                  let encode_ctx : Sequent.Encode.encode_ctx = 
                    { types = CTy.empty_context } in
                  let core_defs = typed_defs |> List.map (fun (_path, typed_def) ->
                    Sequent.Encode.encode_term_def encode_ctx typed_def
                  ) in
                  print_endline "  OK";
                  Some core_defs
                with e ->
                  fail (Printf.sprintf "Encode error: %s" (Printexc.to_string e));
                  None
              in
              print_newline ();
              
              match core_defs_result with
              | None -> ()
              | Some core_defs ->
                  (* Print Core definitions *)
                  print_endline "Core Definitions:";
                  List.iter (fun def ->
                    Printf.printf "%s\n\n" (pp_definition def)
                  ) core_defs;
                  
                  (* 5. Create execution context and monomorphize *)
                  print_endline "Monomorphization:";
                  let mono_result =
                    try
                      (* Use first definition as main, rest as defs *)
                      let (main, defs) = match core_defs with
                        | [] -> failwith "No definitions"
                        | [d] -> (d, Path.emptytbl)
                        | d :: rest -> 
                            let tbl = List.fold_left (fun acc def ->
                              Path.add def.CTm.path def acc
                            ) Path.emptytbl rest in
                            (d, tbl)
                      in
                      let exe : Mono.exe_ctx = { main; defs } in
                      let result = MonoX.monomorphize exe in
                      print_endline "  OK";
                      Some result
                    with e ->
                      fail (Printf.sprintf "Monomorphize error: %s" (Printexc.to_string e));
                      None
                  in
                  print_newline ();
                  
                  match mono_result with
                  | None -> ()
                  | Some result ->
                      (* Print new declarations *)
                      if result.new_declarations <> [] then begin
                        print_endline "Generated Codata Types:";
                        List.iter (fun dec ->
                          Printf.printf "%s\n\n" (pp_dec dec)
                        ) result.new_declarations
                      end;
                      
                      (* Print mono_infos *)
                      if not (Path.is_empty result.MonoX.mono_infos) then begin
                        print_endline "Mono Infos:";
                        Path.to_list result.MonoX.mono_infos |> List.iter (fun (path, (info: MonoX.mono_info)) ->
                          Printf.printf "  %s:\n" (Path.name path);
                          Printf.printf "    mono_path: %s\n" (Path.name info.MonoX.mono_path);
                          Printf.printf "    instantiations: %d\n" 
                            (List.length info.MonoX.instantiations);
                          List.iteri (fun i inst ->
                            let inst_str = inst |> List.map (fun arg ->
                              match arg with
                              | Mono.GroundExt Int -> "int"
                              | Mono.GroundSgn (p, _) -> Path.name p
                            ) |> String.concat ", " in
                            Printf.printf "      [%d]: %s\n" i inst_str
                          ) info.MonoX.instantiations
                        );
                        print_newline ()
                      end;
                      
                      (* Print transformed definitions *)
                      print_endline "Transformed Definitions:";
                      List.iter (fun def ->
                        Printf.printf "%s\n\n" (pp_definition def)
                      ) result.definitions;
                      
                      if !test_passed then begin
                        print_endline "PASS ✓";
                        incr pass_count
                      end else
                        print_endline "FAIL ✗";
                      print_newline ()

(* ========================================================================= *)
(* Test Cases                                                                *)
(* ========================================================================= *)

(* Direct Core test: manually build a polymorphic definition and call it *)
let run_core_test ~name 
    (make_test: unit -> (Mono.exe_ctx * string)) =
  incr test_count;
  print_endline "════════════════════════════════════════════════════════════════";
  Printf.printf "Test %d: %s\n" !test_count name;
  print_endline "────────────────────────────────────────────────────────────────";
  
  let test_passed = ref true in
  let fail reason =
    test_passed := false;
    Printf.printf "  ✗ %s\n" reason
  in
  
  try
    let (exe, desc) = make_test () in
    
    (* Print description *)
    print_endline "Setup:";
    Printf.printf "%s\n\n" desc;
    
    (* Print definitions *)
    print_endline "Core Definitions:";
    Printf.printf "%s\n\n" (pp_definition exe.Mono.main);
    Path.to_list exe.Mono.defs |> List.iter (fun (_, def) ->
      Printf.printf "%s\n\n" (pp_definition def)
    );
    
    (* Run monomorphization *)
    print_endline "Monomorphization:";
    let mono_result =
      try
        let result = MonoX.monomorphize exe in
        print_endline "  OK";
        Some result
      with e ->
        fail (Printf.sprintf "Error: %s" (Printexc.to_string e));
        None
    in
    print_newline ();
    
    match mono_result with
    | None -> ()
    | Some result ->
        (* Print new declarations *)
        if result.MonoX.new_declarations <> [] then begin
          print_endline "Generated Codata Types:";
          List.iter (fun dec ->
            Printf.printf "%s\n\n" (pp_dec dec)
          ) result.MonoX.new_declarations
        end;
        
        (* Print mono_infos *)
        if not (Path.is_empty result.MonoX.mono_infos) then begin
          print_endline "Mono Infos:";
          Path.to_list result.MonoX.mono_infos |> List.iter (fun (path, (info: MonoX.mono_info)) ->
            Printf.printf "  %s:\n" (Path.name path);
            Printf.printf "    mono_path: %s\n" (Path.name info.MonoX.mono_path);
            Printf.printf "    instantiations: %d\n" 
              (List.length info.MonoX.instantiations);
            List.iteri (fun i inst ->
              let inst_str = inst |> List.map (fun arg ->
                match arg with
                | Mono.GroundExt Int -> "int"
                | Mono.GroundSgn (p, _) -> Path.name p
              ) |> String.concat ", " in
              Printf.printf "      [%d]: %s\n" i inst_str
            ) info.MonoX.instantiations
          );
          print_newline ()
        end;
        
        (* Print transformed definitions *)
        print_endline "Transformed Definitions:";
        List.iter (fun def ->
          Printf.printf "%s\n\n" (pp_definition def)
        ) result.MonoX.definitions;
        
        if !test_passed then begin
          print_endline "PASS ✓";
          incr pass_count
        end else
          print_endline "FAIL ✗";
        print_newline ()
  with e ->
    Printf.printf "  ✗ Setup error: %s\n" (Printexc.to_string e);
    print_endline "FAIL ✗";
    print_newline ()

let () =
  print_endline "\n╔══════════════════════════════════════════════════════════════╗";
  print_endline "║           MONOMORPHIZATION TEST SUITE                        ║";
  print_endline "╚══════════════════════════════════════════════════════════════╝\n";
  
  (* Test 1: Simple non-polymorphic function - from surface syntax *)
  run_test ~name:"Non-polymorphic function (surface)"
    {|
let double(x: int): int = x + x
    |};
  
  (* Test 2: Direct Core test - polymorphic identity with explicit type args in Call *)
  run_core_test ~name:"Polymorphic identity (Core)"
    (fun () ->
      (* Create: 
         def id{a: +}(x: Prd a, k: Cns a) = ⟨x | k⟩
         def main(k: Cns int) = Call(id, [int], [42, k])
      *)
      let a = Ident.mk "a" in
      let x = Ident.mk "x" in
      let k = Ident.mk "k" in
      
      let id_path = Path.of_string "id" in
      let main_path = Path.of_string "main" in
      
      (* def id{a: +}(x: Prd a, k: Cns a) = ⟨x | k⟩ *)
      let id_def : CTm.definition = 
        { path = id_path
        ; type_params = [(a, CTy.Base CB.Pos)]
        ; term_params = [(x, CB.Prd (CTy.TVar a)); (k, CB.Cns (CTy.TVar a))]
        ; body = CTm.Cut (CTy.TVar a, CTm.Var x, CTm.Var k)
        } in
      
      (* def main(k: Cns int) = Call(id, [int], [42, k]) *)
      let main_def : CTm.definition =
        { path = main_path
        ; type_params = []
        ; term_params = [(k, CB.Cns (CTy.Ext Int))]
        ; body = CTm.Call (id_path, [CTy.Ext Int], [CTm.Lit 42; CTm.Var k])
        } in
      
      let exe : Mono.exe_ctx =
        { main = main_def
        ; defs = Path.of_list [(id_path, id_def)]
        } in
      
      (exe, "  id{a}(x, k) = ⟨x | k⟩\n  main(k) = id{int}(42, k)")
    );
  
  (* Test 3: Multiple instantiations *)
  run_core_test ~name:"Multiple instantiations (Core)"
    (fun () ->
      let a = Ident.mk "a" in
      let x = Ident.mk "x" in
      let y = Ident.mk "y" in
      let k = Ident.mk "k" in
      
      let const_path = Path.of_string "const" in
      let test1_path = Path.of_string "test1" in
      let test2_path = Path.of_string "test2" in
      let main_path = Path.of_string "main" in
      
      (* Define a simple "bool" type for testing *)
      let bool_path = Path.of_string "bool" in
      let bool_ty = CTy.Sgn (bool_path, []) in
      
      (* def const{a}(x: Prd a, y: Prd int, k: Cns a) = ⟨x | k⟩ *)
      let const_def : CTm.definition =
        { path = const_path
        ; type_params = [(a, CTy.Base CB.Pos)]
        ; term_params = [(x, CB.Prd (CTy.TVar a)); (y, CB.Prd (CTy.Ext Int)); (k, CB.Cns (CTy.TVar a))]
        ; body = CTm.Cut (CTy.TVar a, CTm.Var x, CTm.Var k)
        } in
      
      (* def test1(k: Cns int) = const{int}(1, 2, k) *)
      let test1_def : CTm.definition =
        { path = test1_path
        ; type_params = []
        ; term_params = [(k, CB.Cns (CTy.Ext Int))]
        ; body = CTm.Call (const_path, [CTy.Ext Int], [CTm.Lit 1; CTm.Lit 2; CTm.Var k])
        } in
      
      (* Create a dummy bool producer *)
      let true_ctor = Path.of_string "true" in
      let bool_dec : CTy.dec = 
        { name = bool_path
        ; polarity = CB.Pos
        ; param_kinds = []
        ; type_args = []
        ; xtors = [{ name = true_ctor; quantified = []; existentials = []; argument_types = []; main = bool_ty }]
        } in
      
      (* def test2(k: Cns bool) = const{bool}(true, 0, k) *)
      let test2_def : CTm.definition =
        { path = test2_path
        ; type_params = []
        ; term_params = [(k, CB.Cns bool_ty)]
        ; body = CTm.Call (const_path, [bool_ty], [CTm.Ctor (bool_dec, true_ctor, []); CTm.Lit 0; CTm.Var k])
        } in
      
      (* def main(k: Cns int) = test1(k) *)
      let main_def : CTm.definition =
        { path = main_path
        ; type_params = []
        ; term_params = [(k, CB.Cns (CTy.Ext Int))]
        ; body = CTm.Call (test1_path, [], [CTm.Var k])
        } in
      
      let exe : Mono.exe_ctx =
        { main = main_def
        ; defs = Path.of_list 
            [ (const_path, const_def)
            ; (test1_path, test1_def)
            ; (test2_path, test2_def)
            ]
        } in
      
      (exe, "  const{a}(x, y, k) = ⟨x | k⟩\n  test1(k) = const{int}(1, 2, k)\n  test2(k) = const{bool}(true, 0, k)")
    );
  
  (* Summary *)
  print_endline "════════════════════════════════════════════════════════════════";
  Printf.printf "Results: %d/%d tests passed\n" !pass_count !test_count;
  print_endline "════════════════════════════════════════════════════════════════"
