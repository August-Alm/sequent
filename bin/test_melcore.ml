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

module MTy = Melcore.Types.MelcoreTypes
module MTm = Melcore.Terms
module MPrint = Melcore.Printing
module CTy = Core.Types.CoreTypes
module CTm = Core.Terms
module FB = Focused.Types.FocusedBase
module FTy = Focused.Types.FocusedTypes
module FTm = Focused.Terms
module FPrint = Focused.Printing
module Machine = Focused.Semantics
module Encode = Sequent.Encode
module Focus = Sequent.Focus

open Common.Identifiers

(* Test harness *)
let test_count = ref 0
let pass_count = ref 0

(* Empty definitions context for simple terms *)
let empty_defs : MTm.definitions = Path.emptytbl

(* Close a focused command by replacing axiom/invoke on 'ret' with Ret *)
let rec close_ret (ret_ty: FTy.typ) (cmd: FTm.command) : FTm.command =
  match cmd with
  | FTm.Axiom (_, v, k) when Ident.name k = "ret" -> 
      FTm.Ret (ret_ty, v)
  | FTm.Invoke (k, _, _, args) when Ident.name k = "ret" ->
      (* ret.xtor(args) - create a producer and return it *)
      (match args with
        v :: _ -> FTm.Ret (ret_ty, v)
      | [] -> cmd)
  (* Handle SwitchForall on ret: convert to NewForall + Ret *)
  | FTm.SwitchForall (k, a, kind, body) when Ident.name k = "ret" ->
      let v = Ident.fresh () in
      let forall_ty = FTy.Forall (a, kind, ret_ty) in (* TODO: proper body type *)
      FTm.NewForall (v, a, kind, close_ret ret_ty body, FTm.Ret (forall_ty, v))
  (* Handle Switch on ret for signature types (including Fun, Raise, Lower): convert to New + Ret *)
  | FTm.Switch (k, sg, branches) when Ident.name k = "ret" ->
      let v = Ident.fresh () in
      let branches' = List.map (fun (xtor, ty_vars, tm_vars, b) ->
        (xtor, ty_vars, tm_vars, close_ret ret_ty b)
      ) branches in
      FTm.New (v, sg, branches', FTm.Ret (ret_ty, v))
  | FTm.Let (v, dec, xtor, args, body) -> 
      FTm.Let (v, dec, xtor, args, close_ret ret_ty body)
  | FTm.LetInstantiate (v, a, k, ty, body) ->
      FTm.LetInstantiate (v, a, k, ty, close_ret ret_ty body)
  | FTm.New (v, sg, branches, body) ->
      let branches' = List.map (fun (xtor, ty_vars, tm_vars, b) ->
        (xtor, ty_vars, tm_vars, close_ret ret_ty b)
      ) branches in
      FTm.New (v, sg, branches', close_ret ret_ty body)
  | FTm.NewForall (v, a, k, body, cont) ->
      FTm.NewForall (v, a, k, close_ret ret_ty body, close_ret ret_ty cont)
  | FTm.Switch (x, sg, branches) ->
      let branches' = List.map (fun (xtor, ty_vars, tm_vars, b) ->
        (xtor, ty_vars, tm_vars, close_ret ret_ty b)
      ) branches in
      FTm.Switch (x, sg, branches')
  | FTm.SwitchForall (k, a, kind, body) ->
      FTm.SwitchForall (k, a, kind, close_ret ret_ty body)
  | FTm.Lit (n, v, body) -> 
      FTm.Lit (n, v, close_ret ret_ty body)
  | FTm.Add (a, b, r, body) -> 
      FTm.Add (a, b, r, close_ret ret_ty body)
  | FTm.Sub (a, b, r, body) -> 
      FTm.Sub (a, b, r, close_ret ret_ty body)
  | FTm.NewInt (k, v, branch, cont) ->
      FTm.NewInt (k, v, close_ret ret_ty branch, close_ret ret_ty cont)
  | FTm.Ifz (v, t, e) -> 
      FTm.Ifz (v, close_ret ret_ty t, close_ret ret_ty e)
  | _ -> cmd

let run_test ~name ~manual_repr ?expected_result (term: MTm.term) =
  incr test_count;
  print_endline "════════════════════════════════════════════════════════════════";
  Printf.printf "Test %d: %s\n" !test_count name;
  print_endline "────────────────────────────────────────────────────────────────";
  
  (* Track overall success - must pass all stages *)
  let test_passed = ref true in
  let fail reason = 
    test_passed := false;
    Printf.printf "  ✗ %s\n" reason
  in
  
  (* 1. Print manual representation *)
  print_endline "Melcore Term:";
  Printf.printf "  Manual:  %s\n" manual_repr;
  print_newline ();
  
  (* 2. Type-check via infer_term *)
  let empty_ctx : MTm.tc_context = MTm.make_tc_context [] empty_defs in
  
  (* Raw type printer showing internal structure (for debugging) *)
  let rec raw_typ (t: MTy.typ) : string = match t with
    | MTy.Base _ -> "Base"
    | MTy.Ext _ -> "int"
    | MTy.TVar v -> "TVar(" ^ Ident.name v ^ ")"
    | MTy.TMeta v -> "TMeta(" ^ Ident.name v ^ ")"
    | MTy.Forall (x, k, b) -> "Forall(" ^ Ident.name x ^ ", " ^ raw_typ k ^ ", " ^ raw_typ b ^ ")"
    | MTy.Sgn (p, args) -> "Sgn(" ^ Path.name p ^ ", [" ^ String.concat ", " (List.map raw_typ args) ^ "])"
    | MTy.PromotedCtor (d, c, args) -> "PromotedCtor(" ^ Path.name d ^ ", " ^ Path.name c ^ ", [" ^ String.concat ", " (List.map raw_typ args) ^ "])"
    | MTy.Arrow (a, b) -> "Arrow(" ^ raw_typ a ^ ", " ^ raw_typ b ^ ")"
  in
  
  (* Raw Core type printer *)
  let rec raw_core_typ (t: CTy.typ) : string = match t with
    | CTy.Base _ -> "Base"
    | CTy.Ext _ -> "int"
    | CTy.TVar v -> "TVar(" ^ Ident.name v ^ ")"
    | CTy.TMeta v -> "TMeta(" ^ Ident.name v ^ ")"
    | CTy.Forall (x, k, b) -> "Forall(" ^ Ident.name x ^ ", " ^ raw_core_typ k ^ ", " ^ raw_core_typ b ^ ")"
    | CTy.Sgn (p, args) -> "Sgn(" ^ Path.name p ^ ", [" ^ String.concat ", " (List.map raw_core_typ args) ^ "])"
    | CTy.PromotedCtor (d, c, args) -> "PromotedCtor(" ^ Path.name d ^ ", " ^ Path.name c ^ ", [" ^ String.concat ", " (List.map raw_core_typ args) ^ "])"
    | CTy.Arrow (a, b) -> "Arrow(" ^ raw_core_typ a ^ ", " ^ raw_core_typ b ^ ")"
  in
  
  let show_error (e: MTm.check_error) = match e with
    | MTm.UnboundVariable v -> "Unbound variable: " ^ Ident.name v
    | MTm.UnboundSymbol s -> "Unbound symbol: " ^ Path.name s
    | MTm.UnboundDeclaration s -> "Unbound declaration: " ^ Path.name s
    | MTm.UnboundXtor (d, x) -> Printf.sprintf "Unbound xtor %s in %s" (Path.name x) (Path.name d)
    | MTm.TypeMismatch {expected; actual} -> 
        Printf.sprintf "Type mismatch: expected %s, got %s" 
          (MPrint.typ_to_string expected) (MPrint.typ_to_string actual)
    | MTm.ExpectedFun t -> Printf.sprintf "Expected function type, got %s" (MPrint.typ_to_string t)
    | MTm.ExpectedForall t -> Printf.sprintf "Expected forall type, got %s" (MPrint.typ_to_string t)
    | MTm.ExpectedData t -> Printf.sprintf "Expected data type, got %s" (MPrint.typ_to_string t)
    | MTm.ExpectedCodata t -> Printf.sprintf "Expected codata type, got %s" (MPrint.typ_to_string t)
    | MTm.XtorArityMismatch {xtor=_; expected; got} ->
        Printf.sprintf "Xtor arity mismatch: expected %d, got %d" expected got
    | MTm.TypeArgArityMismatch {xtor=_; expected; got} ->
        Printf.sprintf "Type arg arity mismatch: expected %d, got %d" expected got
    | MTm.NonExhaustive _ -> "Non-exhaustive"
    | MTm.UnificationFailed (t1, t2) -> 
        Printf.sprintf "Unification failed:\n      expected: %s\n           raw: %s\n      actual:   %s\n           raw: %s"
          (MPrint.typ_to_string t1) (raw_typ t1) (MPrint.typ_to_string t2) (raw_typ t2)
    | MTm.KindError _ -> "Kind error"
  in
  
  print_endline "Melcore Type-check:";
  let typed_result =
    try
      match MTm.infer_term empty_ctx term with
      | Ok (typed_term, inferred_ty) ->
          print_endline "  ✓ OK";
          Some (typed_term, inferred_ty)
      | Error e ->
          fail (show_error e);
          None
    with e ->
      fail (Printf.sprintf "Exception: %s" (Printexc.to_string e));
      None
  in
  print_newline ();
  
  (match typed_result with
  | None -> ()  (* Already marked as failed *)
  | Some (typed_term, inferred_ty) ->
      (* 3. Normalize (beta-reduce and instantiate) before encoding *)
      let normalized_term = MTm.normalize typed_term in
      
      (* 4. Encode to Core *)
      let encode_ctx : Encode.encode_ctx =
        let sorts =
          CTy.empty_context.decs
          |> Path.to_list
          |> List.map (fun (p, d) -> (p, d.CTy.data_sort))
          |> Path.of_list
        in
        { types = CTy.empty_context; data_sorts = sorts } in
      print_endline "Core Encoding:";
      let core_result =
        try
          let core_term = Encode.encode_term encode_ctx normalized_term in
          let core_ty = Encode.encode_type encode_ctx.data_sorts inferred_ty in
          Printf.printf "  ✓ Melcore type: %s\n" (MPrint.typ_to_string inferred_ty);
          Printf.printf "        raw: %s\n" (raw_typ inferred_ty);
          Printf.printf "    Core type raw: %s\n" (raw_core_typ core_ty);
          Some (core_term, core_ty)
        with e ->
          fail (Printf.sprintf "Encode exception: %s" (Printexc.to_string e));
          None
      in
      print_newline ();
      
      match core_result with
      | None -> ()
      | Some (core_term, core_ty) ->
          (* Print Core term for debugging *)
          print_endline "Core Term:";
          let rec pp_core_term = function
            | CTm.Var v -> Ident.name v
            | CTm.Lit n -> string_of_int n
            | CTm.Ctor (dec, xtor, _) ->
                Printf.sprintf "Ctor(%s, %s, ...)" (Path.name dec.CTy.name) (Path.name xtor)
            | CTm.Dtor (dec, xtor, _) ->
                Printf.sprintf "Dtor(%s, %s, ...)" (Path.name dec.CTy.name) (Path.name xtor)
            | CTm.Match (dec, _) ->
                Printf.sprintf "Match(%s, ...)" (Path.name dec.CTy.name)
            | CTm.Comatch (dec, branches) ->
                let branch_strs = List.map (fun (xtor, _, _, body) ->
                  Printf.sprintf "%s => %s" (Path.name xtor) (pp_core_cmd body)
                ) branches in
                Printf.sprintf "Comatch(%s, [%s])" (Path.name dec.CTy.name) (String.concat "; " branch_strs)
            | CTm.MuPrd (_, v, body) ->
                Printf.sprintf "μ+%s.%s" (Ident.name v) (pp_core_cmd body)
            | CTm.MuCns (_, v, body) ->
                Printf.sprintf "μ-%s.%s" (Ident.name v) (pp_core_cmd body)
            | CTm.NewForall (a, k, _, body) ->
                Printf.sprintf "NewForall(%s:%s, %s)" 
                  (Ident.name a) (FPrint.typ_to_string (Focus.focus_type k)) (pp_core_cmd body)
            | CTm.InstantiateDtor ty ->
                Printf.sprintf "InstantiateDtor(%s)" (FPrint.typ_to_string (Focus.focus_type ty))
          and pp_core_cmd = function
            | CTm.Cut (ty, l, r) ->
                Printf.sprintf "Cut[%s](%s, %s)"
                  (FPrint.typ_to_string (Focus.focus_type ty))
                  (pp_core_term l) (pp_core_term r)
            | CTm.Call (p, _, _) ->
                Printf.sprintf "Call(%s, ...)" (Path.name p)
            | CTm.Add (a, b, r) ->
                Printf.sprintf "Add(%s, %s, %s)" (pp_core_term a) (pp_core_term b) (pp_core_term r)
            | CTm.Sub (a, b, r) ->
                Printf.sprintf "Sub(%s, %s, %s)" (pp_core_term a) (pp_core_term b) (pp_core_term r)
            | CTm.Ifz (cond, t, e) ->
                Printf.sprintf "Ifz(%s, %s, %s)" (pp_core_term cond) (pp_core_cmd t) (pp_core_cmd e)
            | CTm.Ret (ty, t) ->
                Printf.sprintf "Ret[%s](%s)" (FPrint.typ_to_string (Focus.focus_type ty)) (pp_core_term t)
            | CTm.End -> "End"
          in
          Printf.printf "  %s\n\n" (pp_core_term core_term);
          
          (* 4. Create cut with ret consumer and focus *)
          print_endline "Focus (Cut-free):";
          let focus_result =
            try
              let ret = Ident.mk "ret" in
              (* Use MuCns to create a proper consumer binding, matching simple.ml's pattern *)
              let ret_consumer = CTm.MuCns (core_ty, ret, CTm.Ret (core_ty, CTm.Var ret)) in
              let core_cmd = CTm.Cut (core_ty, core_term, ret_consumer) in
              let focused = Focus.focus_command core_cmd in
              let focused_ty = Focus.focus_type core_ty in
              let closed = close_ret focused_ty focused in
              Printf.printf "%s\n" (FPrint.pp_command closed);
              Some (ret, focused_ty, closed)
            with e ->
              fail (Printf.sprintf "Focus exception: %s" (Printexc.to_string e));
              None
          in
          print_newline ();
          
          match focus_result with
          | None -> ()
          | Some (ret, focused_ty, closed) ->
              (* 5. Machine evaluation *)
              print_endline "Machine Evaluation:";
              let eval_result =
                try
                  let trace = false in
                  let ((final_cmd, final_env), step_count) = Machine.eval ~trace closed in
                  Printf.printf "  Steps: %d\n" step_count;
                  Printf.printf "  Final: %s\n" (Machine.cmd_name final_cmd);
                  let result = Machine.get_result (final_cmd, final_env) in
                  (match result with
                   | Some (Machine.IntVal n) ->
                       Printf.printf "  Result: %d\n" n
                   | Some v ->
                       Printf.printf "  Result: %s\n" (Machine.pp_value v)
                   | None -> ());
                  Some result
                with e ->
                  fail (Printf.sprintf "Eval exception: %s" (Printexc.to_string e));
                  None
              in
              
              (* Check expected result if provided *)
              (match expected_result, eval_result with
               | Some expected, Some (Some (Machine.IntVal actual)) when expected = actual ->
                   Printf.printf "  ✓ Expected %d, got %d\n" expected actual
               | Some expected, Some (Some (Machine.IntVal actual)) ->
                   fail (Printf.sprintf "Expected %d, got %d" expected actual)
               | Some expected, Some None ->
                   fail (Printf.sprintf "Expected %d, got no result" expected)
               | Some expected, None ->
                   fail (Printf.sprintf "Expected %d, evaluation failed" expected)
               | Some expected, Some (Some v) ->
                   fail (Printf.sprintf "Expected int %d, got %s" expected (Machine.pp_value v))
               | None, _ -> ());  (* No expected result specified *)
              print_newline ();
              
              (* 6. Focused type checking *)
              print_endline "Focused Type Check:";
              (* Following simple.ml's collapse_chiral: for negative types (codata),
                 the return continuation chirality flips from Cns to Prd.
                 Fun, Lower, Forall are negative (codata); Raise, Int, user Sgn are positive (data). *)
              let is_negative_fty (t: FTy.typ) : bool =
                match t with
                | FTy.Sgn (s, _) when Path.equal s Common.Types.Prim.fun_sym -> true
                | FTy.Sgn (s, _) when Path.equal s Common.Types.Prim.lower_sym -> true
                | FTy.Forall (_, _, _) -> true
                | _ -> false
              in
              let ret_chiral = 
                if is_negative_fty focused_ty 
                then FB.Prd focused_ty  (* Negative type: chirality flips Cns -> Prd *)
                else FB.Cns focused_ty  (* Positive type: stays as Cns *)
              in
              let focused_tc_ctx : FTm.context = 
                { types = FTy.empty_context
                ; term_vars = Ident.add ret ret_chiral Ident.emptytbl
                } in
              (match FTm.check_command focused_tc_ctx Ident.emptytbl closed with
               | Ok () -> print_endline "  ✓ OK"
               | Error e -> 
                   let err_msg = match e with
                     | FTm.UnboundVariable v -> 
                         Printf.sprintf "Unbound variable: %s" (Ident.name v)
                     | FTm.UnboundDeclaration p -> 
                         Printf.sprintf "Unbound declaration: %s" (Path.name p)
                     | FTm.UnboundXtor (d, x) -> 
                         Printf.sprintf "Unbound xtor %s in %s" (Path.name x) (Path.name d)
                     | FTm.UnificationFailed (t1, t2) -> 
                         Printf.sprintf "Unification failed: %s vs %s" 
                           (FPrint.typ_to_string t1) (FPrint.typ_to_string t2)
                     | FTm.ChiralityMismatch { expected_chirality; actual } ->
                         let exp = match expected_chirality with `Prd -> "producer" | `Cns -> "consumer" in
                         let act = match actual with FB.Prd _ -> "producer" | FB.Cns _ -> "consumer" in
                         Printf.sprintf "Chirality mismatch: expected %s, got %s" exp act
                     | FTm.XtorArityMismatch { xtor; expected; got } ->
                         Printf.sprintf "Xtor %s arity mismatch: expected %d, got %d" 
                           (Path.name xtor) expected got
                     | FTm.TypeVarArityMismatch { xtor; expected; got } ->
                         Printf.sprintf "Type var arity mismatch for %s: expected %d, got %d" 
                           (Path.name xtor) expected got
                     | FTm.NonExhaustiveMatch { dec_name; missing=_ } ->
                         Printf.sprintf "Non-exhaustive match on %s" (Path.name dec_name)
                     | FTm.ArityMismatch { expected; got } ->
                         Printf.sprintf "Arity mismatch: expected %d, got %d" expected got
                     | FTm.ExpectedSignature t ->
                         Printf.sprintf "Expected signature type, got %s" (FPrint.typ_to_string t)
                   in
                   fail err_msg));
  
  (* Final verdict *)
  print_newline ();
  if !test_passed then begin
    print_endline "PASS ✓";
    incr pass_count
  end else
    print_endline "FAIL ✗";
  print_newline ()

(* ════════════════════════════════════════════════════════════════════════════
   Helper for building Melcore types
   ════════════════════════════════════════════════════════════════════════════ *)

let int_ty : MTy.typ = MTy.Ext Int
let arrow (a: MTy.typ) (b: MTy.typ) : MTy.typ = Sgn (Common.Types.Prim.fun_sym, [a; b])

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

  (* ══════════════════════════════════════════════════════════════════
     Test 22: Polymorphic identity
     Polymorphic identity: λ{a} x:a. x
     ══════════════════════════════════════════════════════════════════ *)
  let a = Ident.mk "a" in
  let at = MTy.TVar a in
  let x = Ident.mk "x" in
  let id_poly = MTm.All ((a, MTy.Base Melcore.Types.MelcoreBase.Typ), MTm.Lam (x, Some at, MTm.Var x)) in
  run_test
    ~name:"{a}. a -> a: λx:a. x"
    ~manual_repr:"λ{a} x:a. x"
    
    id_poly;

  (* ══════════════════════════════════════════════════════════════════
     Test 23: Applied polymorphic identity
     Identity on integers: (λ{a} x:a. x){Int} 5 = 5
     ══════════════════════════════════════════════════════════════════ *)
  let a = Ident.mk "a" in
  let at = MTy.TVar a in
  let x = Ident.mk "x" in
  let id_poly = MTm.All ((a, MTy.Base Melcore.Types.MelcoreBase.Typ), MTm.Lam (x, Some at, MTm.Var x)) in
  let id_int = MTm.Ins (id_poly, int_ty) in
  let id_int_app = MTm.App (id_int, MTm.Int 5) in
  run_test
    ~name:"Applied polymorphic identity: (λ{a} x:a. x){Int} 5 = 5"
    ~manual_repr:"(λ{a} x:a. x){Int} 5"
    
    id_int_app;

  (* ══════════════════════════════════════════════════════════════════
     Test 24: Applied monomorphic identity
     Identity on integers: (λx:Int. x) 5 = 5
     ══════════════════════════════════════════════════════════════════ *)
  let x = Ident.mk "x" in
  let id_int = MTm.Lam (x, Some int_ty, MTm.Var x) in
  let id_int_app = MTm.App (id_int, MTm.Int 5) in
  run_test
    ~name:"Applied monomorphic identity: (λx:Int. x) 5 = 5"
    ~manual_repr:"(λx:Int. x) 5"
    
    id_int_app;

  (* ══════════════════════════════════════════════════════════════════
     Test 25: Monomorphic identity with expression argument
     (λx:Int. x) (5 + 3) - is the argument evaluated CBV or CBN?
     ══════════════════════════════════════════════════════════════════ *)
  let x = Ident.mk "x" in
  let id_int = MTm.Lam (x, Some int_ty, MTm.Var x) in
  let id_int_expr = MTm.App (id_int, MTm.Add (MTm.Int 5, MTm.Int 3)) in
  run_test
    ~name:"Monomorphic id with expr: (λx:Int. x) (5+3)"
    ~manual_repr:"(λx:Int. x) (5+3)"
    
    id_int_expr;

  (* ══════════════════════════════════════════════════════════════════
     Test 26: Polymorphic identity with expression argument
     (λ{a} x:a. x){Int} (5 + 3) - is the argument evaluated CBV or CBN?
     ══════════════════════════════════════════════════════════════════ *)
  let a = Ident.mk "a" in
  let at = MTy.TVar a in
  let x = Ident.mk "x" in
  let id_poly = MTm.All ((a, MTy.Base Melcore.Types.MelcoreBase.Typ), MTm.Lam (x, Some at, MTm.Var x)) in
  let id_int = MTm.Ins (id_poly, int_ty) in
  let id_poly_expr = MTm.App (id_int, MTm.Add (MTm.Int 5, MTm.Int 3)) in
  run_test
    ~name:"Polymorphic id with expr: (λ{a} x:a. x){Int} (5+3)"
    ~manual_repr:"(λ{a} x:a. x){Int} (5+3)"
    
    id_poly_expr;

  (* Summary *)
  print_endline "════════════════════════════════════════════════════════════════";
  Printf.printf "Results: %d/%d tests passed\n" !pass_count !test_count;
  if !pass_count = !test_count then
    print_endline "All tests PASSED ✓"
  else
    print_endline "Some tests FAILED ✗";
  print_endline "════════════════════════════════════════════════════════════════"
