(**
  Minimal test for nat data type
*)

module Syntax = Lang.Syntax
module Parse = Lang.Parse
module MT = Melcore.Types.MelcoreTypes
module MTm = Melcore.Terms
module MPrint = Melcore.Printing
open Common.Identifiers

let () =
  let source = {|
data nat: type where
  { zero: nat
  ; succ: nat -> nat
  }

let iszero(n: nat): nat =
  match n with
    { zero => zero
    ; succ(m) => succ(m)
    }
  |} in
  
  print_endline "Parsing...";
  let ast_defs = Parse.parse_defs_string source in
  print_endline "OK";
  
  print_endline "Desugaring...";
  let result = Sequent.Desugar.desugar ast_defs in
  let melcore_defs = result.Sequent.Desugar.term_defs in
  let type_defs = result.Sequent.Desugar.type_defs in
  print_endline "OK";
  
  print_endline "\nType defs:";
  List.iter (fun (dec: MT.dec) ->
    Printf.printf "  %s:\n" (Path.name dec.name);
    List.iter (fun (xtor: MT.xtor) ->
      Printf.printf "    %s: quant=%d, args=%d\n"
        (Path.name xtor.name)
        (List.length xtor.quantified)
        (List.length xtor.argument_types)
    ) dec.xtors
  ) type_defs;
  
  print_endline "\nMelcore:";
  Path.to_list melcore_defs
  |> List.iter (fun (_, def) ->
      Printf.printf "%s\n" (MPrint.term_def_to_string def));
  
  (* Debug: inspect the actual AST *)
  print_endline "\nAST inspection:";
  Path.to_list melcore_defs
  |> List.iter (fun (_, (def: MTm.term_def)) ->
      let rec show_term t = match t with
        | MTm.Ctor (dec, xtor, ty_args, tm_args) ->
            Printf.sprintf "Ctor(%s, %s, ty=%d, tm=%d)"
              (Path.name dec) (Path.name xtor)
              (List.length ty_args) (List.length tm_args)
        | MTm.Var v -> Printf.sprintf "Var(%s)" (Ident.name v)
        | MTm.Sym s -> Printf.sprintf "Sym(%s)" (Path.name s)
        | MTm.App (f, x) -> Printf.sprintf "App(%s, %s)" (show_term f) (show_term x)
        | MTm.Match (scrut, branches) ->
            Printf.sprintf "Match(%s, [%s])"
              (show_term scrut)
              (String.concat "; " (List.map show_branch branches))
        | _ -> "..."
      and show_branch (xtor, ty_vars, tm_vars, body) =
        Printf.sprintf "%s(%d ty, %d tm) => %s"
          (Path.name xtor) (List.length ty_vars) (List.length tm_vars) (show_term body)
      in
      Printf.printf "  %s: %s\n" (Path.name def.name) (show_term def.body));
  
  print_endline "\nType-checking...";
  let tc_ctx = MTm.make_tc_context type_defs melcore_defs in
  Path.to_list melcore_defs
  |> List.iter (fun (_, (def: MTm.term_def)) ->
      Printf.printf "  Checking %s: %!" (Path.name def.name);
      match MTm.check_definition tc_ctx def with
      | Ok _ -> print_endline "OK"
      | Error e -> Printf.printf "Error: %s\n" (match e with
          | MTm.UnboundVariable v -> "Unbound: " ^ Ident.name v
          | MTm.UnboundSymbol p -> "Unbound symbol: " ^ Path.name p
          | MTm.UnboundDeclaration p -> "Unbound declaration: " ^ Path.name p
          | MTm.UnboundXtor (dec, xtor) -> 
              Printf.sprintf "Unbound xtor %s in %s" (Path.name xtor) (Path.name dec)
          | MTm.ExpectedData t -> "Expected data: " ^ MPrint.typ_to_string t
          | MTm.ExpectedCodata t -> "Expected codata: " ^ MPrint.typ_to_string t
          | MTm.ExpectedFun t -> "Expected function: " ^ MPrint.typ_to_string t
          | MTm.ExpectedForall t -> "Expected forall: " ^ MPrint.typ_to_string t
          | MTm.TypeMismatch {expected; actual} -> 
              Printf.sprintf "Type mismatch: expected %s, got %s" 
                (MPrint.typ_to_string expected) (MPrint.typ_to_string actual)
          | MTm.NonExhaustive _ -> "Non-exhaustive"
          | MTm.XtorArityMismatch {xtor; expected; got} ->
              Printf.sprintf "Arity mismatch for %s: expected %d, got %d"
                (Path.name xtor) expected got
          | MTm.TypeArgArityMismatch {xtor; expected; got} ->
              Printf.sprintf "Type arg arity mismatch for %s: expected %d, got %d"
                (Path.name xtor) expected got
          | MTm.UnificationFailed (t1, t2) ->
              Printf.sprintf "Unification failed: %s vs %s"
                (MPrint.typ_to_string t1) (MPrint.typ_to_string t2)
          | MTm.KindError _ -> "Kind error"));
  
  print_endline "Done!"
