(**
  Minimal test for nat data type
*)

module Syntax = Lang.Syntax
module Parse = Lang.Parse
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
  let melcore_defs = Sequent.Desugar.desugar ast_defs in
  print_endline "OK";
  
  print_endline "Melcore:";
  Path.to_list melcore_defs
  |> List.iter (fun (_, def) ->
      Printf.printf "%s\n" (MPrint.term_def_to_string def));
  
  print_endline "\nType-checking...";
  Path.to_list melcore_defs
  |> List.iter (fun (_, (def: MTm.term_def)) ->
      Printf.printf "  Checking %s: %!" (Path.name def.name);
      match MTm.check_definition melcore_defs def with
      | Ok _ -> print_endline "OK"
      | Error e -> Printf.printf "Error: %s\n" (match e with
          | MTm.UnboundVariable v -> "Unbound: " ^ Ident.name v
          | MTm.UnboundSymbol p -> "Unbound symbol: " ^ Path.name p
          | MTm.ExpectedData t -> "Expected data: " ^ MPrint.typ_to_string t
          | MTm.ExpectedCode t -> "Expected code: " ^ MPrint.typ_to_string t
          | MTm.TypeMismatch {expected; actual} -> 
              Printf.sprintf "Type mismatch: expected %s, got %s" 
                (MPrint.typ_to_string expected) (MPrint.typ_to_string actual)
          | MTm.SignatureMismatch _ -> "Signature mismatch"
          | MTm.XtorNotInSignature (x, sgn) -> 
              Printf.sprintf "Xtor %s not in signature %s (xtors: %s)" 
                (Path.name x.name)
                (Path.name sgn.name)
                (String.concat ", " (List.map (fun (xt: Melcore.Types.xtor) -> 
                  Path.name xt.name
                ) sgn.xtors))
          | MTm.NonExhaustive _ -> "Non-exhaustive"
          | MTm.ArityMismatch {xtor; expected; actual} ->
              Printf.sprintf "Arity mismatch for %s: expected %d, got %d"
                (Path.name xtor.name) expected actual
          | MTm.UnificationFailed (t1, t2) ->
              Printf.sprintf "Unification failed: %s vs %s"
                (MPrint.typ_to_string t1) (MPrint.typ_to_string t2)));
  
  print_endline "Done!"
