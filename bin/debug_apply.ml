(** Debug file for tracing function application polarization *)

open Common.Identifiers
module P = Path
module I = Ident

let parse_lang (input: string) : Lang.Syntax.ast_defs =
  Lang.Parse.parse_defs_string input

let to_definitions (ast: Lang.Syntax.ast_defs) : Lang.Terms.definitions =
  Lang.Syntax.to_definitions ast

let typecheck_lang (defs: Lang.Terms.definitions) : Lang.Terms.typed_definitions =
  Lang.Terms.check_all defs

let polarize_signatures (defs: Lang.Terms.typed_definitions) : Kore.Types.signatures =
  Sequent.Polarize.signatures defs

let polarize_term_def
    (sgns: Kore.Types.signatures)
    (def: Lang.Terms.typed_term_def)
    : Kore.Terms.definition =
  let body_term = Sequent.Polarize.map_term sgns def.Lang.Terms.body in
  let ret_ty = Sequent.Polarize.map_type def.Lang.Terms.return_type in
  let type_params = List.map (fun (v, k) ->
    (v, Sequent.Polarize.map_kinds k)
  ) def.Lang.Terms.type_args in
  (* All parameters are producers (Lhs) in Kore - chirality flip is in Cut *)
  let term_params = List.map (fun (v, ty) ->
    (v, Kore.Types.Lhs (Sequent.Polarize.map_type ty))
  ) def.Lang.Terms.term_args in
  let k = I.fresh () in
  let body_cmd = Kore.Terms.CutPos (ret_ty, body_term, Kore.Terms.Variable k) in
  { Kore.Terms.name = def.Lang.Terms.name
  ; type_params = type_params
  ; term_params = term_params @ [(k, Kore.Types.Rhs ret_ty)]
  ; body = body_cmd
  }

let build_kore_env (defs: Lang.Terms.typed_definitions) : Kore.Terms.Env.t =
  let sgns = polarize_signatures defs in
  let env = { Kore.Terms.Env.empty with signatures = sgns } in
  List.fold_left (fun env (_, def) ->
    let kore_def = polarize_term_def sgns def in
    Kore.Terms.Env.add_definition env kore_def
  ) env defs.Lang.Terms.term_defs

let () =
  let input = "let apply{a}{b}(f: a -> b)(x: a): b = f(x)" in
  print_endline "Input:";
  print_endline input;
  print_endline "";
  
  print_endline "1. Parsing...";
  let ast = parse_lang input in
  print_endline "   OK";
  
  print_endline "2. Converting...";
  let defs = to_definitions ast in
  print_endline "   OK";
  
  print_endline "3. Type-checking Lang...";
  let typed = typecheck_lang defs in
  print_endline "   OK";
  
  print_endline "4. Building Kore env...";
  let kore_env = build_kore_env typed in
  print_endline "   OK";
  
  print_endline "";
  print_endline "Kore output:";
  List.iter (fun (path, def) ->
    print_endline (Printf.sprintf "  %s:" (P.name path));
    print_endline (Printf.sprintf "    %s" 
      (Kore.Printing.pp_definition ~show_types:true def))
  ) (P.to_list kore_env.Kore.Terms.Env.terms);
  
  print_endline "";
  print_endline "5. Type-checking Kore...";
  
  (* Debug: print the signatures *)
  print_endline "Signatures in env:";
  List.iter (fun (path, (sgn, pol, _k)) ->
    let pol_str = match pol with Kore.Types.Positive -> "+" | Kore.Types.Negative -> "-" in
    print_endline (Printf.sprintf "  %s (%s):" (P.name path) pol_str);
    List.iter (fun (xtor : Kore.Types.xtor) ->
      print_endline (Printf.sprintf "    xtor: %s (parent: %s)" 
        (P.name xtor.Kore.Types.name) (P.name xtor.Kore.Types.parent))
    ) sgn.Kore.Types.xtors
  ) (P.to_list kore_env.Kore.Terms.Env.signatures);
  
  print_endline "";
  print_endline "Path equality test for neg.ret:";
  let neg_sgn, _, _ = Kore.Types.get_def kore_env.Kore.Terms.Env.signatures Kore.Builtins.Sym.neg_t in
  List.iter (fun (xtor : Kore.Types.xtor) ->
    let eq = P.equal xtor.Kore.Types.name Kore.Builtins.Sym.neg_ret in
    print_endline (Printf.sprintf "  %s == Sym.neg_ret: %b" (P.name xtor.Kore.Types.name) eq)
  ) neg_sgn.Kore.Types.xtors;
  
  (try 
    Kore.Terms.check_definitions
      kore_env.Kore.Terms.Env.imports
      kore_env.Kore.Terms.Env.signatures
      kore_env.Kore.Terms.Env.terms;
    print_endline "   OK"
  with e ->
    print_endline ("   FAILED: " ^ Kore.Printing.pp_type_check_exn e))
