open Common.Identifiers
module P = Path
module I = Ident

let input = "
  data nat: type where
    { zero: nat
    ; succ: nat -> nat
    }
  
  let double_succ (n: nat): nat =
    let m = succ(n) in
    succ(m)
"

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
  let ast = Lang.Parse.parse_defs_string input in
  let defs = Lang.Syntax.to_definitions ast in
  let typed = Lang.Terms.check_all defs in
  let kore_env = build_kore_env typed in
  print_endline "Kore:";
  List.iter (fun (path, def) ->
    print_endline (Printf.sprintf "  %s:" (P.name path));
    print_endline (Printf.sprintf "    %s" 
      (Kore.Printing.pp_definition ~show_types:true def))
  ) (P.to_list kore_env.Kore.Terms.Env.terms);
  Kore.Terms.check_definitions
    kore_env.Kore.Terms.Env.imports
    kore_env.Kore.Terms.Env.signatures
    kore_env.Kore.Terms.Env.terms;
  print_endline "Kore typechecked!";
  let cut = Sequent.Focus.map_env kore_env in
  print_endline "Cut:";
  print_endline (Cut.Printing.pp_program ~show_types:true cut.program)
