open Common.Identifiers
module P = Path
module I = Ident

let input = "
  let compose{a}{b}{c}(f: b -> c)(g: a -> b)(x: a): c =
    f(g(x))
"

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

let () =
  let ast = Lang.Parse.parse_defs_string input in
  let defs = Lang.Syntax.to_definitions ast in
  let typed = Lang.Terms.check_all defs in
  let kore_env = build_kore_env typed in
  Kore.Terms.check_definitions
    kore_env.Kore.Terms.Env.imports
    kore_env.Kore.Terms.Env.signatures
    kore_env.Kore.Terms.Env.terms;
  print_endline "Kore typechecked!";
  List.iter (fun (path, def) ->
    print_endline (Printf.sprintf "  %s:" (P.name path));
    print_endline (Printf.sprintf "    %s" 
      (Kore.Printing.pp_definition ~show_types:true def))
  ) (P.to_list kore_env.Kore.Terms.Env.terms);
  let cut = Sequent.Focus.map_env kore_env in
  print_endline "Focused!";
  print_endline (Cut.Printing.pp_program ~show_types:true cut.program);
  print_endline "Typechecking Cut...";
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
  try
    Cut.Terms.check_program cut.signatures extern_env cut.program;
    print_endline "Cut typechecked!"
  with e ->
    print_endline ("Cut type error: " ^ Cut.Printing.pp_type_check_exn e);
    raise e
