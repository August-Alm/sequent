(**
  module: Pipeline
  description: Main compilation pipeline for the Melcore language.
*)

let ( let* ) = Result.bind

module LangStage = struct

  module MTypes = Melcore.Types.MelcoreTypes
  module MTerms = Melcore.Terms

  let parse_string (input: string)
      : (Lang.Syntax.ast_defs, string) result =
    try Ok (Lang.Parse.parse_defs_string input)
    with e ->  Error (Printf.sprintf "Parse error: %s" (Printexc.to_string e))

  let desugar (ast: Lang.Syntax.ast_defs)
      : ((MTypes.dec list * MTerms.definitions), string) result =
    try
      let desugared = Desugar.desugar ast in
      Ok (desugared.type_defs, desugared.term_defs)
    with e ->
      Error (Printf.sprintf "Desugar error: %s" (Printexc.to_string e))

  let to_melcore (input: string) =
    let* ast = parse_string input in
    let* desugared = desugar ast in
    Ok desugared

end

module MelcoreStage = struct

  open Common.Identifiers
  module MTypes = Melcore.Types.MelcoreTypes
  module MTerms = Melcore.Terms
  module CTypes = Core.Types.CoreTypes
  module CTerms = Core.Terms

  let type_check (decs: MTypes.dec list) (defs: MTerms.definitions)
      : ((MTypes.dec list * MTerms.typed_definitions), string) result =
    let ctx = MTerms.make_tc_context decs defs in
    Path.to_list defs
    |> List.fold_left (fun acc (path, def) ->
      match acc with
        Error _ -> acc  (* Short-circuit on first error *)
      | Ok acc_defs ->
        (match MTerms.check_definition ctx def with
            Ok tdef -> Ok ((path, tdef) :: acc_defs)
        | Error e ->
            let msg = "Type error in " ^ Path.name path ^ ":\n" ^
            (Melcore.Printing.check_error_to_string e) in
            Error msg)
    ) (Ok [])
    (* Reverse to maintain original order *)
    |> function
      | Ok lst -> Ok (decs, Path.of_list (List.rev lst))
      | Error msg -> Error msg
    
  let normalize (defs: MTerms.typed_definitions)
      : MTerms.typed_definitions =
    Path.to_list defs
    |> List.map (fun (p, def) -> (p, MTerms.normalize_def def))
    |> Path.of_list
  
  let encode (decs: MTypes.dec list) (defs: MTerms.typed_definitions)
      : (CTypes.dec list * CTerms.definition Path.tbl, string) result =
    let ctx = Encode.make_encode_ctx ~defs decs in 
    try
      defs
      |> Path.map_tbl (Encode.encode_term_def ctx)
      |> (fun encs -> Ok (List.map snd (Path.to_list ctx.types.decs), encs))
    with e ->
      Error (Printf.sprintf "Encoding error: %s" (Printexc.to_string e))

end
    
module CoreStage = struct

  open Common.Identifiers
  module CTypes = Core.Types.CoreTypes
  module CTerms = Core.Terms
  module Mono = Core.Monomorphize
  module FTypes = Focused.Types.FocusedTypes
  module FTerms = Focused.Terms
  module FReturn = Focused.Return

  let type_check (decs: CTypes.dec Path.tbl) (defs: CTerms.definition Path.tbl)
      : (CTerms.definition Path.tbl, string) result =
    let ctx = CTerms.make_tc_context decs defs in
    Path.to_list defs
    |> List.fold_left (fun acc (path, def) ->
      match acc with
        Error _ -> acc  (* Short-circuit on first error *)
      | Ok acc_defs ->
        (match CTerms.check_def ctx def with
            Ok tdef -> Ok ((path, tdef) :: acc_defs)
        | Error e ->
            let msg = "Type error in " ^ Path.name path ^ ":\n" ^
            (Core.Printing.check_error_to_string e) in
            Error msg)
    ) (Ok [])
    (* Reverse to maintain original order *)
    |> function
        Error msg -> Error msg
      | Ok lst -> Ok (Path.of_list (List.rev lst))

  let monomorphize (defs: CTerms.definition Path.tbl)
      : (Mono.mono_result, string) result =
    match List.find_opt (fun (p, _) ->
      Path.name p = "main"
    ) (Path.to_list defs)
    with
      None -> Error "Monomorphization error: no main function found"
    | Some (_, main) ->
      let defs = Path.filter (fun p _ -> Path.name p <> "main") defs in 
      match Mono.monomorphize { main = main; defs = defs } with
        Error e -> Error ("Monomorphization error:" ^ Core.Printing.mono_error_to_string e)
      | Ok mono_defs -> Ok mono_defs
  
  let focus (decs: CTypes.dec Path.tbl) (mono_defs: Mono.mono_result)
      : (FTypes.dec Path.tbl * FTerms.definition * FTerms.definition Path.tbl, string) result =
    try
      let decs_with_new =
        List.fold_left (fun acc (dec: CTypes.dec) ->
          Path.add dec.name dec acc
        ) decs mono_defs.new_declarations
      in
      let focused_decs = Focus.focus_decs decs_with_new in
      let focused_main = Focus.focus_def decs_with_new mono_defs.main in
      (* Close main's return continuation - main's term_params should have the 
         return continuation as the last parameter. Replace references to it with Ret. *)
      let closed_main = 
        match List.rev focused_main.term_params with
        | (ret_k, Focused.Types.FocusedBase.Cns ret_ty) :: _ ->
            (* Use close_ret_var to close over the specific return continuation variable *)
            let closed_body = FReturn.close_ret_var ret_ty ret_k focused_main.body in
            { focused_main with body = closed_body }
        | _ -> focused_main
      in
      let focused_defs =
        List.fold_left (fun acc (def: CTerms.definition) ->
          let focused_def = Focus.focus_def decs_with_new def in
          Path.add focused_def.path focused_def acc
        ) Path.emptytbl mono_defs.definitions in
      Ok (focused_decs, closed_main, focused_defs)
    with e ->
      Error (Printf.sprintf "Focusing error: %s" (Printexc.to_string e))
end


module FocusedStage = struct

  open Common.Identifiers
  module FTypes = Focused.Types.FocusedTypes
  module FTerms = Focused.Terms
  module FMachine = Focused.Semantics

  let type_check (decs: FTypes.dec Path.tbl) (defs: FTerms.definition Path.tbl)
      : (FTerms.definition Path.tbl, string) result =
    let ctx = FTerms.make_tc_context decs defs in
    Path.to_list defs
    |> List.fold_left (fun acc (path, def) ->
      match acc with
        Error _ -> acc  (* Short-circuit on first error *)
      | Ok acc_defs ->
        (match FTerms.check_def ctx def with
            Ok tdef -> Ok ((path, tdef) :: acc_defs)
        | Error e ->
            let msg = "Type error in " ^ Path.name path ^ ":\n" ^
            (Focused.Printing.check_error_to_string e) in
            Error msg)
    ) (Ok [])
    (* Reverse to maintain original order *)
    |> function
      | Ok lst -> Ok (Path.of_list (List.rev lst))
      | Error msg -> Error msg

  (** Returns the final command, environment, and step count *)
  let eval ?(trace=false) (main: FTerms.definition) (defs: FTerms.definition Path.tbl)
      : (FTerms.command * FMachine.env * int, string) result =
    try
      let env = { FMachine.empty_env with defs = defs } in
      let ((cmd, env), steps) = FMachine.run ~trace (main.body, env) in
      Ok (cmd, env, steps)
    with e ->
      Error (Printf.sprintf "Evaluation error: %s" (Printexc.to_string e))

end