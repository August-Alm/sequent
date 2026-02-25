(**
  module: Pipeline
  description: Main compilation pipeline for the Melcore language.
*)

let ( let* ) = Result.bind

module Lang = struct

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

module Melcore = struct

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
    let ctx = Encode.make_encode_ctx decs in 
    try
      Path.to_list defs
      |> List.map (fun (p, def) -> (p, Encode.encode_term_def ctx def))
      |> Path.of_list
      |> (fun encs -> Ok (List.map snd (Path.to_list ctx.types.decs), encs))
    with e ->
      Error (Printf.sprintf "Encoding error: %s" (Printexc.to_string e))

end
    
module Core = struct

  open Common.Identifiers
  module CTypes = Core.Types.CoreTypes
  module CTerms = Core.Terms
  module Mono = Core.Monomorphize
  module FTypes = Focused.Types.FocusedTypes
  module FTerms = Focused.Terms

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
      | Ok lst -> Ok (Path.of_list (List.rev lst))
      | Error msg -> Error msg

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
        Ok mono_defs -> Ok mono_defs
      | Error e -> Error ("Monomorphization error:" ^ Core.Printing.mono_error_to_string e)
end