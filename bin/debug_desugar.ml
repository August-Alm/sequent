let rec describe_ast (ast: Lang.Syntax.ast) : string =
  match ast with
  | Lang.Syntax.AST_Int n -> Printf.sprintf "Int(%d)" n
  | Lang.Syntax.AST_Add (a, b) -> Printf.sprintf "Add(%s, %s)" (describe_ast a) (describe_ast b)
  | Lang.Syntax.AST_Var x -> Printf.sprintf "Var(%s)" x
  | Lang.Syntax.AST_App (f, a) -> Printf.sprintf "App(%s, %s)" (describe_ast f) (describe_ast a)
  | Lang.Syntax.AST_Ins (t, _) -> Printf.sprintf "Ins(%s, _)" (describe_ast t)
  | Lang.Syntax.AST_Lam (ty_args, tm_args, body) ->
      Printf.sprintf "Lam(ty_args=%d, tm_args=%d, %s)" 
        (List.length ty_args) (List.length tm_args) (describe_ast body)
  | Lang.Syntax.AST_Let (x, t, u) -> Printf.sprintf "Let(%s, %s, %s)" x (describe_ast t) (describe_ast u)
  | Lang.Syntax.AST_Match (t, _) -> Printf.sprintf "Match(%s, ...)" (describe_ast t)
  | Lang.Syntax.AST_New (_, _) -> "New(...)"
  | Lang.Syntax.AST_Xtor (name, _, _) -> Printf.sprintf "Xtor(%s, ...)" name

let () =
  let src = "fun (x: int)(y: int) => x + y" in
  Printf.printf "Input: %s\n" src;
  
  let expr = Lang.Parse.parse_expr_string src in
  Printf.printf "Structure: %s\n" (describe_ast expr);
  
  let empty_defs = { Lang.Syntax.type_defs = []; term_defs = [] } in
  try
    let term = Sequent.Desugar.desugar_term empty_defs expr in
    Printf.printf "Desugared: %s\n" (Melcore.Printing.term_to_string term)
  with e ->
    Printf.printf "Error: %s\n" (Printexc.to_string e)
