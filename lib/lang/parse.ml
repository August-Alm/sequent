(** Main parsing interface *)

(* Parse an expression from a string *)
let parse_expr_string s =
  let lexbuf = Lexer.from_string s in
  let provider = Lexer.provider lexbuf in
  try
    MenhirLib.Convert.Simplified.traditional2revised Parser.main_expr provider
  with
  | Parser.Error ->
      let (pos, _) = Sedlexing.lexing_positions lexbuf in
      failwith (Printf.sprintf "Parse error at line %d, column %d"
                  pos.Lexing.pos_lnum
                  (pos.Lexing.pos_cnum - pos.Lexing.pos_bol))

(* Parse a type from a string *)
let parse_typ_string s =
  let lexbuf = Lexer.from_string s in
  let provider = Lexer.provider lexbuf in
  try
    MenhirLib.Convert.Simplified.traditional2revised Parser.main_typ provider
  with
  | Parser.Error ->
      let (pos, _) = Sedlexing.lexing_positions lexbuf in
      failwith (Printf.sprintf "Parse error at line %d, column %d"
                  pos.Lexing.pos_lnum
                  (pos.Lexing.pos_cnum - pos.Lexing.pos_bol))

(* Parse an expression from a channel *)
let parse_expr_channel ch =
  let lexbuf = Lexer.from_channel ch in
  let provider = Lexer.provider lexbuf in
  try
    MenhirLib.Convert.Simplified.traditional2revised Parser.main_expr provider
  with
  | Parser.Error ->
      let (pos, _) = Sedlexing.lexing_positions lexbuf in
      failwith (Printf.sprintf "Parse error at line %d, column %d"
                  pos.Lexing.pos_lnum
                  (pos.Lexing.pos_cnum - pos.Lexing.pos_bol))

(* Parse a type from a channel *)
let parse_typ_channel ch =
  let lexbuf = Lexer.from_channel ch in
  let provider = Lexer.provider lexbuf in
  try
    MenhirLib.Convert.Simplified.traditional2revised Parser.main_typ provider
  with
  | Parser.Error ->
      let (pos, _) = Sedlexing.lexing_positions lexbuf in
      failwith (Printf.sprintf "Parse error at line %d, column %d"
                  pos.Lexing.pos_lnum
                  (pos.Lexing.pos_cnum - pos.Lexing.pos_bol))

(* Parse top-level definitions from a string *)
let parse_defs_string s =
  let lexbuf = Lexer.from_string s in
  let provider = Lexer.provider lexbuf in
  try
    MenhirLib.Convert.Simplified.traditional2revised Parser.main_defs provider
  with
  | Parser.Error ->
      let (pos, _) = Sedlexing.lexing_positions lexbuf in
      failwith (Printf.sprintf "Parse error at line %d, column %d"
                  pos.Lexing.pos_lnum
                  (pos.Lexing.pos_cnum - pos.Lexing.pos_bol))

(* Parse top-level definitions from a channel *)
let parse_defs_channel ch =
  let lexbuf = Lexer.from_channel ch in
  let provider = Lexer.provider lexbuf in
  try
    MenhirLib.Convert.Simplified.traditional2revised Parser.main_defs provider
  with
  | Parser.Error ->
      let (pos, _) = Sedlexing.lexing_positions lexbuf in
      failwith (Printf.sprintf "Parse error at line %d, column %d"
                  pos.Lexing.pos_lnum
                  (pos.Lexing.pos_cnum - pos.Lexing.pos_bol))
