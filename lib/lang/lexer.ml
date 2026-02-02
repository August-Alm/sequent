(** Sedlex-based lexer for the surface language *)

open Parser

(* Unicode-aware sedlex lexer *)
let whitespace = [%sedlex.regexp? Plus (' ' | '\t' | '\r' | '\n')]
let digit = [%sedlex.regexp? '0'..'9']
let letter = [%sedlex.regexp? 'a'..'z' | 'A'..'Z']
let ident_char = [%sedlex.regexp? letter | digit | '_']
let ident_start = [%sedlex.regexp? letter | '_']
let identifier = [%sedlex.regexp? ident_start, Star ident_char]
let integer = [%sedlex.regexp? Plus digit]

(* Keywords *)
let keywords = [
  ("fun", KW_FUN);
  ("let", KW_LET);
  ("in", KW_IN);
  ("match", KW_MATCH);
  ("with", KW_WITH);
  ("new", KW_NEW);
  ("data", KW_DATA);
  ("code", KW_CODE);
  ("where", KW_WHERE);
  ("end", KW_END);
  ("type", KW_TYPE);
]

let keyword_table =
  let tbl = Hashtbl.create (List.length keywords) in
  List.iter (fun (k, v) -> Hashtbl.add tbl k v) keywords;
  tbl

(* Main lexer function *)
let rec token lexbuf =
  match%sedlex lexbuf with
  | whitespace -> token lexbuf
  | "(*" -> comment lexbuf; token lexbuf
  | "---" -> line_comment lexbuf; token lexbuf
  | "->" -> ARROW
  | "=>" -> DBLARROW
  | "(" -> LPAREN
  | ")" -> RPAREN
  | "{" -> LBRACE
  | "}" -> RBRACE
  | "[" -> LBRACK
  | "]" -> RBRACK
  | ":" -> COLON
  | "=" -> EQUAL
  | "+" -> PLUS
  | "*" -> STAR
  | "|" -> PIPE
  | ";" -> SEMICOLON
  | integer ->
      let s = Sedlexing.Utf8.lexeme lexbuf in
      INT (int_of_string s)
  | identifier ->
      let s = Sedlexing.Utf8.lexeme lexbuf in
      (try Hashtbl.find keyword_table s
       with Not_found -> IDENT s)
  | eof -> EOF
  | _ ->
      let (pos, _) = Sedlexing.lexing_positions lexbuf in
      let tok = Sedlexing.Utf8.lexeme lexbuf in
      failwith (Printf.sprintf "Unexpected character '%s' at line %d, column %d"
                  tok
                  pos.Lexing.pos_lnum
                  (pos.Lexing.pos_cnum - pos.Lexing.pos_bol))

(* Handle nested comments *)
and comment lexbuf =
  match%sedlex lexbuf with
  | "(*" -> comment lexbuf; comment lexbuf
  | "*)" -> ()
  | eof -> failwith "Unterminated comment"
  | any -> comment lexbuf
  | _ -> failwith "Unexpected in comment"

(* Handle line comments *)
and line_comment lexbuf =
  match%sedlex lexbuf with
  | '\n' -> ()
  | eof -> ()
  | any -> line_comment lexbuf
  | _ -> ()

(* Create a lexer from a string *)
let from_string s =
  Sedlexing.Utf8.from_string s

(* Create a lexer from a channel *)
let from_channel ch =
  Sedlexing.Utf8.from_channel ch

(* Token stream for parser *)
let provider lexbuf () =
  let tok = token lexbuf in
  let (start_pos, end_pos) = Sedlexing.lexing_positions lexbuf in
  (tok, start_pos, end_pos)
