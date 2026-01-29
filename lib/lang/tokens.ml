(** Token types for the lexer *)

type token =
  (* Keywords *)
  | KW_FUN
  | KW_LET
  | KW_IN
  | KW_MATCH
  | KW_WITH
  | KW_NEW
  | KW_DATA
  | KW_CODE
  | KW_WHERE
  | KW_END
  | KW_TYPE
  (* Delimiters *)
  | LPAREN
  | RPAREN
  | LBRACE
  | RBRACE
  | LBRACK
  | RBRACK
  
  (* Operators *)
  | ARROW        (* -> *)
  | DBLARROW     (* => *)
  | COLON
  | SEMICOLON
  | EQUAL
  | STAR
  | PIPE
  
  (* Identifiers *)
  | IDENT of string
  | INT of int
  
  (* Special *)
  | EOF

let string_of_token = function
  | KW_FUN -> "fun"
  | KW_LET -> "let"
  | KW_IN -> "in"
  | KW_MATCH -> "match"
  | KW_WITH -> "with"
  | KW_NEW -> "new"
  | KW_DATA -> "data"
  | KW_CODE -> "code"
  | KW_WHERE -> "where"
  | KW_END -> "end"
  | KW_TYPE -> "type"
  | LPAREN -> "("
  | RPAREN -> ")"
  | LBRACE -> "{"
  | RBRACE -> "}"
  | LBRACK -> "["
  | RBRACK -> "]"
  | ARROW -> "->"
  | DBLARROW -> "=>"
  | COLON -> ":"
  | EQUAL -> "="
  | STAR -> "*"
  | PIPE -> "|"
  | SEMICOLON -> ";"
  | IDENT s -> "ident(" ^ s ^ ")"
  | INT n -> "int(" ^ string_of_int n ^ ")"
  | EOF -> "EOF"
