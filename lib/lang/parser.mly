%{
  open Syntax
%}

(* Token declarations *)
%token KW_FUN KW_LET KW_IN KW_MATCH KW_WITH KW_NEW KW_DATA KW_CODE KW_WHERE KW_END KW_TYPE
%token LPAREN RPAREN LBRACE RBRACE LBRACK RBRACK
%token ARROW DBLARROW COLON SEMICOLON EQUAL STAR PIPE PLUS
%token <string> IDENT
%token <int> INT
%token EOF

(* Precedence and associativity *)
%left PLUS
%right ARROW
%nonassoc KW_IN
%nonassoc KW_WITH
%nonassoc KW_END
%nonassoc KW_TYPE
%nonassoc DBLARROW
(* Start symbol *)
%start <Syntax.ast> main_expr
%start <Syntax.ast_typ> main_typ
%start <Syntax.ast_defs> main_defs

%%

main_expr:
  | e = expr EOF { e }

main_typ:
  | t = typ EOF { t }

main_defs:
  | defs = definitions EOF { defs }

(* ===== KINDS ===== *)

kind:
  | KW_TYPE { AST_KStar }
  | k1 = kind_atom ARROW k2 = kind { AST_KArrow (k1, k2) }

kind_atom:
  | KW_TYPE { AST_KStar }
  | LPAREN k = kind RPAREN { k }

(* ===== TYPES ===== *)

typ:
  | t1 = typ_app ARROW t2 = typ { AST_TyFun (t1, t2) }
  | LBRACE x = IDENT RBRACE t = typ { AST_TyAll ((x, None), t) }
  | LBRACE x = IDENT COLON k = kind RBRACE t = typ { AST_TyAll ((x, Some k), t) }
  | t = typ_app { t }

typ_app:
  | t = typ_atom { t }
  | t = typ_app LPAREN arg = typ RPAREN
    { AST_TyApp (t, [arg]) }

typ_atom:
  | x = IDENT { AST_TyVar x }
  | LPAREN t = typ RPAREN { t }

(* ===== TERMS ===== *)

expr:
  | e = expr_app { e }
  | KW_FUN ty_args = type_args tm_args = term_args DBLARROW body = expr
    { AST_Lam (ty_args, tm_args, body) }
  | KW_LET x = IDENT EQUAL t = expr KW_IN u = expr
    { AST_Let (x, t, u) }
  | t1 = expr PLUS t2 = expr
    { AST_Add (t1, t2) }
  | KW_MATCH t = expr KW_WITH LBRACE clauses = separated_list(SEMICOLON, clause) RBRACE
    { AST_Match (t, clauses) }
  | KW_NEW LBRACE clauses = separated_list(SEMICOLON, clause) RBRACE
    { AST_New (None, clauses) }
  | KW_NEW ty = typ LBRACE clauses = separated_list(SEMICOLON, clause) RBRACE
    { AST_New (Some ty, clauses) }

expr_app:
  | e = expr_atom { e }
  (* Function application: f(x) *)
  | f = expr_app LPAREN arg = expr RPAREN
    { AST_App (f, arg) }
  (* Type application: f{T} *)
  | f = expr_app LBRACE ty = typ RBRACE
    { AST_Ins (f, ty) }
  (* Constructor/destructor with type args: Xtor{T1}{T2}(x)(y) *)
  | x = IDENT ty_args = type_applications term_args = term_applications
    { 
      if ty_args = [] && term_args = [] then
        AST_Var x
      else
        AST_Xtor (x, ty_args, term_args)
    }

expr_atom:
  | n = INT { AST_Int n }
  | x = IDENT { AST_Var x }
  | LPAREN e = expr RPAREN { e }

(* Type arguments: {T1}{T2}... *)
type_applications:
  | { [] }
  | LBRACE t = typ RBRACE rest = type_applications { t :: rest }

(* Term arguments: (x)(y)... *)
term_applications:
  | { [] }
  | LPAREN e = expr RPAREN rest = term_applications { e :: rest }

(* Type parameters for lambdas *)
type_args:
  | { [] }
  | LBRACE param = type_param RBRACE rest = type_args { param :: rest }

type_param:
  | x = IDENT { (x, None) }
  | x = IDENT COLON k = kind { (x, Some k) }

(* Term parameters for lambdas *)
term_args:
  | { [] }
  | params = term_args_group rest = term_args { params @ rest }

term_args_group:
  | x = IDENT { [(x, None)] }
  | LPAREN x = IDENT COLON t = typ RPAREN { [(x, Some t)] }

(* Pattern matching clauses *)
clause:
  | xtor = IDENT ty_binders = type_binders tm_binders = term_binders DBLARROW body = expr
    { (xtor, ty_binders, tm_binders, body) }

type_binders:
  | { [] }
  | LBRACE x = IDENT RBRACE rest = type_binders { x :: rest }

term_binders:
  | { [] }
  | LPAREN x = IDENT RPAREN rest = term_binders { x :: rest }

(* ===== TOP-LEVEL DEFINITIONS ===== *)

definitions:
  | { { type_defs = []; term_defs = [] } }
  | def = definition rest = definitions
    { match def with
      | `Type td -> { rest with type_defs = td :: rest.type_defs }
      | `Term tm -> { rest with term_defs = tm :: rest.term_defs }
    }

definition:
  | td = type_def { `Type td }
  | tm = term_def { `Term tm }

(* Type definitions *)
type_def:
  (* type t = ty *)
  | KW_TYPE name = IDENT EQUAL ty = typ
    { AST_TyAlias (name, ty) }
  (* data t: k where { xtor1; ...; xtorN } *)
  | KW_DATA name = IDENT COLON k = kind KW_WHERE LBRACE xtors = separated_list(SEMICOLON, xtor_decl) RBRACE
    { AST_TyData { name = name; kind = k; clauses = xtors } }
  (* code t: k where { xtor1; ...; xtorN } *)
  | KW_CODE name = IDENT COLON k = kind KW_WHERE LBRACE xtors = separated_list(SEMICOLON, xtor_decl) RBRACE
    { AST_TyCode { name = name; kind = k; clauses = xtors } }

(* Constructor/destructor declaration: xtor: {a0: k0} ... {aM: kM} t0 -> .. -> tN *)
xtor_decl:
  | name = IDENT COLON ty_args = xtor_type_args ret = xtor_return_type
    { { name = name; type_args = ty_args; term_args = ret } }

xtor_type_args:
  | { [] }
  | LBRACE x = IDENT COLON k = kind RBRACE rest = xtor_type_args { (x, Some k) :: rest }
  | LBRACE x = IDENT RBRACE rest = xtor_type_args { (x, None) :: rest }

xtor_return_type:
  | t = typ_app { [t] }
  | t = typ_app ARROW rest = xtor_return_type { t :: rest }

(* Term definitions: let f {a0: k0} ... {aM: kM} (x0: t0) ... (xN: tN) : ty = t *)
term_def:
  | KW_LET name = IDENT ty_args = type_args tm_args = term_def_args COLON ret = typ EQUAL body = expr
    { { name = name; type_args = ty_args; term_args = tm_args; return_type = ret; body = body } }

term_def_args:
  | { [] }
  | LPAREN x = IDENT COLON t = typ RPAREN rest = term_def_args { (x, t) :: rest }

%%
