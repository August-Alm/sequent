(**
  Module: Lang.Syntax
  Description: Abstract syntax of surface language.
  
  This module defines the abstract syntax of the surface language.
*)

type ast_kind = AST_KStar | AST_KArrow of ast_kind * ast_kind

type ast_typ =
    AST_TyVar of string
  | AST_TyApp of ast_typ * (ast_typ list)
  | AST_TyFun of ast_typ * ast_typ
  | AST_TyAll of (string * ast_kind option) * ast_typ

type ast =
  (* n *)
  | AST_Int of int
  (* t + u *)
  | AST_Add of ast * ast
  (* x *)
  | AST_Var of string
  (* t(u) *)
  | AST_App of ast * ast
  (* t{ty} *)
  | AST_Ins of ast * ast_typ
  (* (fun {a: k} x (y: a) => t)  *)
  | AST_Lam of type_args * term_args * ast
  (*
    forall {a: k} t or forall {a} t
  | AST_All of type_args * ast_typ
  *)
  (* let x = t in u *)
  | AST_Let of string * ast * ast
  (* match t with clauses *)
  | AST_Match of ast * (ast_clause list)
  (* new { clauses } *)
  | AST_New of (ast_typ option) * (ast_clause list)
  (* xtor{ai's}(ti's); type and term arguments *)
  | AST_Xtor of string * (ast_typ list) * (ast list)

and type_args = (string * (ast_kind option)) list
and term_args = (string * (ast_typ option)) list

and ast_clause =
  (* xtor{ai's}(xi's) => t; type binders and term binders (as identifiers), and body *)
  string * (string list) * (string list) * ast

(* xtor: {a0: k0} ... {aM: kM} t0 -> .. -> tN *)
type ast_xtor =
  { name: string
  ; type_args: (string * ast_kind option) list
  ; term_args: ast_typ list
  }

type ast_type_dec =
  { name: string
  ; kind: ast_kind
  ; clauses: ast_xtor list
  }

(*
  top-level type definition:
  alias:
    type t = ty
  data type:
    data t: k where { xtor1; ...; xtorN }
  code type:
    code t: k where { xtor1; ...; xtorN }
*)
type ast_type_def =
  | AST_TyAlias of string * ast_typ
  | AST_TyData of ast_type_dec
  | AST_TyCode of ast_type_dec

(*
top-level term:
  let f {a0: k0} ... {aM: kM} (x0: t0) ... (xN: tN) : ty = t
argument types and return type are mandatory
*)
type ast_term_def =
  { name: string
  ; type_args: type_args
  ; term_args: (string * ast_typ) list
  ; return_type: ast_typ
  ; body: ast
  }

(*
  type t = ...
  
  let f {a0: k0} ... {aM: kM} (x0: t0) ... (xN: tN) : ty = t

  data td = ...

  let g {b0: k0} ... {bP: kP} (y0: s0) ... (yQ: sQ) : sy = u

  ...
*)
type ast_defs =
  { type_defs: ast_type_def list
  ; term_defs: ast_term_def list
  }

(* ===== TO_STRING FUNCTIONS ===== *)

let ident n = "\n" ^ String.make (2 * n) ' '

(* Convert kind to string *)
let rec kind_to_string = function
  | AST_KStar -> "type"
  | AST_KArrow (k1, k2) ->
    let k1_str =
      match k1 with
      | AST_KStar -> kind_to_string k1
      | AST_KArrow _ -> "(" ^ kind_to_string k1 ^ ")"
    in
    k1_str ^ " -> " ^ kind_to_string k2

(* Convert type to string *)
let rec typ_to_string = function
  | AST_TyVar x -> x
  | AST_TyApp (t, args) ->
    let t_str = typ_app_base_to_string t in
    let args_str = List.map (fun arg -> "(" ^ typ_to_string arg ^ ")") args in
    t_str ^ String.concat "" args_str
  | AST_TyFun (t1, t2) ->
    let t1_str = match t1 with
      | AST_TyFun _ -> "(" ^ typ_to_string t1 ^ ")"
      | _ -> typ_to_string t1
    in
    t1_str ^ " -> " ^ typ_to_string t2
  | AST_TyAll ((x, k_opt), t) ->
    let k_str = match k_opt with
      | None -> ""
      | Some k -> ": " ^ kind_to_string k
    in
    "{" ^ x ^ k_str ^ "} " ^ typ_to_string t

and typ_app_base_to_string = function
  | AST_TyVar x -> x
  | AST_TyApp _ as t -> typ_to_string t
  | t -> "(" ^ typ_to_string t ^ ")"

and typ_atom_to_string = function
  | AST_TyVar x -> x
  | t -> "(" ^ typ_to_string t ^ ")"

(* Convert term to string *)
let rec ast_to_string (lvl: int) = function
  | AST_Int n -> string_of_int n
  | AST_Var x -> x
  | AST_Add (t1, t2) ->
    "(" ^ ast_to_string lvl t1 ^ " + " ^ ast_to_string lvl t2 ^ ")"
  | AST_App (t, u) ->
    ast_app_to_string lvl t ^ "(" ^ ast_to_string lvl u ^ ")"
  | AST_Ins (t, ty) ->
    ast_app_to_string lvl t ^ "{" ^ typ_to_string ty ^ "}"
  | AST_Lam (ty_args, tm_args, body) ->
    let ty_args_str = String.concat "" (List.map type_arg_to_string ty_args) in
    let tm_args_str = String.concat "" (List.map term_arg_to_string tm_args) in
    "fun " ^ ty_args_str ^ tm_args_str ^ " => " ^ ast_to_string lvl body
  | AST_Let (x, t, u) ->
    "let " ^ x ^ " = " ^ ast_to_string lvl t ^ " in" ^
    ident lvl ^ ast_to_string lvl u
  | AST_Match (t, clauses) ->
    let clauses_str =
      clauses
      |> (List.map (clause_to_string (lvl + 2)))
      |> String.concat (ident lvl ^ "; ")
    in
    (if lvl = 1 then "" else ident lvl) ^ "match " ^ ast_to_string lvl t ^ " with" ^
    ident lvl ^ "{ " ^ clauses_str ^
    ident lvl ^ "}"
  | AST_New (ty_opt, clauses) ->
    let ty_str =
      match ty_opt with
      | None -> ""
      | Some ty -> " " ^ typ_atom_to_string ty
    in
    let clauses_str = String.concat "; " (List.map (clause_to_string lvl) clauses) in
    "new" ^ ty_str ^ " { " ^ clauses_str ^ " }"
  | AST_Xtor (name, ty_args, tm_args) ->
    let ty_args_str =
      String.concat "" (List.map (fun ty -> "{" ^ typ_to_string ty ^ "}") ty_args)
    in
    let tm_args_str =
      String.concat "" (List.map (fun tm -> "(" ^ ast_to_string lvl tm ^ ")") tm_args)
    in
    name ^ ty_args_str ^ tm_args_str

and ast_app_to_string (lvl: int) = function
  | AST_Int _ | AST_Var _ | AST_Add _ | AST_App _ | AST_Ins _ | AST_Xtor _ as t -> ast_to_string lvl t
  | t -> "(" ^ ast_to_string lvl t ^ ")"

and type_arg_to_string (x, k_opt) =
  match k_opt with
  | None -> "{" ^ x ^ "}"
  | Some k -> "{" ^ x ^ ": " ^ kind_to_string k ^ "}"

and term_arg_to_string (x, ty_opt) =
  match ty_opt with
  | None -> x
  | Some ty -> "(" ^ x ^ ": " ^ typ_to_string ty ^ ")"

and clause_to_string (lvl: int) (xtor, ty_binders, tm_binders, body) =
  let ty_binders_str = String.concat "" (List.map (fun x -> "{" ^ x ^ "}") ty_binders) in
  let tm_binders_str = String.concat "" (List.map (fun x -> "(" ^ x ^ ")") tm_binders) in
  xtor ^ ty_binders_str ^ tm_binders_str ^ " => " ^ ast_to_string lvl body

(* Convert constructor declaration to string *)
let xtor_to_string (xtor : ast_xtor) =
  let ty_args_str = String.concat " " (List.map (fun (x, k_opt) ->
    match k_opt with
    | None -> "{" ^ x ^ "}"
    | Some k -> "{" ^ x ^ ": " ^ kind_to_string k ^ "}"
  ) xtor.type_args) in
  let tm_args_str = 
    match xtor.term_args with
    | [] -> ""
    | tm_types -> String.concat " -> " (List.map typ_to_string tm_types)
  in
  let args_sep = if ty_args_str = "" || tm_args_str = "" then "" else " " in
  xtor.name ^ ": " ^ ty_args_str ^ args_sep ^ tm_args_str

(* Convert type definition to string *)
let type_def_to_string = function
  | AST_TyAlias (name, ty) ->
    "type " ^ name ^ " = " ^ typ_to_string ty
  | AST_TyData dec ->
    let xtors_str =
      String.concat (ident 1 ^ "; ") (List.map xtor_to_string dec.clauses)
    in
    "data " ^ dec.name ^ ": " ^ kind_to_string dec.kind ^ 
    " where" ^ ident 1 ^ "{ " ^ xtors_str ^ ident 1 ^ "}"
  | AST_TyCode dec ->
    let xtors_str =
      String.concat (ident 1 ^ "; ") (List.map xtor_to_string dec.clauses)
    in
    "code " ^ dec.name ^ ": " ^ kind_to_string dec.kind ^ 
    " where" ^ ident 1 ^ "{ " ^ xtors_str ^ ident 1 ^"}"

(* Convert term definition to string *)
let term_def_to_string def =
  let ty_args_str = String.concat "" (List.map type_arg_to_string def.type_args) in
  let tm_args_str = String.concat "" (List.map (fun (x, ty) ->
    "(" ^ x ^ ": " ^ typ_to_string ty ^ ")") def.term_args)
  in
  "let " ^ def.name ^ ty_args_str ^ tm_args_str ^ 
  ": " ^ typ_to_string def.return_type ^ 
  " =" ^ ident 1 ^ ast_to_string 1 def.body

(* Convert all definitions to string *)
let defs_to_string defs =
  let type_strs = List.map type_def_to_string defs.type_defs in
  let term_strs = List.map term_def_to_string defs.term_defs in
  let all_strs = type_strs @ term_strs in
  String.concat "\n\n" all_strs
