(**
  Module: Lang.Syntax
  Description: Parsed syntax of surface language.
  
  This module defines the abstract syntax of the surface language.
*)

type ast_kind = AST_KStar | AST_KArrow of ast_kind * ast_kind

type ast_typ =
  | AST_TyVar of string
  | AST_TyApp of ast_typ * (ast_typ list)
  | AST_TyFun of ast_typ * ast_typ
  | AST_TyAll of (string * ast_kind option) * ast_typ

type ast =
  (* n *)
  | AST_Int of int
  (* x *)
  | AST_Var of string
  (* t + u *)
  | AST_Add of ast * ast
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

(* convert kind to string *)
let rec kind_to_string = function
  | AST_KStar -> "type"
  | AST_KArrow (k1, k2) ->
    let k1_str =
      match k1 with
      | AST_KStar -> kind_to_string k1
      | AST_KArrow _ -> "(" ^ kind_to_string k1 ^ ")"
    in
    k1_str ^ " -> " ^ kind_to_string k2

(* convert type to string *)
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

(* convert term to string *)
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

(* convert constructor declaration to string *)
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

(* convert type definition to string *)
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

(* convert term definition to string *)
let term_def_to_string def =
  let ty_args_str = String.concat "" (List.map type_arg_to_string def.type_args) in
  let tm_args_str = String.concat "" (List.map (fun (x, ty) ->
    "(" ^ x ^ ": " ^ typ_to_string ty ^ ")") def.term_args)
  in
  "let " ^ def.name ^ ty_args_str ^ tm_args_str ^ 
  ": " ^ typ_to_string def.return_type ^ 
  " =" ^ ident 1 ^ ast_to_string 1 def.body

(* convert all definitions to string *)
let defs_to_string defs =
  let type_strs = List.map type_def_to_string defs.type_defs in
  let term_strs = List.map term_def_to_string defs.term_defs in
  let all_strs = type_strs @ term_strs in
  String.concat "\n\n" all_strs

(* ===== CONVERSION TO INTERNAL REPRESENTATION ===== *)

open Common.Identifiers
open Types
open Terms
module StringMap = Utility.StringMap

(* context for type and term variables during conversion *)
type conv_ctx =
  { type_vars: Ident.t StringMap.t
  ; term_vars: Ident.t StringMap.t
  ; type_symbols: Path.t StringMap.t  (* map type names to their Path.t *)
  ; term_symbols: Path.t StringMap.t  (* map term names to their Path.t for top-level defs *)
  ; defs: ty_defs
  }

let empty_ctx defs =
  { type_vars = StringMap.empty
  ; term_vars = StringMap.empty
  ; type_symbols = StringMap.empty
  ; term_symbols = StringMap.empty
  ; defs = defs
  }

let add_type_var ctx name id =
  { ctx with type_vars = StringMap.add name id ctx.type_vars }

let add_term_var ctx name id =
  { ctx with term_vars = StringMap.add name id ctx.term_vars }

let add_type_symbol ctx name path =
  { ctx with type_symbols = StringMap.add name path ctx.type_symbols }

let add_term_symbol ctx name path =
  { ctx with term_symbols = StringMap.add name path ctx.term_symbols }

let lookup_type_var ctx name =
  StringMap.find_opt name ctx.type_vars

let lookup_term_var ctx name =
  StringMap.find_opt name ctx.term_vars

let lookup_type_symbol ctx name =
  StringMap.find_opt name ctx.type_symbols

let lookup_term_symbol ctx name =
  StringMap.find_opt name ctx.term_symbols

(* convert kind *)
let rec kind_of_ast = function
  | AST_KStar -> KStar
  | AST_KArrow (k1, k2) -> KArrow (kind_of_ast k1, kind_of_ast k2)

(* convert type *)
let rec typ_of_ast (ctx: conv_ctx) (ty: ast_typ) : typ =
  match ty with
  | AST_TyVar x ->
    (* first check if it's a type symbol *)
    (match lookup_type_symbol ctx x with
    | Some path -> TySym path
    | None ->
      (* otherwise look it up as a type variable *)
      (match lookup_type_var ctx x with
      | Some id -> TyVar id
      | None -> failwith ("unbound type variable: " ^ x)))
  
  | AST_TyApp (t, args) ->
    let t' = typ_of_ast ctx t in
    List.fold_left (fun acc arg -> TyApp (acc, typ_of_ast ctx arg)) t' args
  
  | AST_TyFun (t1, t2) -> TyFun (typ_of_ast ctx t1, typ_of_ast ctx t2)
  
  | AST_TyAll ((x, k_opt), t) ->
    let k = match k_opt with
      | Some k -> kind_of_ast k
      | None -> KStar
    in
    let x_id = Ident.mk x in
    let ctx' = add_type_var ctx x x_id in
    TyAll ((x_id, k), typ_of_ast ctx' t)

(* extract arguments from a type application of the form parent(a1)...(aK) *)
let extract_arguments (parent: Path.t) (ty: typ) : typ list =
  let rec collect acc t =
    match t with
    | TySym p when Path.equal p parent -> List.rev acc
    | TyApp (t', arg) -> collect (arg :: acc) t'
    | _ -> failwith ("Expected type application of " ^ Path.name parent)
  in
  match ty with
  | TySym p when Path.equal p parent -> []  (* just the parent type *)
  | _ -> collect [] ty

(* convert constructor/destructor declaration *)
let xtor_of_ast
    (ctx: conv_ctx) (parent: Path.t) (is_data: bool) (xtor: ast_xtor) : ty_xtor =
  (* process type arguments to build quantified list and context *)
  let quantified, ctx' = 
    List.fold_left (fun (quant_acc, ctx_acc) (x, k_opt) ->
      let k = match k_opt with
        | Some k -> kind_of_ast k
        | None -> KStar
      in
      let x_id = Ident.mk x in
      let ctx_new = add_type_var ctx_acc x x_id in
      ((x_id, k) :: quant_acc, ctx_new)
    ) ([], ctx) xtor.type_args
  in
  let quantified = List.rev quantified in
  
  (* Convert all term argument types *)
  let all_types = List.map (typ_of_ast ctx') xtor.term_args in
  
  (* Split into sources and parent type, extract arguments *)
  let sources, arguments =
    if is_data then
      (* Data constructor: ty1 -> ... -> tyN -> parent(a1)...(aK) *)
      match List.rev all_types with
      | [] -> failwith ("Constructor must have at least a return type")
      | return_ty :: rev_sources ->
          let arguments = extract_arguments parent return_ty in
          (List.rev rev_sources, arguments)
    else
      (* Code destructor: parent(a1)...(aK) -> ty2 -> ... -> tyN *)
      match all_types with
      | [] -> failwith ("Destructor must have at least an input type")
      | input_ty :: rest_sources ->
          let arguments = extract_arguments parent input_ty in
          (rest_sources, arguments)
  in

  { parent = parent
  ; symbol = Path.of_string xtor.name
  ; quantified = quantified
  ; sources = sources
  ; arguments = arguments
  ; constraints = None
  }

(* convert type declaration *)
let ty_dec_of_ast
    (ctx: conv_ctx) (name: string) (kind: ast_kind) (xtors: ast_xtor list) (is_data: bool) : ty_dec =
  let symbol = 
    match lookup_type_symbol ctx name with
    | Some path -> path
    | None -> failwith ("type symbol not found in context: " ^ name)
  in
  let rec args_of_kind k =
    match k with
    | AST_KStar -> []
    | AST_KArrow (k1, k2) -> (None, kind_of_ast k1) :: args_of_kind k2
  in
  let arguments = args_of_kind kind in
  let xtors' = List.map (xtor_of_ast ctx symbol is_data) xtors in
  { symbol = symbol
  ; arguments = arguments
  ; xtors = xtors'
  }

(* build type definitions from ast_defs *)
let build_ty_defs (ast_defs: ast_defs): ty_defs =
  (* first pass: create Path.t for each type and build initial definitions *)
  let type_paths, initial_defs = 
    List.fold_left (fun (paths_acc, defs_acc) tdef ->
      match tdef with
      | AST_TyAlias (name, _ty) ->
        (match name with
        | "int" -> (paths_acc, defs_acc)  (* skip built-in int type *)
        | _ -> failwith ("Unknown type alias: " ^ name))
      
      | AST_TyData dec ->
        let symbol = Path.of_string dec.name in
        let rec args_of_kind k =
          match k with
          | AST_KStar -> []
          | AST_KArrow (k1, k2) -> (None, kind_of_ast k1) :: args_of_kind k2
        in
        let arguments = args_of_kind dec.kind in
        let k = kind_of_ast dec.kind in
        let ty_dec = { symbol = symbol; arguments = arguments; xtors = [] } in
        ((dec.name, symbol) :: paths_acc, (symbol, (Data ty_dec, k)) :: defs_acc)
      
      | AST_TyCode dec ->
        let symbol = Path.of_string dec.name in
        let rec args_of_kind k =
          match k with
          | AST_KStar -> []
          | AST_KArrow (k1, k2) -> (None, kind_of_ast k1) :: args_of_kind k2
        in
        let arguments = args_of_kind dec.kind in
        let k = kind_of_ast dec.kind in
        let ty_dec = { symbol = symbol; arguments = arguments; xtors = [] } in
        ((dec.name, symbol) :: paths_acc, (symbol, (Code ty_dec, k)) :: defs_acc)
    ) ([], []) ast_defs.type_defs
  in
  let initial_defs = List.rev initial_defs in
  
  (* build context with type symbol mappings *)
  let ctx = 
    List.fold_left (fun ctx_acc (name, path) ->
      add_type_symbol ctx_acc name path
    ) (empty_ctx initial_defs) type_paths
  in
  
  (* second pass: fill in constructors with proper context *)
  List.filter_map (fun tdef ->
    match tdef with
    | AST_TyAlias _ -> None
    
    | AST_TyData dec ->
        let ty_dec = ty_dec_of_ast ctx dec.name dec.kind dec.clauses true in
        let k = kind_of_ast dec.kind in
        Some (ty_dec.symbol, (Data ty_dec, k))
    
    | AST_TyCode dec ->
        let ty_dec = ty_dec_of_ast ctx dec.name dec.kind dec.clauses false in
        let k = kind_of_ast dec.kind in
        Some (ty_dec.symbol, (Code ty_dec, k))
  ) ast_defs.type_defs

(* find constructor/destructor by name *)
let find_xtor (ctx: conv_ctx) (name: string) : (ty_xtor * bool) =
  let rec search defs =
    match defs with
    | [] -> failwith ("undefined constructor/destructor: " ^ name)
    | (_, (Data dec, _)) :: rest ->
        (match List.find_opt (fun x -> Path.name x.symbol = name) dec.xtors with
        | Some xtor -> (xtor, true)  (* true = constructor *)
        | None -> search rest)
    | (_, (Code dec, _)) :: rest ->
        (match List.find_opt (fun x -> Path.name x.symbol = name) dec.xtors with
        | Some xtor -> (xtor, false)  (* false = destructor *)
        | None -> search rest)
  in
  search ctx.defs

(* convert term *)
let rec term_of_ast (ctx: conv_ctx) (trm: ast) : term =
  match trm with
  | AST_Int n -> TmInt n
  
  | AST_Add (t1, t2) ->
    TmAdd (term_of_ast ctx t1, term_of_ast ctx t2)
  
  | AST_Var x ->
    (* first try to look it up as a term variable *)
    (match lookup_term_var ctx x with
    | Some id -> TmVar id
    | None ->
      (* check if it's a top-level term symbol *)
      (match lookup_term_symbol ctx x with
      | Some path -> TmSym path
      | None ->
        (* if not a variable or symbol, check if it's a constructor/destructor
          with no arguments *)
        (try
          let (xtor, is_ctor) = find_xtor ctx x in
          if is_ctor then TmCtor (xtor, [], [])
          else TmDtor (xtor, [], [])
        with Failure _ ->
          failwith ("unbound variable: " ^ x))))
  
  | AST_App (t, u) ->
    TmApp (term_of_ast ctx t, term_of_ast ctx u)
  
  | AST_Ins (t, ty) ->
    TmIns (term_of_ast ctx t, typ_of_ast ctx ty)
  
  | AST_Lam (ty_args, tm_args, body) ->
    (* first, process type arguments into nested TmAll *)
    let rec process_type_args ctx' args =
      match args with
      | [] -> process_term_args ctx' tm_args
      | (x, k_opt) :: rest ->
        let k = match k_opt with
          | Some k -> kind_of_ast k
          | None -> KStar
        in
        let x_id = Ident.mk x in
        let ctx'' = add_type_var ctx' x x_id in
        TmAll ((x_id, k), process_type_args ctx'' rest)
    
    (* then, process term arguments into nested TmLam *)
    and process_term_args ctx' args =
      match args with
      | [] -> term_of_ast ctx' body
      | (x, ty_opt) :: rest ->
        let x_id = Ident.mk x in
        let ctx'' = add_term_var ctx' x x_id in
        let rest' = process_term_args ctx'' rest in
        TmLam (x_id, Option.map (typ_of_ast ctx') ty_opt, rest')
    in
    process_type_args ctx ty_args
  
  | AST_Let (x, t, u) ->
    let t' = term_of_ast ctx t in
    let x_id = Ident.mk x in
    let ctx' = add_term_var ctx x x_id in
    TmLet (x_id, t', term_of_ast ctx' u)
  
  | AST_Match (t, clauses) ->
    let t' = term_of_ast ctx t in
    let clauses' = List.map (clause_of_ast ctx) clauses in
    TmMatch (t', clauses')
  
  | AST_New (ty_opt, clauses) ->
    let ty_opt' = Option.map (typ_of_ast ctx) ty_opt in
    let clauses' = List.map (clause_of_ast ctx) clauses in
    TmNew (ty_opt', clauses')
  
  | AST_Xtor (name, ty_args, tm_args) ->
    (* First check if this is a term symbol (function call), not a constructor/destructor *)
    (match lookup_term_symbol ctx name with
    | Some path ->
        (* It's a function call - convert to nested TmIns and TmApp *)
        let base = TmSym path in
        let with_types = List.fold_left (fun acc ty ->
          TmIns (acc, typ_of_ast ctx ty)
        ) base ty_args in
        List.fold_left (fun acc tm ->
          TmApp (acc, term_of_ast ctx tm)
        ) with_types tm_args
    | None ->
        (* Not a function, try constructor/destructor *)
        let (xtor, is_ctor) = find_xtor ctx name in
        let ty_args' = List.map (typ_of_ast ctx) ty_args in
        let tm_args' = List.map (term_of_ast ctx) tm_args in
        if is_ctor then
          TmCtor (xtor, ty_args', tm_args')
        else
          TmDtor (xtor, ty_args', tm_args'))

and clause_of_ast
    (ctx: conv_ctx) (xtor_name, ty_binders, tm_binders, body) : clause =
  let (xtor, _) = find_xtor ctx xtor_name in
  
  (* Type binders in patterns should reuse type variables already in scope,
     not shadow them with fresh identifiers. *)
  let ty_ids, ctx' = 
    List.fold_left (fun (ids_acc, ctx_acc) x ->
      (* Check if type variable is already in scope *)
      match lookup_type_var ctx_acc x with
      | Some existing_id ->
          (* Reuse existing type variable *)
          (existing_id :: ids_acc, ctx_acc)
      | None ->
          (* Create new type variable *)
          let x_id = Ident.mk x in
          (x_id :: ids_acc, add_type_var ctx_acc x x_id)
    ) ([], ctx) ty_binders
  in
  let ty_ids = List.rev ty_ids in
  
  (* bind term variables *)
  let tm_ids, ctx'' = 
    List.fold_left (fun (ids_acc, ctx_acc) x ->
      let x_id = Ident.mk x in
      (x_id :: ids_acc, add_term_var ctx_acc x x_id)
    ) ([], ctx') tm_binders
  in
  let tm_ids = List.rev tm_ids in
  
  let body' = term_of_ast ctx'' body in
  (xtor, ty_ids, tm_ids, body')

(* converting a single AST term with given type definitions *)
let to_term (ast_defs: ast_defs) (trm: ast) : term =
  let ty_defs = build_ty_defs ast_defs in
  
  (* Build context with type symbols *)
  let type_symbols = List.fold_left (fun acc (path, _) ->
    let name = Path.name path in
    StringMap.add name path acc
  ) StringMap.empty ty_defs in
  
  let ctx = { (empty_ctx ty_defs) with type_symbols = type_symbols } in
  term_of_ast ctx trm

let to_term_def (ctx: conv_ctx) (def: ast_term_def) : (Path.t * term_def) =
  (* Look up the Path.t from context - it was created in to_definitions *)
  let name = 
    match lookup_term_symbol ctx def.name with
    | Some path -> path
    | None -> failwith ("term symbol not found in context: " ^ def.name)
  in
  
  (* process type arguments *)
  let typ_args, ctx' =
    List.fold_left (fun (quant_acc, ctx_acc) (x, k_opt) ->
      let k = match k_opt with
        | Some k -> kind_of_ast k
        | None -> KStar
      in
      let x_id = Ident.mk x in
      let ctx_new = add_type_var ctx_acc x x_id in
      ((x_id, k) :: quant_acc, ctx_new)
    ) ([], ctx) def.type_args
  in
  let typ_args = List.rev typ_args in
  
  (* process term arguments *)
  let term_args, ctx'' =
    List.fold_left (fun (args_acc, ctx_acc) (x, ty) ->
      let x_id = Ident.mk x in
      let ty' = typ_of_ast ctx_acc ty in
      let ctx_new = add_term_var ctx_acc x x_id in
      ((x_id, ty') :: args_acc, ctx_new)
    ) ([], ctx') def.term_args
  in
  let term_args = List.rev term_args in
  
  let return_type = typ_of_ast ctx'' def.return_type in
  let body = term_of_ast ctx'' def.body in
  
  (name,
  { name = name
  ; type_args = typ_args
  ; term_args = term_args
  ; return_type = return_type
  ; body = body
  })

let to_definitions (ast_defs: ast_defs) : definitions =
  let ty_defs = build_ty_defs ast_defs in
  (* Extract type symbol names from ty_defs *)
  let type_symbols = List.fold_left (fun acc (path, _) ->
    let name = Path.name path in
    StringMap.add name path acc
  ) StringMap.empty ty_defs in
  
  (* Create Path.t for each term definition upfront.
     This enables mutual recursion: all definitions can reference each other
     regardless of declaration order. *)
  let term_symbols = List.fold_left (fun acc (def: ast_term_def) ->
    StringMap.add def.name (Path.of_string def.name) acc
  ) StringMap.empty ast_defs.term_defs in
  
  (* Build context with all type and term symbols *)
  let ctx = { (empty_ctx ty_defs) with 
              type_symbols = type_symbols;
              term_symbols = term_symbols } in
  
  (* Convert all term definitions using the full context.
     Since all symbols are already registered, definitions can reference
     each other in any order, including mutual recursion. *)
  let term_defs = List.map (to_term_def ctx) ast_defs.term_defs in
  
  { type_defs = ty_defs; term_defs = term_defs }