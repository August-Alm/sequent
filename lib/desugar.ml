(**
  Module: Desugar
  Description: Convert surface syntax (Lang.Syntax) to Melcore AST.
  
  This module desugars the parsed surface language into the Melcore
  intermediate representation used for type checking.
*)

open Common.Identifiers
open Lang.Syntax
module MT = Melcore.Types
module Trm = Melcore.Terms
module StringMap = Utility.StringMap

(* ===== CONTEXT FOR DESUGARING ===== *)

(* During desugaring we track:
   - type_vars: maps surface type variable names to internal Ident.t
   - term_vars: maps surface term variable names to internal Ident.t
   - type_symbols: maps type names (like "List") to their Path.t
   - xtor_symbols: maps constructor/destructor names to their (xtor, polarity) *)
type conv_ctx =
  { type_vars: Ident.t StringMap.t
  ; term_vars: Ident.t StringMap.t
  ; type_symbols: (Path.t * MT.polarity * MT.sgn_typ Lazy.t) StringMap.t
  ; type_aliases: ast_typ StringMap.t  (* type aliases map to their definition *)
  ; xtor_symbols: (MT.xtor * MT.polarity) StringMap.t
  ; term_symbols: Path.t StringMap.t
  }

let empty_ctx : conv_ctx =
  { type_vars = StringMap.empty
  ; term_vars = StringMap.empty
  ; type_symbols = StringMap.empty
  ; type_aliases = StringMap.empty
  ; xtor_symbols = StringMap.empty
  ; term_symbols = StringMap.empty
  }

let add_type_var ctx name id =
  { ctx with type_vars = StringMap.add name id ctx.type_vars }

let add_term_var ctx name id =
  { ctx with term_vars = StringMap.add name id ctx.term_vars }

let add_type_symbol ctx name path pol sgn =
  { ctx with type_symbols = StringMap.add name (path, pol, sgn) ctx.type_symbols }

let add_xtor_symbol ctx name xtor pol =
  { ctx with xtor_symbols = StringMap.add name (xtor, pol) ctx.xtor_symbols }

let add_term_symbol ctx name path =
  { ctx with term_symbols = StringMap.add name path ctx.term_symbols }

let add_type_alias ctx name ty =
  { ctx with type_aliases = StringMap.add name ty ctx.type_aliases }

let lookup_type_var ctx name = StringMap.find_opt name ctx.type_vars
let lookup_type_alias ctx name = StringMap.find_opt name ctx.type_aliases
let lookup_term_var ctx name = StringMap.find_opt name ctx.term_vars
let lookup_type_symbol ctx name = StringMap.find_opt name ctx.type_symbols
let lookup_xtor_symbol ctx name = StringMap.find_opt name ctx.xtor_symbols
let lookup_term_symbol ctx name = StringMap.find_opt name ctx.term_symbols

(* ===== KIND CONVERSION ===== *)

let rec kind_of_ast : ast_kind -> MT.kind = function
  | AST_KStar -> MT.Star
  | AST_KArrow (k1, k2) -> MT.Arrow (kind_of_ast k1, kind_of_ast k2)

(* Extract parameter kinds from a kind (e.g., type -> type -> type gives [Star; Star]) *)
let rec params_of_kind : ast_kind -> MT.kind list = function
  | AST_KStar -> []
  | AST_KArrow (k1, k2) -> kind_of_ast k1 :: params_of_kind k2

(* ===== TYPE CONVERSION ===== *)

let rec typ_of_ast (ctx: conv_ctx) (ty: ast_typ) : MT.typ =
  match ty with
  | AST_TyVar x ->
      (* Check for primitive types first *)
      (match x with
      | "int" -> MT.Ext MT.Int
      | _ ->
          (* Check if it's a type alias *)
          (match lookup_type_alias ctx x with
          | Some aliased_ty -> typ_of_ast ctx aliased_ty
          | None ->
              (* Check if it's a type symbol (data/codata) *)
              (match lookup_type_symbol ctx x with
              | Some (path, pol, sgn) ->
                  (* Use Sym directly for nullary types.
                     whnf only instantiates App(Sym, args), not bare Sym.
                     Sym will be wrapped in App when type arguments are applied. *)
                  MT.Sym (path, pol, sgn)
              | None ->
                  (* Otherwise look it up as a type variable.
                     Use Var (Unbound id), NOT Rigid - we don't have existential
                     syntax support yet, so all type variables are universals
                     that should be substitutable. *)
                  (match lookup_type_var ctx x with
                  | Some id -> MT.Var (ref (MT.Unbound id))
                  | None -> failwith ("Unbound type variable: " ^ x)))))

  | AST_TyApp (t, args) ->
      let t' = typ_of_ast ctx t in
      let args' = List.map (typ_of_ast ctx) args in
      MT.App (t', args')

  | AST_TyFun (t1, t2) ->
      MT.Fun (typ_of_ast ctx t1, typ_of_ast ctx t2)

  | AST_TyAll ((x, k_opt), t) ->
      let k = match k_opt with Some k -> kind_of_ast k | None -> MT.Star in
      let x_id = Ident.mk x in
      let ctx' = add_type_var ctx x x_id in
      MT.All ((x_id, k), typ_of_ast ctx' t)

(* ===== SIGNATURE BUILDING ===== *)

(* Build all type signatures at once, handling mutual recursion properly.
   This uses a two-phase approach:
   1. Create all paths and register them with placeholder lazy signatures
   2. Build the actual signatures, which can reference any type via the context
   The key is that the lazy signatures capture the context at the time they're forced,
   so mutual references work correctly. *)

(* First pass: create all type symbols with placeholder signatures that will 
   be replaced in the second pass *)
let collect_type_symbols (defs: ast_defs) : conv_ctx =
  List.fold_left (fun ctx tdef ->
    match tdef with
    | AST_TyAlias (name, ty) ->
        add_type_alias ctx name ty
    
    | AST_TyData dec ->
        let path = Path.of_string dec.name in
        let params = params_of_kind dec.kind in
        (* Create placeholder - will be replaced in build_signatures *)
        let sgn = lazy { MT.name = path; parameters = params; xtors = [] } in
        add_type_symbol ctx dec.name path MT.Pos sgn
    
    | AST_TyCode dec ->
        let path = Path.of_string dec.name in
        let params = params_of_kind dec.kind in
        let sgn = lazy { MT.name = path; parameters = params; xtors = [] } in
        add_type_symbol ctx dec.name path MT.Neg sgn
  ) empty_ctx defs.type_defs

(* Convert an xtor declaration to internal representation.
   parent_lazy_sgn is the lazy signature being built - used for xtor.main
   to avoid Sym -> whnf -> Sym infinite recursion. *)
let xtor_of_ast (ctx: conv_ctx) (_parent_path: Path.t) (_parent_params: MT.kind list) 
    (_parent_lazy_sgn: MT.sgn_typ Lazy.t) (is_data: bool) (xtor: ast_xtor) : MT.xtor =
  (* Build context with type parameters *)
  let params, ctx' =
    List.fold_left (fun (acc, ctx_acc) (x, k_opt) ->
      let k = match k_opt with Some k -> kind_of_ast k | None -> MT.Star in
      let x_id = Ident.mk x in
      ((x_id, k) :: acc, add_type_var ctx_acc x x_id)
    ) ([], ctx) xtor.type_args
  in
  let params = List.rev params in
  
  (* Convert argument types - these use Sym which is fine *)
  let arg_types = List.map (typ_of_ast ctx') xtor.term_args in
  
  (* For data types: args -> parent(params)
     For codata types: parent(params) -> args -> result
     The last type in term_args is the main/result type *)
  let arguments, _main_from_ast =
    if is_data then
      (* Data: all but last are arguments, last is main (must be parent applied to type args) *)
      match List.rev arg_types with
      | [] -> failwith ("Constructor " ^ xtor.name ^ " must have a return type")
      | main :: rev_args -> (List.rev rev_args, main)
    else
      (* Codata: first is "this" (main), rest are arguments including result *)
      match arg_types with
      | [] -> failwith ("Destructor " ^ xtor.name ^ " must have a receiver type")
      | main :: args -> (args, main)
  in
  
  (* CRITICAL: Use the main type directly from the AST (_main_from_ast).
     This correctly handles GADTs where constructors specify concrete type arguments.
     For example:
     - lit: int -> expr(int) should have main = App(Sym(expr), [Sym(int)])
     - add: expr(int) -> expr(int) -> expr(int) should have main = App(Sym(expr), [Sym(int)])
     - ifthenelse: {a:type}. bool -> a -> a -> expr(a) has main = App(Sym(expr), [Var a])
     
     The previous approach of constructing main from params was wrong because
     non-polymorphic GADT constructors (like lit) have no type params but still
     have concrete type arguments in their return type. *)
  let main = _main_from_ast in
  let _ = main in (* Suppress unused warning if needed *)
  
  (* For now, no existentials - all type params are universals *)
  { MT.name = Path.of_string xtor.name
  ; parameters = params
  ; existentials = []
  ; arguments = arguments
  ; main = main
  }

(* Build a signature with self-referential lazy.
   Uses OCaml's recursive value binding to create a lazy that references itself. *)
let build_recursive_signature 
    (ctx: conv_ctx) (path: Path.t) (dec: ast_type_dec) (is_data: bool) 
    : MT.sgn_typ Lazy.t =
  let params = params_of_kind dec.kind in
  let pol = if is_data then MT.Pos else MT.Neg in
  (* Create a recursive lazy that contains itself *)
  let rec lazy_sgn = lazy begin
    (* Create a modified context where this type maps to our recursive lazy *)
    let ctx = add_type_symbol ctx dec.name path pol lazy_sgn in
    let xtors = List.map (xtor_of_ast ctx path params lazy_sgn is_data) dec.clauses in
    { MT.name = path; parameters = params; xtors = xtors }
  end in
  lazy_sgn

(* Second pass: build signatures with proper recursive references *)
let build_signatures (ctx: conv_ctx) (defs: ast_defs) : conv_ctx =
  (* Build signatures one by one, each with proper self-reference *)
  let ctx = List.fold_left (fun ctx tdef ->
    match tdef with
    | AST_TyAlias _ -> ctx
    
    | AST_TyData dec ->
        let (path, _, _) = match lookup_type_symbol ctx dec.name with
          | Some x -> x
          | None -> failwith ("Type symbol not found: " ^ dec.name)
        in
        let lazy_sgn = build_recursive_signature ctx path dec true in
        add_type_symbol ctx dec.name path MT.Pos lazy_sgn
    
    | AST_TyCode dec ->
        let (path, _, _) = match lookup_type_symbol ctx dec.name with
          | Some x -> x
          | None -> failwith ("Type symbol not found: " ^ dec.name)
        in
        let lazy_sgn = build_recursive_signature ctx path dec false in
        add_type_symbol ctx dec.name path MT.Neg lazy_sgn
  ) ctx defs.type_defs in
  
  (* Register xtors by forcing the signatures (now safe with recursive lazy) *)
  List.fold_left (fun ctx tdef ->
    match tdef with
    | AST_TyAlias _ -> ctx
    
    | AST_TyData dec ->
        let (_, _, lazy_sgn) = match lookup_type_symbol ctx dec.name with
          | Some x -> x
          | None -> failwith ("Type symbol not found: " ^ dec.name)
        in
        let sgn = Lazy.force lazy_sgn in
        List.fold_left (fun ctx (xtor: MT.xtor) ->
          add_xtor_symbol ctx (Path.name xtor.name) xtor MT.Pos
        ) ctx sgn.xtors
    
    | AST_TyCode dec ->
        let (_, _, lazy_sgn) = match lookup_type_symbol ctx dec.name with
          | Some x -> x
          | None -> failwith ("Type symbol not found: " ^ dec.name)
        in
        let sgn = Lazy.force lazy_sgn in
        List.fold_left (fun ctx (xtor: MT.xtor) ->
          add_xtor_symbol ctx (Path.name xtor.name) xtor MT.Neg
        ) ctx sgn.xtors
  ) ctx defs.type_defs

(* ===== TERM CONVERSION ===== *)

let rec term_of_ast (ctx: conv_ctx) (trm: ast) : Trm.term =
  match trm with
  | AST_Int n -> Trm.Int n
  
  | AST_Add (t1, t2) ->
      Trm.Add (term_of_ast ctx t1, term_of_ast ctx t2)
  
  | AST_Var x ->
      (* First try term variable *)
      (match lookup_term_var ctx x with
      | Some id -> Trm.Var id
      | None ->
          (* Then try term symbol (top-level def) *)
          (match lookup_term_symbol ctx x with
          | Some path -> Trm.Sym path
          | None ->
              (* Then try as a nullary constructor/destructor *)
              (match lookup_xtor_symbol ctx x with
              | Some (xtor, MT.Pos) -> Trm.Ctor (xtor, [])
              | Some (xtor, MT.Neg) -> Trm.Dtor (xtor, [])
              | None -> failwith ("Unbound variable: " ^ x))))
  
  | AST_App (t, u) ->
      Trm.App (term_of_ast ctx t, term_of_ast ctx u)
  
  | AST_Ins (t, ty) ->
      Trm.Ins (term_of_ast ctx t, typ_of_ast ctx ty)
  
  | AST_Lam (ty_args, tm_args, body) ->
      (* Process type args into nested All, then term args into nested Lam *)
      let rec process_ty_args ctx_ty = function
        | [] -> process_tm_args ctx_ty tm_args
        | (x, k_opt) :: rest ->
            let k = match k_opt with Some k -> kind_of_ast k | None -> MT.Star in
            let x_id = Ident.mk x in
            let ctx_ty' = add_type_var ctx_ty x x_id in
            Trm.All ((x_id, k), process_ty_args ctx_ty' rest)
      and process_tm_args ctx_tm = function
        | [] -> term_of_ast ctx_tm body
        | (x, ty_opt) :: rest ->
            let x_id = Ident.mk x in
            let ty_opt' = Option.map (typ_of_ast ctx_tm) ty_opt in
            let ctx_tm' = add_term_var ctx_tm x x_id in
            Trm.Lam (x_id, ty_opt', process_tm_args ctx_tm' rest)
      in
      process_ty_args ctx ty_args
  
  | AST_Let (x, t, u) ->
      let t' = term_of_ast ctx t in
      let x_id = Ident.mk x in
      let ctx' = add_term_var ctx x x_id in
      Trm.Let (x_id, t', term_of_ast ctx' u)
  
  | AST_Match (t, clauses) ->
      let t' = term_of_ast ctx t in
      let clauses' = List.map (branch_of_clause ctx) clauses in
      Trm.Match (t', clauses')
  
  | AST_New (ty_opt, clauses) ->
      let ty_opt' = Option.map (typ_of_ast ctx) ty_opt in
      let clauses' = List.map (branch_of_clause ctx) clauses in
      Trm.New (ty_opt', clauses')
  
  | AST_Xtor (name, ty_args, tm_args) ->
      (* First check if it's a term symbol (function call) *)
      (match lookup_term_symbol ctx name with
      | Some path ->
          (* Function call: convert to nested Ins and App *)
          let base = Trm.Sym path in
          let with_types = List.fold_left (fun acc ty ->
            Trm.Ins (acc, typ_of_ast ctx ty)
          ) base ty_args in
          List.fold_left (fun acc tm ->
            Trm.App (acc, term_of_ast ctx tm)
          ) with_types tm_args
      | None ->
          (* Constructor or destructor *)
          (match lookup_xtor_symbol ctx name with
          | Some (xtor, pol) ->
              (* Apply type arguments to instantiate xtor's universal params.
                 xtor.parameters are the universals, ty_args are the instantiations. *)
              let ty_args' = List.map (typ_of_ast ctx) ty_args in
              let xtor' =
                if List.length ty_args' = List.length xtor.parameters then
                  (* Build substitution: xtor param ids -> provided type args *)
                  let subst = List.map2 (fun (id, _) ty -> (id, ty)) 
                    xtor.parameters ty_args' in
                  { xtor with
                    parameters = []
                  ; arguments = List.map (MT.subst_unbound subst) xtor.arguments
                  ; main = MT.subst_unbound subst xtor.main
                  }
                else if ty_args' = [] then
                  xtor (* No instantiation - will be inferred *)
                else
                  failwith (Printf.sprintf 
                    "Type arity mismatch for %s: expected %d, got %d"
                    name (List.length xtor.parameters) (List.length ty_args'))
              in
              let args' = List.map (term_of_ast ctx) tm_args in
              (match pol with
              | MT.Pos -> Trm.Ctor (xtor', args')
              | MT.Neg -> Trm.Dtor (xtor', args'))
          | None -> failwith ("Unknown constructor/destructor: " ^ name)))

and branch_of_clause (ctx: conv_ctx) (xtor_name, ty_binders, tm_binders, body) : Trm.branch =
  (* Look up the xtor *)
  let (xtor, _pol) = match lookup_xtor_symbol ctx xtor_name with
    | Some x -> x
    | None -> failwith ("Unknown xtor in pattern: " ^ xtor_name)
  in
  
  (* Bind type variables *)
  let ctx = List.fold_left (fun ctx x ->
    match lookup_type_var ctx x with
    | Some _ -> ctx  (* Already in scope *)
    | None -> add_type_var ctx x (Ident.mk x)
  ) ctx ty_binders in
  
  (* Bind term variables *)
  let tm_ids, ctx =
    List.fold_left (fun (ids, ctx) x ->
      let x_id = Ident.mk x in
      (x_id :: ids, add_term_var ctx x x_id)
    ) ([], ctx) tm_binders
  in
  let tm_ids = List.rev tm_ids in
  
  let body' = term_of_ast ctx body in
  (xtor, tm_ids, body')

(* ===== TOP-LEVEL CONVERSION ===== *)

(* Collect term symbols before processing definitions *)
let collect_term_symbols (ctx: conv_ctx) (defs: ast_defs) : conv_ctx =
  List.fold_left (fun ctx (def: ast_term_def) ->
    add_term_symbol ctx def.name (Path.of_string def.name)
  ) ctx defs.term_defs

(* Convert a term definition *)
let term_def_of_ast (ctx: conv_ctx) (def: ast_term_def) : Trm.term_def =
  let path = match lookup_term_symbol ctx def.name with
    | Some p -> p
    | None -> failwith ("Term symbol not found: " ^ def.name)
  in
  
  (* Process type args *)
  let type_args, ctx =
    List.fold_left (fun (acc, ctx) (x, k_opt) ->
      let k = match k_opt with Some k -> kind_of_ast k | None -> MT.Star in
      let x_id = Ident.mk x in
      ((x_id, k) :: acc, add_type_var ctx x x_id)
    ) ([], ctx) def.type_args
  in
  let type_args = List.rev type_args in
  
  (* Process term args *)
  let term_args, ctx =
    List.fold_left (fun (acc, ctx) (x, ty) ->
      let x_id = Ident.mk x in
      let ty' = typ_of_ast ctx ty in
      ((x_id, ty') :: acc, add_term_var ctx x x_id)
    ) ([], ctx) def.term_args
  in
  let term_args = List.rev term_args in
  
  let return_type = typ_of_ast ctx def.return_type in
  let body = term_of_ast ctx def.body in
  
  { Trm.name = path
  ; type_args = type_args
  ; term_args = term_args
  ; return_type = return_type
  ; body = body
  }

(* Main entry point: desugar all definitions *)
let desugar (defs: ast_defs) : Trm.definitions =
  (* Phase 1: collect type symbols *)
  let ctx = collect_type_symbols defs in
  (* Phase 2: build signatures with xtors *)
  let ctx = build_signatures ctx defs in
  (* Phase 3: collect term symbols for mutual recursion *)
  let ctx = collect_term_symbols ctx defs in
  (* Phase 4: convert term definitions *)
  let term_defs = List.map (term_def_of_ast ctx) defs.term_defs in
  (* Build Path.tbl *)
  List.fold_left (fun tbl (def: Trm.term_def) ->
    Path.add def.name def tbl
  ) Path.emptytbl term_defs

(* Convert a single term with given definitions context *)
let desugar_term (defs: ast_defs) (trm: ast) : Trm.term =
  let ctx = collect_type_symbols defs in
  let ctx = build_signatures ctx defs in
  let ctx = collect_term_symbols ctx defs in
  term_of_ast ctx trm
