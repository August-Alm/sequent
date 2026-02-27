(**
  Module: Desugar
  Description: Convert surface syntax (Lang.Syntax) to Melcore AST.
  
  This module desugars the parsed surface language into the Melcore
  internal representation used for type checking.
*)

open Common.Identifiers
open Lang.Syntax
open Melcore.Types.MelcoreBase
module MT = Melcore.Types.MelcoreTypes
module Trm = Melcore.Terms
module StringMap = Utility.StringMap

type data_sort = Common.Types.data_sort

(* ===== CONTEXT FOR DESUGARING ===== *)

(* During desugaring we track:
  - type_vars: maps surface type variable names to internal Ident.t
  - term_vars: maps surface term variable names to internal Ident.t
  - type_symbols: maps type names (like "List") to their Path.t
  - xtor_symbols: maps constructor/destructor names to their (dec_path, xtor, polarity) *)
type conv_ctx =
  { type_vars: Ident.t StringMap.t
  ; term_vars: Ident.t StringMap.t
  ; type_symbols: (Path.t * data_sort * MT.dec Lazy.t) StringMap.t
  ; type_aliases: ast_typ StringMap.t  (* type aliases map to their definition *)
  ; xtor_symbols: (Path.t * MT.xtor * data_sort) StringMap.t  (* dec_path, xtor, data_sort *)
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

let add_xtor_symbol ctx name dec_path xtor pol =
  { ctx with xtor_symbols = StringMap.add name (dec_path, xtor, pol) ctx.xtor_symbols }

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

(* In the new type system, kinds are represented as types:
   Base Typ = kind of inhabitable types
   Arrow = higher kinds *)
let default_kind = MT.Base Typ 

let rec kind_of_ast : ast_kind -> MT.typ = function
    AST_KStar -> default_kind
  | AST_KArrow (k1, k2) -> MT.Arrow (kind_of_ast k1, kind_of_ast k2)

(* Extract parameter kinds from a kind (e.g., type -> type -> type
  gives [Base Typ; Base Typ]) *)
let rec params_of_kind : ast_kind -> MT.typ list = function
    AST_KStar -> []
  | AST_KArrow (k1, k2) -> kind_of_ast k1 :: params_of_kind k2

(* ===== TYPE CONVERSION ===== *)

let rec typ_of_ast (ctx: conv_ctx) (ty: ast_typ) : MT.typ =
  match ty with
    AST_TyVar x ->
      (* Check for primitive types first *)
      (match x with
        "int" -> MT.Ext Int
      | _ ->
          (* Check if it's a type alias *)
          (match lookup_type_alias ctx x with
          | Some aliased_ty -> typ_of_ast ctx aliased_ty
          | None ->
              (* Check if it's a type symbol (data/codata) *)
              (match lookup_type_symbol ctx x with
              | Some (path, _pol, _sgn) ->
                  (* Use Sgn with no args for nullary types *)
                  MT.Sgn (path, [])
              | None ->
                  (* Otherwise look it up as a type variable. *)
                  (match lookup_type_var ctx x with
                  | Some id -> MT.TVar id
                  | None -> failwith ("Unbound type variable: " ^ x)))))

  | AST_TyApp (t, args) ->
      (* Type application: could be List(int), algebra(b)(c) etc.
         Handle curried applications by collecting all args.
         If the head is a type symbol name, we create Sgn(name, all_args). *)
      let rec collect_ty_app head acc =
        match head with
        | AST_TyApp (h, more_args) -> collect_ty_app h (more_args @ acc)
        | _ -> (head, acc)
      in
      let (head, all_args) = collect_ty_app t args in
      let all_args' = List.map (typ_of_ast ctx) all_args in
      (match head with
        AST_TyVar name ->
          (match lookup_type_symbol ctx name with
            Some (path, _pol, _sgn) -> MT.Sgn (path, all_args')
          | None ->
              (* Higher-kinded type variable application - not yet supported *)
              failwith ("Higher-kinded application not supported: " ^ name))
      | _ ->
          (* Complex type in function position - not supported *)
          failwith "Complex type application not supported")

  | AST_TyFun (t1, t2) -> (* TODO: Is this really correct? Doesn't handle polarization *)
      MT.fun_sgn (typ_of_ast ctx t1) (typ_of_ast ctx t2)

  | AST_TyAll ((x, k_opt), t) ->
      let k = match k_opt with Some k -> kind_of_ast k | None -> default_kind in
      let x_id = Ident.mk x in
      let ctx' = add_type_var ctx x x_id in
      MT.Forall (x_id, k, typ_of_ast ctx' t)

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
      AST_TyAlias (name, ty) ->
        add_type_alias ctx name ty
    | AST_TyData dec ->
        let path = Path.of_string dec.name in
        let params = params_of_kind dec.kind in
        (* Create placeholder - will be replaced in build_signatures *)
        let sgn = lazy { MT.name = path; data_sort = Data; param_kinds = params; type_args = []; xtors = [] } in
        add_type_symbol ctx dec.name path Data sgn
    | AST_TyCode dec ->
        let path = Path.of_string dec.name in
        let params = params_of_kind dec.kind in
        let sgn = lazy { MT.name = path; data_sort = Codata; param_kinds = params; type_args = []; xtors = [] } in
        add_type_symbol ctx dec.name path Codata sgn
  ) empty_ctx defs.type_defs

(* Convert an xtor declaration to internal representation. *)

(* Helper: collect free type variables (as Ident.t) in a type *)
let rec free_type_vars_in_typ (t: MT.typ) : Ident.t list =
  match t with
  | MT.Base _ -> []
  | MT.Ext _ -> []
  | MT.TVar v -> [v]
  | MT.TMeta _ -> []
  | MT.Arrow (t1, t2) -> free_type_vars_in_typ t1 @ free_type_vars_in_typ t2
  | MT.Sgn (_, args) -> List.concat_map free_type_vars_in_typ args
  | MT.PromotedCtor (_, _, args) -> List.concat_map free_type_vars_in_typ args
  | MT.Forall (v, k, body) -> 
      let fv = free_type_vars_in_typ body in
      List.filter (fun x -> not (Ident.equal x v)) fv @
      free_type_vars_in_typ k

let xtor_of_ast (ctx: conv_ctx) (ds: Common.Types.data_sort) (xtor: ast_xtor) : MT.xtor =
  (* Build context with type parameters *)
  let params, ctx' =
    List.fold_left (fun (acc, ctx_acc) (x, k_opt) ->
      let k = match k_opt with Some k -> kind_of_ast k | None -> default_kind in
      let x_id = Ident.mk x in
      ((x_id, k) :: acc, add_type_var ctx_acc x x_id)
    ) ([], ctx) xtor.type_args
  in
  let params = List.rev params in
  
  (* Convert argument types *)
  let arg_types = List.map (typ_of_ast ctx') xtor.term_args in
  
  (* For data types: args -> parent(params)
    For codata types: parent(params) -> args -> result
    The last type in term_args is the main/result type *)
  let arguments, main_from_ast =
    match ds with
    | Common.Types.Data ->
      (* Data: all args are arguments, main is parent(params) *)
      (* Data: all but last are arguments, last is main (must be parent applied to type args) *)
      (match List.rev arg_types with
        [] -> failwith ("Constructor " ^ xtor.name ^ " must have a return type")
      | main :: rev_args -> (List.rev rev_args, main))
    | Common.Types.Codata ->
      (* Codata: first is "this" (main), rest are arguments including result.
         argument_types is stored reversed (arg0 first where arg0 is the result).
         Surface: main -> argN -> ... -> arg0
         Storage: [arg0; ...; argN] = reverse of (rest) *)
      (match arg_types with
        [] -> failwith ("Destructor " ^ xtor.name ^ " must have a receiver type")
      | main :: args -> (List.rev args, main))
  in
  
  (* Wrap arguments as chiral types (in Melcore, mk_producer is identity) *)
  let chiral_args = List.map mk_producer arguments in
  
  (* Split params into quantified vs existentials:
     - quantified: params that appear free in the main type (determine the declaration's type args)
     - existentials: params that don't appear in main type (independently chosen by the xtor)
     
     For example, in: fold: {d}{r} foldable(d) -> algebra(d)(r) -> r
     - main = foldable(d), so d is quantified
     - r doesn't appear in main, so r is existential *)
  let main_free_vars = free_type_vars_in_typ main_from_ast in
  let is_quantified (v, _k) = List.exists (Ident.equal v) main_free_vars in
  let quantified = List.filter is_quantified params in
  let existentials = List.filter (fun p -> not (is_quantified p)) params in
  
  { MT.name = Path.of_string xtor.name
  ; quantified = quantified
  ; existentials = existentials
  ; argument_types = chiral_args
  ; main = main_from_ast
  }

(* Build a signature with self-referential lazy.
  Uses OCaml's recursive value binding to create a lazy that references itself. *)
let build_recursive_signature 
    (ctx: conv_ctx) (path: Path.t) (dec: ast_type_dec) (ds: Common.Types.data_sort) 
    : MT.dec Lazy.t =
  let params = params_of_kind dec.kind in
  (* Create a recursive lazy that contains itself *)
  let rec lazy_sgn = lazy begin
    (* Create a modified context where this type maps to our recursive lazy *)
    let ctx = add_type_symbol ctx dec.name path ds lazy_sgn in
    let xtors = List.map (xtor_of_ast ctx ds) dec.clauses in
    {MT.name = path; data_sort = ds; param_kinds = params; type_args = []; xtors = xtors}
  end in
  lazy_sgn

(* Second pass: build signatures with proper recursive references *)
let build_signatures (ctx: conv_ctx) (defs: ast_defs) : conv_ctx =
  (* Build signatures one by one, each with proper self-reference *)
  let ctx = List.fold_left (fun ctx tdef ->
    match tdef with
      AST_TyAlias _ -> ctx
    | AST_TyData dec ->
        let (path, _, _) =
          match lookup_type_symbol ctx dec.name with
            Some x -> x
          | None -> failwith ("Type symbol not found: " ^ dec.name)
        in
        let lazy_sgn = build_recursive_signature ctx path dec Common.Types.Data in
        add_type_symbol ctx dec.name path Data lazy_sgn
    | AST_TyCode dec ->
        let (path, _, _) =
          match lookup_type_symbol ctx dec.name with
            Some x -> x
          | None -> failwith ("Type symbol not found: " ^ dec.name)
        in
        let lazy_sgn = build_recursive_signature ctx path dec Common.Types.Codata in
        add_type_symbol ctx dec.name path Codata lazy_sgn
  ) ctx defs.type_defs in
  
  (* Register xtors by forcing the signatures (now safe with recursive lazy) *)
  List.fold_left (fun ctx tdef ->
    match tdef with
      AST_TyAlias _ -> ctx
    | AST_TyData dec ->
        let (_, _, lazy_sgn) =
          match lookup_type_symbol ctx dec.name with
            Some x -> x
          | None -> failwith ("Type symbol not found: " ^ dec.name)
        in
        let sgn = Lazy.force lazy_sgn in
        List.fold_left (fun ctx (xtor: MT.xtor) ->
          add_xtor_symbol ctx (Path.name xtor.name) sgn.name xtor Data
        ) ctx sgn.xtors
    | AST_TyCode dec ->
        let (_, _, lazy_sgn) =
          match lookup_type_symbol ctx dec.name with
            Some x -> x
          | None -> failwith ("Type symbol not found: " ^ dec.name)
        in
        let sgn = Lazy.force lazy_sgn in
        List.fold_left (fun ctx (xtor: MT.xtor) ->
          add_xtor_symbol ctx (Path.name xtor.name) sgn.name xtor Codata
        ) ctx sgn.xtors
  ) ctx defs.type_defs

(* ===== TERM CONVERSION ===== *)

(* Helper to collect applications and instantiations from an AST term.
   Returns (head, ty_args, tm_args) where head is the base term being applied. *)
let rec collect_apps (trm: ast) : ast * ast_typ list * ast list =
  match trm with
  | AST_App (t, u) ->
      let head, ty_args, tm_args = collect_apps t in
      (head, ty_args, tm_args @ [u])
  | AST_Ins (t, ty) ->
      let head, ty_args, tm_args = collect_apps t in
      if tm_args <> [] then
        failwith "Type instantiation after term application is not allowed"
      else
        (head, ty_args @ [ty], tm_args)
  | _ -> (trm, [], [])

let rec term_of_ast (ctx: conv_ctx) (trm: ast) : Trm.term =
  match trm with
    AST_Int n -> Trm.Int n
  
  | AST_Add (t1, t2) ->
      Trm.Add (term_of_ast ctx t1, term_of_ast ctx t2)
  
  | AST_Sub (t1, t2) ->
      Trm.Sub (term_of_ast ctx t1, term_of_ast ctx t2)
  
  | AST_Ifz (n, t, u) ->
      Trm.Ifz (term_of_ast ctx n, term_of_ast ctx t, term_of_ast ctx u)
  
  | AST_Var x ->
      (* First try term variable *)
      (match lookup_term_var ctx x with
        Some id -> Trm.Var id
      | None ->
          (* Then try term symbol (top-level def) *)
          (match lookup_term_symbol ctx x with
            Some path -> Trm.Sym path
          | None ->
              (* Then try as a nullary constructor/destructor *)
              (match lookup_xtor_symbol ctx x with
                Some (dec_path, xtor, Data) -> Trm.Ctor (dec_path, xtor.name, [], [])
              | Some (dec_path, xtor, Codata) -> Trm.Dtor (dec_path, xtor.name, [], [])
              | None -> failwith ("Unbound variable: " ^ x))))
  
  | AST_App _ | AST_Ins _ ->
      (* Collect all nested apps and ins to handle xtor applications correctly *)
      let head, ty_args, tm_args = collect_apps trm in
      (match head with
      | AST_Var x ->
          (* Check if head is a term variable - regular application *)
          (match lookup_term_var ctx x with
          | Some id ->
              let base = Trm.Var id in
              let with_types = List.fold_left (fun acc ty ->
                Trm.Ins (acc, typ_of_ast ctx ty)
              ) base ty_args in
              List.fold_left (fun acc tm ->
                Trm.App (acc, term_of_ast ctx tm)
              ) with_types tm_args
          | None ->
              (* Check if head is a term symbol (function) *)
              (match lookup_term_symbol ctx x with
              | Some path ->
                  let base = Trm.Sym path in
                  let with_types = List.fold_left (fun acc ty ->
                    Trm.Ins (acc, typ_of_ast ctx ty)
                  ) base ty_args in
                  List.fold_left (fun acc tm ->
                    Trm.App (acc, term_of_ast ctx tm)
                  ) with_types tm_args
              | None ->
                  (* Check if head is a constructor/destructor *)
                  (match lookup_xtor_symbol ctx x with
                  | Some (dec_path, xtor, ds) ->
                      let ty_args' = List.map (typ_of_ast ctx) ty_args in
                      let tm_args' = List.map (term_of_ast ctx) tm_args in
                      (match ds with
                        Data -> Trm.Ctor (dec_path, xtor.name, ty_args', tm_args')
                      | Codata -> Trm.Dtor (dec_path, xtor.name, ty_args', tm_args'))
                  | None -> failwith ("Unbound: " ^ x))))
      | _ ->
          (* General case: head is not a simple variable *)
          let base = term_of_ast ctx head in
          let with_types = List.fold_left (fun acc ty ->
            Trm.Ins (acc, typ_of_ast ctx ty)
          ) base ty_args in
          List.fold_left (fun acc tm ->
            Trm.App (acc, term_of_ast ctx tm)
          ) with_types tm_args)
  
  | AST_Lam (ty_args, tm_args, body) ->
      (* Process type args into nested All, then term args into nested Lam *)
      let rec process_ty_args ctx_ty = function
          [] -> process_tm_args ctx_ty tm_args
        | (x, k_opt) :: rest ->
            let k = match k_opt with Some k -> kind_of_ast k | None -> default_kind in
            let x_id = Ident.mk x in
            let ctx_ty' = add_type_var ctx_ty x x_id in
            Trm.All ((x_id, k), process_ty_args ctx_ty' rest)
      and process_tm_args ctx_tm = function
          [] -> term_of_ast ctx_tm body
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
      (* First check if it's a local term variable *)
      (match lookup_term_var ctx name with
        Some id ->
          (* Local variable with type/term applications *)
          let base = Trm.Var id in
          let with_types = List.fold_left (fun acc ty ->
            Trm.Ins (acc, typ_of_ast ctx ty)
          ) base ty_args in
          List.fold_left (fun acc tm ->
            Trm.App (acc, term_of_ast ctx tm)
          ) with_types tm_args
      | None ->
          (* Then check if it's a term symbol (top-level function call) *)
          (match lookup_term_symbol ctx name with
            Some path ->
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
                Some (dec_path, xtor, ds) ->
                  (* Apply type arguments to instantiate xtor's universal params.
                    xtor.quantified are the universals, ty_args are the instantiations. *)
                  let ty_args' = List.map (typ_of_ast ctx) ty_args in
                  let args' = List.map (term_of_ast ctx) tm_args in
                  (match ds with
                    Data -> Trm.Ctor (dec_path, xtor.name, ty_args', args')
                  | Codata -> Trm.Dtor (dec_path, xtor.name, ty_args', args'))
              | None -> failwith ("Unknown constructor/destructor: " ^ name))))

and branch_of_clause
    (ctx: conv_ctx) (xtor_name, ty_binders, tm_binders, body) : Trm.branch =
  (* Look up the xtor *)
  let (_dec_path, xtor, _ds) =
    match lookup_xtor_symbol ctx xtor_name with
      Some x -> x
    | None -> failwith ("Unknown xtor in pattern: " ^ xtor_name)
  in
  
  (* Bind type variables and collect their ids *)
  let ty_ids, ctx =
    List.fold_left (fun (ids, ctx) x ->
      match lookup_type_var ctx x with
        Some id -> (id :: ids, ctx)  (* Already in scope *)
      | None -> 
          let x_id = Ident.mk x in
          (x_id :: ids, add_type_var ctx x x_id)
    ) ([], ctx) ty_binders
  in
  let ty_ids = List.rev ty_ids in
  
  (* Bind term variables *)
  let tm_ids, ctx =
    List.fold_left (fun (ids, ctx) x ->
      let x_id = Ident.mk x in
      (x_id :: ids, add_term_var ctx x x_id)
    ) ([], ctx) tm_binders
  in
  let tm_ids = List.rev tm_ids in
  
  let body' = term_of_ast ctx body in
  (xtor.name, ty_ids, tm_ids, body')

(* ===== TOP-LEVEL CONVERSION ===== *)

(* Collect term symbols before processing definitions *)
let collect_term_symbols (ctx: conv_ctx) (defs: ast_defs) : conv_ctx =
  List.fold_left (fun ctx (def: ast_term_def) ->
    add_term_symbol ctx def.name (Path.of_string def.name)
  ) ctx defs.term_defs

(* Convert a term definition *)
let term_def_of_ast (ctx: conv_ctx) (def: ast_term_def) : Trm.term_def =
  let path = match lookup_term_symbol ctx def.name with
      Some p -> p
    | None -> failwith ("Term symbol not found: " ^ def.name)
  in
  
  (* Process type args *)
  let type_args, ctx =
    List.fold_left (fun (acc, ctx) (x, k_opt) ->
      let k = match k_opt with Some k -> kind_of_ast k | None -> default_kind in
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
  ; type_params = type_args
  ; term_params = term_args
  ; return_type = return_type
  ; body = body
  }

(* Result type for desugaring *)
type desugar_result =
  { type_defs: MT.dec list
  ; term_defs: Trm.definitions
  }

(** Main entry point: desugar all definitions *)
let desugar (defs: ast_defs) : desugar_result =
  (* Phase 1: collect type symbols *)
  let ctx = collect_type_symbols defs in
  (* Phase 2: build signatures with xtors *)
  let ctx = build_signatures ctx defs in
  (* Phase 3: collect term symbols for mutual recursion *)
  let ctx = collect_term_symbols ctx defs in
  (* Phase 4: convert term definitions *)
  let term_defs = List.map (term_def_of_ast ctx) defs.term_defs in
  (* Build term definitions table *)
  let term_tbl = List.fold_left (fun tbl (def: Trm.term_def) ->
    Path.add def.name def tbl
  ) Path.emptytbl term_defs in
  (* Collect type signatures (skip aliases) *)
  let type_sigs = List.filter_map (fun tdef ->
    match tdef with
      AST_TyAlias _ -> None
    | AST_TyData dec | AST_TyCode dec ->
        match lookup_type_symbol ctx dec.name with
        | Some (_, _, lazy_sgn) -> Some (Lazy.force lazy_sgn)
        | None -> None
  ) defs.type_defs in
  { type_defs = type_sigs; term_defs = term_tbl }

(* Convert a single term with given definitions context *)
let desugar_term (defs: ast_defs) (trm: ast) : Trm.term =
  let ctx = collect_type_symbols defs in
  let ctx = build_signatures ctx defs in
  let ctx = collect_term_symbols ctx defs in
  term_of_ast ctx trm
