(**
  Module: Core.Terms
  Description: Term syntax the of intermediate language Core.
  
  This module contains the definition of the abstract syntax of the
  intermediate language Core.
*)

open Common.Identifiers
open Common.Types

type chirality =
  | Prd of Type.t
  | Cns of Type.t

module Chirality = struct
  let to_string = function
    | Prd ty -> "Prd " ^ Type.to_string ty
    | Cns ty -> "Cns " ^ Type.to_string ty
end

module Context = struct
  type t =
    { kinds: kind Ident.tbl
    ; chiralities: chirality Ident.tbl
    }
  
  let empty = {kinds = Ident.emptytbl; chiralities = Ident.emptytbl}

  let add (x, ch: (Ident.t * chirality)) (ctx: t) =
    { kinds = Ident.add x KStar ctx.kinds
    ; chiralities = Ident.add x ch ctx.chiralities
    }
  
  let add_many (xs: (Ident.t * chirality) list) (ctx: t) =
    List.fold_left (fun acc x -> add x acc) ctx xs

  let kinds (ctx: t) = ctx.kinds

  let lookup_chirality (x: Ident.t) (ctx: t)  =
    Ident.find_opt x ctx.chiralities
  
  let lookup_kind (x: Ident.t) (ctx: t) =
    Ident.find x ctx.kinds
end


type statement =
  | Cut of producer * consumer

and producer =
  | Int of int
  | Var of Ident.t
  | Mu of Ident.t * statement
  | Constructor of Path.t * xtor_args 
  | Cocase of pattern list

and consumer =
  | Covar of Ident.t
  | MuTilde of Ident.t * statement
  | Destructor of Path.t * xtor_args
  | Case of pattern list

and pattern =
  { xtor: Path.t
  ; type_vars: Ident.t list
  ; variables: Ident.t list
  ; covariables: Ident.t list
  ; statement: statement
  }

and expression =
  Pro of producer | Con of consumer

and xtor_args =
  (* Bi's          pi: Prd Ai        ci: Cns Bi *)
  (Type.t list) * (producer list) * (consumer list)

type term_def =
  { name: Path.t
  ; type_args: (Ident.t * Kind.t) list
  ; prod_args: (Ident.t * Type.t) list
  ; cons_args: (Ident.t * Type.t) list
  ; return_type: Type.t
  ; body: statement
  }

type definitions =
  { type_defs: ty_defs
  ; term_defs: (Path.t * term_def) list
  }

type context =
  { kinds: kind Ident.tbl
  ; types: typ Ident.tbl
  }

exception Error of string
let error msg = raise (Error msg)

module CT = Common.Types

(* Helper functions to look up type definitions and xtors *)
let get_type_def (defs: definitions) (xtor: Path.t) : (ty_def * kind) =
  match List.assoc_opt xtor defs.type_defs with
  | Some def -> def
  | None -> error ("undefined type symbol: " ^ Path.name xtor)

let get_xtor (defs: definitions) (sym: Path.t) : ty_xtor =
  let rec find_in_defs defs_list =
    match defs_list with
    | [] -> error ("undefined constructor/destructor: " ^ Path.name sym)
    | (_, (ty_def, _)) :: rest ->
      match ty_def with
      | Data td | Code td ->
        (match List.find_opt (fun x -> Path.equal x.symbol sym) td.xtors with
        | Some xtor -> xtor
        | None -> find_in_defs rest)
      | Prim _ -> find_in_defs rest
  in
  find_in_defs defs.type_defs

let rec check_statement
    (defs: definitions) (ctx: Context.t)
    (s: statement) (ty: Type.t) =
  match s with
  | Cut (p, c) ->
    check_producer defs ctx p ty |> ignore;
    check_consumer defs ctx c ty |> ignore;
    ctx

and check_producer
    (defs: definitions) (ctx: Context.t)
    (p: producer) (ty: Type.t) =
  match p with
  | Mu (u, s) ->
    let ctx_extended = Context.add (u, Cns ty) ctx in
    check_statement defs ctx_extended s ty |> ignore;
    ctx

  | Cocase ptss ->
    (match ty with
    | TyDef (Code td) ->
      (* Check each pattern/cocase *)
      List.iter (fun (pat: pattern) ->
        let xtor = get_xtor defs pat.xtor in
        
        (* Check this xtor belongs to the codata type *)
        if not (Path.equal xtor.parent td.symbol) then
          error ("destructor " ^ Path.name pat.xtor ^ " does not belong to type " ^ Path.name td.symbol);
        
        (* Check type variable count *)
        if List.length pat.type_vars <> List.length xtor.quantified then
          error ("pattern for " ^ Path.name pat.xtor ^ " has wrong number of type variables");
        
        (* Build type substitution *)
        let ty_subst = List.fold_left2 (fun acc tv (qv, _) ->
          Ident.add qv (TyVar tv) acc
        ) Ident.emptytbl pat.type_vars xtor.quantified in
        
        (* Apply substitution to get actual types *)
        let prod_tys = List.map (Type.subst ty_subst) xtor.producers in
        let cons_tys = List.map (Type.subst ty_subst) xtor.consumers in
        
        (* Check argument counts *)
        if List.length pat.variables <> List.length prod_tys then
          error ("pattern for " ^ Path.name pat.xtor ^ " has wrong number of variables");
        if List.length pat.covariables <> List.length cons_tys then
          error ("pattern for " ^ Path.name pat.xtor ^ " has wrong number of covariables");
        
        (* Extend context with pattern bindings *)
        let ctx' = List.fold_left2 (fun acc var ty ->
          Context.add (var, Prd ty) acc
        ) ctx pat.variables prod_tys in
        let ctx'' = List.fold_left2 (fun acc covar ty ->
          Context.add (covar, Cns ty) acc
        ) ctx' pat.covariables cons_tys in
        
        (* Check the body statement *)
        check_statement defs ctx'' pat.statement ty |> ignore
      ) ptss;
      
      (* Check exhaustivity: all destructors covered *)
      let covered = List.map (fun (pat: pattern) -> pat.xtor) ptss in
      List.iter (fun (xtor: ty_xtor) ->
        if not (List.exists (Path.equal xtor.symbol) covered) then
          error ("missing cocase for destructor " ^ Path.name xtor.symbol)
      ) td.xtors;
      
      (* Check no duplicates *)
      let rec check_dups seen = function
        | [] -> ()
        | pat :: rest ->
          if List.exists (Path.equal pat.xtor) seen then
            error ("duplicate cocase for destructor " ^ Path.name pat.xtor)
          else
            check_dups (pat.xtor :: seen) rest
      in
      check_dups [] ptss;
      
      ctx
      
    | _ -> error "cocase used on non-codata type")

  | _ ->
    let p_g, p_ty = infer_producer defs ctx p in
    if Type.equivalent defs.type_defs p_ty ty then p_g
    else error "producer type mismatch"

and check_consumer
    (defs: definitions) (ctx: Context.t)
    (c: consumer) (ty: Type.t) =
  match c with
  | MuTilde (x, s) ->
    let ctx_extended = Context.add (x, Prd ty) ctx in
    check_statement defs ctx_extended s ty |> ignore;
    ctx

  | Case ptss ->
    (match ty with
    | TyDef (Data td) ->
      (* Check each pattern/case *)
      List.iter (fun (pat: pattern) ->
        let xtor = get_xtor defs pat.xtor in
        
        (* Check this xtor belongs to the data type *)
        if not (Path.equal xtor.parent td.symbol) then
          error ("constructor " ^ Path.name pat.xtor ^ " does not belong to type " ^ Path.name td.symbol);
        
        (* Check type variable count *)
        if List.length pat.type_vars <> List.length xtor.quantified then
          error ("pattern for " ^ Path.name pat.xtor ^ " has wrong number of type variables");
        
        (* Build type substitution *)
        let ty_subst = List.fold_left2 (fun acc tv (qv, _) ->
          Ident.add qv (TyVar tv) acc
        ) Ident.emptytbl pat.type_vars xtor.quantified in
        
        (* Apply substitution to get actual types *)
        let prod_tys = List.map (Type.subst ty_subst) xtor.producers in
        let cons_tys = List.map (Type.subst ty_subst) xtor.consumers in
        
        (* Check argument counts *)
        if List.length pat.variables <> List.length prod_tys then
          error ("pattern for " ^ Path.name pat.xtor ^ " has wrong number of variables");
        if List.length pat.covariables <> List.length cons_tys then
          error ("pattern for " ^ Path.name pat.xtor ^ " has wrong number of covariables");
        
        (* Extend context with pattern bindings *)
        let ctx' = List.fold_left2 (fun acc var ty ->
          Context.add (var, Prd ty) acc
        ) ctx pat.variables prod_tys in
        let ctx'' = List.fold_left2 (fun acc covar ty ->
          Context.add (covar, Cns ty) acc
        ) ctx' pat.covariables cons_tys in
        
        (* Check the body statement *)
        check_statement defs ctx'' pat.statement ty |> ignore
      ) ptss;
      
      (* Check exhaustivity: all constructors covered *)
      let covered = List.map (fun (pat: pattern) -> pat.xtor) ptss in
      List.iter (fun (xtor: ty_xtor) ->
        if not (List.exists (Path.equal xtor.symbol) covered) then
          error ("missing case for constructor " ^ Path.name xtor.symbol)
      ) td.xtors;
      
      (* Check no duplicates *)
      let rec check_dups seen = function
        | [] -> ()
        | pat :: rest ->
          if List.exists (Path.equal pat.xtor) seen then
            error ("duplicate case for constructor " ^ Path.name pat.xtor)
          else
            check_dups (pat.xtor :: seen) rest
      in
      check_dups [] ptss;
      
      ctx

    | _ -> error "case used on non-data type")

  | _ ->
    let c_g, c_ty = infer_consumer defs ctx c in
    if Type.equivalent defs.type_defs c_ty ty then c_g
    else error "consumer type mismatch"

and infer_statement
    (defs: definitions) (ctx: Context.t)
    (s: statement) =
  match s with
  | Cut (p, c) ->
    try
      let _, p_ty = infer_producer defs ctx p in
      check_consumer defs ctx c p_ty |> ignore;
    with _ ->
      try
        let _, c_ty = infer_consumer defs ctx c in
        check_producer defs ctx p c_ty |> ignore;
      with _ ->
        error "cannot infer cut type";

and infer_producer
    (defs: definitions) (ctx: Context.t)
    (p: producer) =
  match p with
  | Int _ ->
    (ctx, CT.Prim.int_typ)
  | Var x ->
    (match Context.lookup_chirality x ctx with
    | Some (Prd ty) -> ctx, ty
    | Some (Cns _) -> error ("variable has consumer type: " ^ (Ident.name x))
    | None -> error ("unbound variable: " ^ (Ident.name x)))
  
  | Mu _ -> error "cannot infer type of μ"

  | Constructor (ctor, (tys, ps, cs)) ->
    let ctor_dec = get_xtor defs ctor in
    let parent_def, _ = get_type_def defs ctor_dec.parent in
    (match parent_def with
    | Data _ ->
      (* Check we have the right number of type arguments *)
      if List.length tys <> List.length ctor_dec.quantified then
        error ("constructor " ^ Path.name ctor ^ " expects " ^
               string_of_int (List.length ctor_dec.quantified) ^
               " type arguments, got " ^ string_of_int (List.length tys));
      
      (* Build substitution from quantified variables to provided types *)
      let ty_subst = List.fold_left2 (fun acc (tv, _) ty ->
        Ident.add tv ty acc
      ) Ident.emptytbl ctor_dec.quantified tys in
      
      (* Apply substitution to producer and consumer types *)
      let prod_tys = List.map (Type.subst ty_subst) ctor_dec.producers in
      let cons_tys = List.map (Type.subst ty_subst) ctor_dec.consumers in
      
      (* Check producer arguments *)
      if List.length ps <> List.length prod_tys then
        error ("constructor " ^ Path.name ctor ^ " expects " ^
               string_of_int (List.length prod_tys) ^ " producer arguments");
      List.iter2 (fun p ty ->
        check_producer defs ctx p ty |> ignore
      ) ps prod_tys;
      
      (* Check consumer arguments *)
      if List.length cs <> List.length cons_tys then
        error ("constructor " ^ Path.name ctor ^ " expects " ^
               string_of_int (List.length cons_tys) ^ " consumer arguments");
      List.iter2 (fun c ty ->
        check_consumer defs ctx c ty |> ignore
      ) cs cons_tys;
      
      (* Build the result type: parent applied to instantiated arguments *)
      let arg_tys = List.map (Type.subst ty_subst) ctor_dec.arguments in
      let result_ty = List.fold_left (fun acc arg ->
        TyApp (acc, arg)
      ) (TySym ctor_dec.parent) arg_tys in
      
      (ctx, result_ty)
    | _ ->
      error ("constructor used on non-data type"))

  | Cocase _ -> error "Cannot infer type of cocase"
  
    
and infer_consumer
    (defs: definitions) (ctx: Context.t)
    (c: consumer) =
  match c with
  | Covar u ->
    (match Context.lookup_chirality u ctx with
    | Some (Cns ty) -> (ctx, ty)
    | Some (Prd _) -> error ("covariable " ^ (Ident.name u) ^ " has producer type")
    | None -> error ("unbound covariable: " ^ (Ident.name u)))

  | MuTilde _ -> error "cannot infer type of μ̃"

  | Destructor (dtor, (tys, ps, cs)) ->
    let dtor_dec = get_xtor defs dtor in
    let parent_def, _ = get_type_def defs dtor_dec.parent in
    (match parent_def with
    | Code _ ->
      (* Check we have the right number of type arguments *)
      if List.length tys <> List.length dtor_dec.quantified then
        error ("destructor " ^ Path.name dtor ^ " expects " ^
               string_of_int (List.length dtor_dec.quantified) ^
               " type arguments, got " ^ string_of_int (List.length tys));
      
      (* Build substitution from quantified variables to provided types *)
      let ty_subst = List.fold_left2 (fun acc (tv, _) ty ->
        Ident.add tv ty acc
      ) Ident.emptytbl dtor_dec.quantified tys in
      
      (* Apply substitution to producer and consumer types *)
      let prod_tys = List.map (Type.subst ty_subst) dtor_dec.producers in
      let cons_tys = List.map (Type.subst ty_subst) dtor_dec.consumers in
      
      (* Check producer arguments *)
      if List.length ps <> List.length prod_tys then
        error ("destructor " ^ Path.name dtor ^ " expects " ^
               string_of_int (List.length prod_tys) ^ " producer arguments");
      List.iter2 (fun p ty ->
        check_producer defs ctx p ty |> ignore
      ) ps prod_tys;
      
      (* Check consumer arguments *)
      if List.length cs <> List.length cons_tys then
        error ("destructor " ^ Path.name dtor ^ " expects " ^
               string_of_int (List.length cons_tys) ^ " consumer arguments");
      List.iter2 (fun c ty ->
        check_consumer defs ctx c ty |> ignore
      ) cs cons_tys;
      
      (* Build the result type: parent applied to instantiated arguments *)
      let arg_tys = List.map (Type.subst ty_subst) dtor_dec.arguments in
      let result_ty = List.fold_left (fun acc arg ->
        TyApp (acc, arg)
      ) (TySym dtor_dec.parent) arg_tys in
      
      (ctx, result_ty)
    | _ ->
      error "destructor used on non-codata type")
  
  | Case _ -> error "Cannot infer type of case"
