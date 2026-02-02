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
    | Prd ty -> "prd " ^ Type.to_string ty
    | Cns ty -> "cns " ^ Type.to_string ty
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
  
  let add_with_kind (x, ch, k: (Ident.t * chirality * kind)) (ctx: t) =
    { kinds = Ident.add x k ctx.kinds
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
  | Cut of producer * Type.t * consumer
  | Call of Path.t * (Type.t list) * (producer list) * (consumer list)
  | Add of producer * producer * consumer

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

(** Pretty-printing for Core terms *)

(* Helper for indentation *)
let indent (n: int) : string = String.make (n * 2) ' '

(* Pretty-print type arguments *)
let type_args_to_string (tys: Type.t list) : string =
  if tys = [] then ""
  else "{" ^ String.concat ", " (List.map Type.to_string tys) ^ "}"

(* Pretty-print identifiers *)
let idents_to_string (ids: Ident.t list) : string =
  String.concat ", " (List.map Ident.name ids)

(* Pretty-print xtor arguments *)
let xtor_args_to_string (ty_args, prods, cons: xtor_args) : string =
  let parts = [] in
  let parts = if ty_args <> [] then 
    (type_args_to_string ty_args) :: parts 
  else parts in
  let parts = if prods <> [] then
    ("(" ^ String.concat ", " (List.map (fun _ -> "_") prods) ^ ")") :: parts
  else parts in
  let parts = if cons <> [] then
    ("(" ^ String.concat ", " (List.map (fun _ -> "_") cons) ^ ")") :: parts
  else parts in
  String.concat "" (List.rev parts)

(* Pretty-print statement *)
let rec statement_to_string ?(depth=0) (s: statement) : string =
  match s with
  | Cut (p, _, c) ->
    "⟨" ^ producer_to_string ~depth p ^ " | " ^ 
    consumer_to_string ~depth c ^ "⟩"
  
  | Add (p1, p2, c) ->
    "add(" ^ producer_to_string ~depth p1 ^ ", " ^
    producer_to_string ~depth p2 ^ ", " ^
    consumer_to_string ~depth c ^ ")"
  
  | Call (f, ty_args, prods, cons) ->
    let f_name = Path.name f in
    let ty_str = type_args_to_string ty_args in
    let ps = List.map (producer_to_string ~depth) prods in
    let prod_str = if ps = [] then "()" else "(" ^ String.concat ", " ps ^ ")" in
    let cs = List.map (consumer_to_string ~depth) cons in
    let cons_str = if cs = [] then "()" else "(" ^ String.concat ", " cs ^ ")" in
    let args_str = prod_str ^ cons_str in
    f_name ^ ty_str ^ args_str

(* Pretty-print producer *)
and producer_to_string ?(depth=0) (p: producer) : string =
  match p with
  | Int n -> string_of_int n
  
  | Var x -> Ident.name x
  
  | Mu (x, s) ->
    let s_str = statement_to_string ~depth:(depth+1) s in
    "μ" ^ Ident.name x ^ "." ^ s_str
  
  | Constructor (xtor, (ty_args, prods, cons)) ->
    let xtor_name = Path.name xtor in
    let ty_str = type_args_to_string ty_args in
    let prod_strs = List.map (producer_to_string ~depth) prods in
    let cons_strs = List.map (consumer_to_string ~depth) cons in
    let args = prod_strs @ cons_strs in
    let args_str = if args = [] then "()" else "(" ^ String.concat ", " args ^ ")" in
    xtor_name ^ ty_str ^ args_str
  
  | Cocase patterns ->
    if patterns = [] then "new {}"
    else
      let pattern_strs = List.map (fun pat ->
        pattern_to_string ~depth pat
      ) patterns in
      if List.length patterns = 1 then
        "new { " ^ List.hd pattern_strs ^ " }"
      else
        "new {\n" ^ 
        String.concat "\n" (List.map (fun s -> indent (depth+1) ^ s) pattern_strs) ^
        "\n" ^ indent depth ^ "}"

(* Pretty-print consumer *)
and consumer_to_string ?(depth=0) (c: consumer) : string =
  match c with
  | Covar x -> Ident.name x
  
  | MuTilde (x, s) ->
    let s_str = statement_to_string ~depth:(depth+1) s in
    "μ̃" ^ Ident.name x ^ "." ^ s_str
  
  | Destructor (xtor, (ty_args, prods, cons)) ->
    let xtor_name = Path.name xtor in
    let ty_str = type_args_to_string ty_args in
    let prod_strs = List.map (producer_to_string ~depth) prods in
    let cons_strs = List.map (consumer_to_string ~depth) cons in
    let args = prod_strs @ cons_strs in
    let args_str = if args = [] then "()" else "(" ^ String.concat ", " args ^ ")" in
    xtor_name ^ ty_str ^ args_str
  
  | Case patterns ->
    if patterns = [] then "case {}"
    else
      let pattern_strs = List.map (fun pat ->
        pattern_to_string ~depth pat
      ) patterns in
      if List.length patterns = 1 then
        "case { " ^ List.hd pattern_strs ^ " }"
      else
        "case {\n" ^ 
        String.concat "\n" (List.map (fun s -> indent (depth+1) ^ s) pattern_strs) ^
        "\n" ^ indent depth ^ "}"

(* Pretty-print pattern *)
and pattern_to_string ?(depth=0) (pat: pattern) : string =
  let xtor_name = Path.name pat.xtor in
  let ty_str = if pat.type_vars = [] then "" 
    else "{" ^ idents_to_string pat.type_vars ^ "}" in
  let var_str = if pat.variables = [] then ""
    else "(" ^ idents_to_string pat.variables ^ ")" in
  let covar_str = if pat.covariables = [] then ""
    else "(" ^ idents_to_string pat.covariables ^ ")" in
  let args_str = ty_str ^ var_str ^ covar_str in
  let stmt_str = statement_to_string ~depth:(depth+1) pat.statement in
  xtor_name ^ args_str ^ " => " ^ stmt_str

(* Pretty-print expression *)
let expression_to_string ?(depth=0) (e: expression) : string =
  match e with
  | Pro p -> producer_to_string ~depth p
  | Con c -> consumer_to_string ~depth c

(* Pretty-print term definition *)
let term_def_to_string (td: term_def) : string =
  let name = Path.name td.name in
  let ty_args_str = if td.type_args = [] then ""
    else "{" ^ String.concat ", " (List.map (fun (x, k) ->
      Ident.name x ^ ": " ^ Kind.to_string k
    ) td.type_args) ^ "}" in
  let prod_args_str = if td.prod_args = [] then ""
    else "(" ^ String.concat ", " (List.map (fun (x, ty) ->
      Ident.name x ^ ": " ^ Type.to_string ty
    ) td.prod_args) ^ ")" in
  let cons_args_str = if td.cons_args = [] then ""
    else "(" ^ String.concat ", " (List.map (fun (x, ty) ->
      Ident.name x ^ ": cns " ^ Type.to_string ty
    ) td.cons_args) ^ ")" in
  let args_str = ty_args_str ^ prod_args_str ^ cons_args_str in
  let ret_str = Type.to_string td.return_type in
  let body_str = statement_to_string ~depth:1 td.body in
  name ^ args_str ^ ": " ^ ret_str ^ " =\n  " ^ body_str

(* Helper functions to look up type definitions and xtors *)
let get_type_def (defs: definitions) (xtor: Path.t) : (ty_def * kind) =
  match List.assoc_opt xtor defs.type_defs with
  | Some def -> def
  | None -> error ("undefined type symbol: " ^ Path.name xtor)

(* Check if a destructor symbol is the primitive $inst{k} for some kind k *)
let is_inst_destructor (sym: Path.t) : kind option =
  match Path.as_ident sym with
  | Some id ->
    let stamp = Ident.stamp id in
    (* $inst{k} has stamp -(1 + to_int k), where to_int k >= 100 and even *)
    if stamp < -100 && (-stamp) mod 2 = 1 then
      (* It's potentially $inst{k} - decode the kind *)
      Some (CT.Prim.of_int (-stamp - 1))
    else
      None
  | None -> None

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
  | Cut (p, t, c) ->
    if not (Type.equivalent defs.type_defs t ty) then
      error ("Cut type mismatch: expected " ^ Type.to_string ty ^
             ", got " ^ Type.to_string t);
    check_producer defs ctx p ty |> ignore;
    check_consumer defs ctx c ty |> ignore;
    ctx
  | Add (p1, p2, c) ->
    (* Check both producers are int type *)
    check_producer defs ctx p1 CT.Prim.int_typ |> ignore;
    check_producer defs ctx p2 CT.Prim.int_typ |> ignore;
    (* Check consumer is int type *)
    check_consumer defs ctx c CT.Prim.int_typ |> ignore;
    ctx
  | Call (sym, ty_args, prods, cons) ->
    (* Look up the function definition to get its type *)
    let def = 
      match List.find_opt (fun (_, td) -> Path.equal td.name sym) defs.term_defs with
      | Some (_, d) -> d
      | None -> error ("Undefined function: " ^ Path.name sym)
    in
    (* Check we have the right number of type arguments *)
    if List.length ty_args <> List.length def.type_args then
      error ("Function " ^ Path.name sym ^ " expects " ^
             string_of_int (List.length def.type_args) ^
             " type arguments, got " ^ string_of_int (List.length ty_args));
    (* Build type substitution *)
    let ty_subst = List.fold_left2 (fun acc (tv, _) ty ->
      Ident.add tv ty acc
    ) Ident.emptytbl def.type_args ty_args in
    (* Check producer arguments with substituted types *)
    List.iter2 (fun prod (_, arg_ty) ->
      let instantiated_ty = Type.subst ty_subst arg_ty in
      check_producer defs ctx prod instantiated_ty |> ignore
    ) prods def.prod_args;
    (* Check consumer arguments with substituted types *)
    List.iter2 (fun cons (_, arg_ty) ->
      let instantiated_ty = Type.subst ty_subst arg_ty in
      check_consumer defs ctx cons instantiated_ty |> ignore
    ) cons def.cons_args;
    ctx

and check_producer
    (defs: definitions) (ctx: Context.t)
    (p: producer) (ty: Type.t) =
  match p with
  | Mu (u, s) ->
    let ctx_extended = Context.add (u, Cns ty) ctx in
    infer_statement defs ctx_extended s;  (* Infer, don't check against ty *)
    ctx

  | Cocase ptss ->
    let ty_normalized = Type.reduce defs.type_defs ty in
    (match ty_normalized with
    | TyDef (Code td) ->
      (* Check each pattern/cocase *)
      List.iter (fun (pat: pattern) ->
        (* Find the xtor in the instantiated type declaration td, not globally *)
        let xtor = match List.find_opt (fun x -> Path.equal x.symbol pat.xtor) td.xtors with
          | Some x -> x
          | None -> error ("destructor " ^ Path.name pat.xtor ^ " not found in type " ^ Path.name td.symbol)
        in
          
          (* Check type variable count *)
          if List.length pat.type_vars <> List.length xtor.quantified then
            error ("pattern for " ^ Path.name pat.xtor ^ " has wrong number of type variables");
          
          (* Apply constraints from type instantiation first *)
          let initial_subst = match xtor.constraints with
            | None -> Ident.emptytbl
            | Some constraints ->
              List.fold_left (fun acc (qv, ty) ->
                Ident.add qv ty acc
              ) Ident.emptytbl constraints
          in
          
          (* Then map remaining quantified vars to pattern type vars *)
          let ty_subst = List.fold_left2 (fun acc tv (qv, _) ->
            match Ident.find_opt qv acc with
            | Some _ -> acc  (* Already constrained, keep it *)
            | None -> Ident.add qv (TyVar tv) acc
          ) initial_subst pat.type_vars xtor.quantified in
          
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
          
          (* Check the body statement - just ensure it type checks *)
          infer_statement defs ctx'' pat.statement
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
      
    | TyVar _ ->
      (* Type variable - skip checking, we can't verify constructors/destructors *)
      (* Just check the pattern bodies with the type variable in scope *)
      List.iter (fun (pat: pattern) ->
        (* Add type variables from pattern to context *)
        let ctx' = List.fold_left (fun acc tv ->
          { Context.kinds = Ident.add tv Common.Types.KStar acc.Context.kinds
          ; Context.chiralities = acc.Context.chiralities
          }
        ) ctx pat.type_vars in
        
        (* Add variables and covariables to context *)
        let ctx'' = List.fold_left (fun acc var ->
          Context.add (var, Prd ty) acc
        ) ctx' pat.variables in
        let ctx''' = List.fold_left (fun acc covar ->
          Context.add (covar, Cns ty) acc
        ) ctx'' pat.covariables in
        
        (* Check the body statement - just ensure it type checks *)
        infer_statement defs ctx''' pat.statement
      ) ptss;
      ctx
      
    | _ -> 
      let ty_str = Type.to_string ty_normalized in
      error ("cocase used on non-codata type: " ^ ty_str))

  | _ ->
    let p_g, p_ty = infer_producer defs ctx p in
    if Type.equivalent defs.type_defs p_ty ty then p_g
    else error ("producer type mismatch: expected " ^ Type.to_string ty ^ ", got " ^ Type.to_string p_ty)

and check_consumer
    (defs: definitions) (ctx: Context.t)
    (c: consumer) (ty: Type.t) =
  match c with
  | MuTilde (x, s) ->
    let ctx_extended = Context.add (x, Prd ty) ctx in
    check_statement defs ctx_extended s ty |> ignore;
    ctx

  | Case ptss ->
    let ty_normalized = Type.reduce defs.type_defs ty in
    (match ty_normalized with
    | TyDef (Data td) ->
      (* Check each pattern/case *)
      List.iter (fun (pat: pattern) ->
        (* Find the xtor in the instantiated type declaration td, not globally *)
        let xtor = match List.find_opt (fun x -> Path.equal x.symbol pat.xtor) td.xtors with
          | Some x -> x
          | None -> error ("constructor " ^ Path.name pat.xtor ^ " not found in type " ^ Path.name td.symbol)
        in
        
        (* Check type variable count *)
        if List.length pat.type_vars <> List.length xtor.quantified then
          error ("pattern for " ^ Path.name pat.xtor ^ " has wrong number of type variables");
        
        (* Apply constraints from type instantiation first *)
        let initial_subst = match xtor.constraints with
          | None -> Ident.emptytbl
          | Some constraints ->
            List.fold_left (fun acc (qv, ty) ->
              Ident.add qv ty acc
            ) Ident.emptytbl constraints
        in
        
        (* Then map remaining quantified vars to pattern type vars *)
        let ty_subst = List.fold_left2 (fun acc tv (qv, _) ->
          match Ident.find_opt qv acc with
          | Some _ -> acc  (* Already constrained, keep it *)
          | None -> Ident.add qv (TyVar tv) acc
        ) initial_subst pat.type_vars xtor.quantified in
        
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
        
        (* Check the body statement - just ensure it type checks *)
        infer_statement defs ctx'' pat.statement
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
    else 
      let c_ty_str = Type.to_string c_ty in
      let ty_str = Type.to_string ty in
      let c_str = match c with | Covar x -> "covar " ^ Ident.name x | _ -> "consumer" in
      error ("consumer type mismatch for " ^ c_str ^ ": expected " ^ ty_str ^ ", got " ^ c_ty_str)

and infer_statement
    (defs: definitions) (ctx: Context.t)
    (s: statement) =
  match s with
  | Cut (p, ty, c) ->
    check_producer defs ctx p ty |> ignore;
    check_consumer defs ctx c ty |> ignore;
  | Add (p1, p2, c) ->
    (* Check both producers are int type *)
    check_producer defs ctx p1 CT.Prim.int_typ |> ignore;
    check_producer defs ctx p2 CT.Prim.int_typ |> ignore;
    (* Check consumer is int type *)
    check_consumer defs ctx c CT.Prim.int_typ |> ignore;
  | Call (sym, ty_args, prods, cons) ->
    (* Look up the function definition to get its type *)
    let def = 
      match List.find_opt (fun (_, td) -> Path.equal td.name sym) defs.term_defs with
      | Some (_, d) -> d
      | None -> error ("Undefined function: " ^ Path.name sym)
    in
    (* Check we have the right number of type arguments *)
    if List.length ty_args <> List.length def.type_args then
      error ("Function " ^ Path.name sym ^ " expects " ^
             string_of_int (List.length def.type_args) ^
             " type arguments, got " ^ string_of_int (List.length ty_args));
    (* Build type substitution *)
    let ty_subst = List.fold_left2 (fun acc (tv, _) ty ->
      Ident.add tv ty acc
    ) Ident.emptytbl def.type_args ty_args in
    (* Check producer arguments with substituted types *)
    List.iter2 (fun prod (_, arg_ty) ->
      let instantiated_ty = Type.subst ty_subst arg_ty in
      check_producer defs ctx prod instantiated_ty |> ignore
    ) prods def.prod_args;
    (* Check consumer arguments with substituted types *)
    List.iter2 (fun cons (_, arg_ty) ->
      let instantiated_ty = Type.subst ty_subst arg_ty in
      check_consumer defs ctx cons instantiated_ty |> ignore
    ) cons def.cons_args;

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

(* Check a term definition *)
let check_term_def (defs: definitions) (td: term_def) : unit =
  (* Build context with type parameters *)
  let ctx = List.fold_left (fun acc (tv, k) ->
    { Context.kinds = Ident.add tv k acc.Context.kinds
    ; Context.chiralities = acc.Context.chiralities
    }
  ) Context.empty td.type_args in
  
  (* Add producer arguments to context *)
  let ctx = List.fold_left (fun acc (x, ty) ->
    Context.add (x, Prd ty) acc
  ) ctx td.prod_args in
  
  (* Add consumer arguments to context *)
  let ctx = List.fold_left (fun acc (x, ty) ->
    Context.add (x, Cns ty) acc
  ) ctx td.cons_args in
  
  (* Check the body statement with the return type *)
  check_statement defs ctx td.body td.return_type |> ignore

(* Check all term definitions *)
let check_definitions (defs: definitions) : unit =
  List.iter (fun (_, td) ->
    check_term_def defs td
  ) defs.term_defs
