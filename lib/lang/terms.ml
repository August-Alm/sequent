(**
  Module: Lang.Terms
  Description: Terms of the surface language.
*)

open Common.Identifiers
open Types


type term =
  (* n *)
  | TmInt of int
  (* x *)
  | TmVar of Ident.t
  (* name *)
  | TmSym of Path.t
  (* t(u) *)
  | TmApp of term * term
  (* t{ty} *)
  | TmIns of term * typ
  (* fun x => t or fun(x: a) => t *)
  | TmLam of Ident.t * (typ option) * term
  (* all {a: k} t *)
  | TmAll of (Ident.t * kind) * term
  (* let x = t in u *)
  | TmLet of Ident.t * term * term
  (* match t with { clauses } *)
  | TmMatch of term * (clause list)
  (* new { clauses } or new ty { clauses }*)
  | TmNew of (typ option) * (clause list)
  (* ctor{ai's}(ti's); type and term arguments *)
  | TmCtor of ty_xtor * (typ list) * (term list)
  (* dtor{ai's}(ti's); type and term arguments *)
  | TmDtor of ty_xtor * (typ list) * (term list)

and clause =
  (* xtor{ai's}(ti's) => t; type and term arguments, and return *)
  ty_xtor * (Ident.t list) * (Ident.t list) * term

(* Typed terms: AST with type annotations *)
type typed_term =
  | TyTmInt of int * typ
  | TyTmVar of Ident.t * typ
  | TyTmSym of Path.t * typ
  | TyTmApp of typed_term * typed_term * typ
  | TyTmIns of typed_term * typ * kind * typ  (* term, type arg, kind, result type *)
  | TyTmLam of Ident.t * typ * typed_term * typ  (* x, arg type, body, function type *)
  | TyTmAll of (Ident.t * kind) * typed_term * typ
  | TyTmLet of Ident.t * typed_term * typed_term * typ
  | TyTmMatch of typed_term * typed_clause list * typ
  | TyTmNew of typ option * typed_clause list * typ
  | TyTmCtor of ty_xtor * typ list * typed_term list * typ
  | TyTmDtor of ty_xtor * typ list * typed_term list * typ

and typed_clause =
  ty_xtor * Ident.t list * Ident.t list * typed_term

let get_type (tm: typed_term) : typ =
  match tm with
  | TyTmInt (_, ty) -> ty
  | TyTmVar (_, ty) -> ty
  | TyTmSym (_, ty) -> ty
  | TyTmApp (_, _, ty) -> ty
  | TyTmIns (_, _, _, ty) -> ty
  | TyTmLam (_, _, _, ty) -> ty
  | TyTmAll (_, _, ty) -> ty
  | TyTmLet (_, _, _, ty) -> ty
  | TyTmMatch (_, _, ty) -> ty
  | TyTmNew (_, _, ty) -> ty
  | TyTmCtor (_, _, _, ty) -> ty
  | TyTmDtor (_, _, _, ty) -> ty

type term_def =
  { name: Path.t
  ; type_args: (Ident.t * kind) list
  ; term_args: (Ident.t * typ) list
  ; return_type: typ
  ; body: term
  }

type typed_term_def =
  { name: Path.t
  ; type_args: (Ident.t * kind) list
  ; term_args: (Ident.t * typ) list
  ; return_type: typ
  ; body: typed_term
  }

type definitions =
  { type_defs: ty_defs
  ; term_defs: (Path.t * term_def) list
  }

type typed_definitions =
  { type_defs: ty_defs
  ; term_defs: (Path.t * typed_term_def) list
  }

type context =
  { kinds: kind Ident.tbl
  ; types: typ Ident.tbl
  }

let rec infer_typ (defs: definitions) (ctx: context) (tm: term) : typ * typed_term =
  match tm with
  | TmInt n -> 
    let ty = Prim.int_typ in
    (ty, TyTmInt (n, ty))
    
  | TmVar x ->
    (match Ident.find_opt x ctx.types with
    | Some ty -> (ty, TyTmVar (x, ty))
    | None -> failwith ("unbound variable: " ^ Ident.name x))

  | TmSym path ->
    (* Look up the top-level definition and construct its type *)
    (match List.find_opt (fun (p, _) -> Path.equal p path) defs.term_defs with
    | None -> failwith ("undefined symbol: " ^ Path.name path)
    | Some (_, td) ->
      (* Build function type from term arguments to return type *)
      let func_ty = List.fold_right (fun (_, arg_ty) ret_ty ->
        TyFun (arg_ty, ret_ty)
      ) td.term_args td.return_type in
      (* Wrap with universal quantifiers for type arguments *)
      let ty = List.fold_right (fun (type_var, kind) body_ty ->
        TyAll ((type_var, kind), body_ty)
      ) td.type_args func_ty in
      (ty, TyTmSym (path, ty)))

  | TmApp (t, u) ->
    (* Infer the type of the function *)
    let t_ty, t_typed = infer_typ defs ctx t in
    (* Reduce to check if it's a function type *)
    (match reduce defs.type_defs t_ty with
    | TyFun (ty_arg, ty_ret) ->
      (* Check the argument has the expected type *)
      let u_typed = check_typ defs ctx u ty_arg in
      (* Return the result type *)
      (ty_ret, TyTmApp (t_typed, u_typed, ty_ret))
    | _ -> failwith "application expects a function type")

  | TmCtor (ctor, ty_args, tm_args) ->
    (* Allow partial application: verify we have at most the expected number of arguments *)
    let n_quantified = List.length ctor.quantified in
    let n_ty_args = List.length ty_args in
    if n_ty_args > n_quantified then
      failwith ("constructor " ^ Path.name ctor.symbol ^
        " expects at most " ^ string_of_int n_quantified ^
        " type arguments but got " ^ string_of_int n_ty_args);
    
    let n_sources = List.length ctor.sources in
    let n_tm_args = List.length tm_args in
    if n_tm_args > n_sources then
      failwith ("constructor " ^ Path.name ctor.symbol ^
        " expects at most " ^ string_of_int n_sources ^
        " arguments but got " ^ string_of_int n_tm_args);
    
    (* Apply constraints from GADT normalization first *)
    let constraint_subst = 
      match ctor.constraints with
      | None -> Ident.emptytbl
      | Some constraints -> 
        List.fold_left (fun acc (var, ty) ->
          Ident.add var ty acc
        ) Ident.emptytbl constraints
    in
    
    (* Split quantified variables into provided and remaining *)
    let provided_quantified, remaining_quantified = 
      let rec split n xs = 
        if n = 0 then [], xs
        else match xs with
        | [] -> [], []
        | x :: xs' -> let provided, remaining = split (n - 1) xs' in x :: provided, remaining
      in split n_ty_args ctor.quantified
    in
    
    (* Build substitution from provided type arguments, on top of constraints *)
    let ty_subst = List.fold_left2 (fun acc (x, _) ty_arg ->
      Ident.add x ty_arg acc
    ) constraint_subst provided_quantified ty_args in
    
    (* Instantiate source types with the partial substitution *)
    let inst_sources = List.map (subst ty_subst) ctor.sources in
    
    (* Split sources into provided and remaining *)
    let provided_sources, remaining_sources =
      let rec split n xs =
        if n = 0 then [], xs
        else match xs with
        | [] -> [], []
        | x :: xs' -> let provided, remaining = split (n - 1) xs' in x :: provided, remaining
      in split n_tm_args inst_sources
    in
    
    (* Check each provided term argument against its corresponding source type *)
    let tm_args_typed = List.map2 (check_typ defs ctx) tm_args provided_sources in
    
    (* Build the base result type by applying parent to instantiated arguments *)
    let inst_arguments = List.map (subst ty_subst) ctor.arguments in
    let base_result_ty = 
      List.fold_left (fun acc arg -> TyApp (acc, arg))
        (TySym ctor.parent) inst_arguments
    in
    
    (* Build function type for remaining term arguments *)
    let result_with_remaining_args = 
      List.fold_right (fun source_ty acc -> TyFun (source_ty, acc))
        remaining_sources base_result_ty
    in
    
    (* Wrap with universal quantification for remaining type variables *)
    let final_result =
      List.fold_right (fun (x, k) acc -> TyAll ((x, k), acc))
        remaining_quantified result_with_remaining_args
    in
    
    (final_result, TyTmCtor (ctor, ty_args, tm_args_typed, final_result))

  | TmDtor (dtor, ty_args, tm_args) ->
    (* Allow partial application: verify we have at most the expected number of arguments *)
    let n_quantified = List.length dtor.quantified in
    let n_ty_args = List.length ty_args in
    if n_ty_args > n_quantified then
      failwith ("destructor " ^ Path.name dtor.symbol ^
        " expects at most " ^ string_of_int n_quantified ^
        " type arguments but got " ^ string_of_int n_ty_args);
    
    let n_sources = List.length dtor.sources in
    let n_tm_args = List.length tm_args in
    if n_tm_args > n_sources then
      failwith ("destructor " ^ Path.name dtor.symbol ^
        " expects at most " ^ string_of_int n_sources ^
        " arguments but got " ^ string_of_int n_tm_args);
    
    (* Apply constraints from GADT normalization first *)
    let constraint_subst = 
      match dtor.constraints with
      | None -> Ident.emptytbl
      | Some constraints -> 
        List.fold_left (fun acc (var, ty) ->
          Ident.add var ty acc
        ) Ident.emptytbl constraints
    in
    
    (* Split quantified variables into provided and remaining *)
    let provided_quantified, remaining_quantified = 
      let rec split n xs = 
        if n = 0 then [], xs
        else match xs with
        | [] -> [], []
        | x :: xs' -> let provided, remaining = split (n - 1) xs' in x :: provided, remaining
      in split n_ty_args dtor.quantified
    in
    
    (* Build substitution from provided type arguments, on top of constraints *)
    let ty_subst = List.fold_left2 (fun acc (x, _) ty_arg ->
      Ident.add x ty_arg acc
    ) constraint_subst provided_quantified ty_args in
    
    (* Instantiate source types with the partial substitution *)
    let inst_sources = List.map (subst ty_subst) dtor.sources in
    
    (* split inst_sources into init (all except last) and last (return type) *)
    let rec split_last lst =
      match lst with
      | [] -> failwith "expected at least one source type"
      | [x] -> [], x
      | x :: xs -> let init, last = split_last xs in x :: init, last
    in
    let inst_arg_sources, inst_return = split_last inst_sources in
    
    (* Split arg sources into provided and remaining *)
    let provided_arg_sources, remaining_arg_sources =
      let rec split n xs =
        if n = 0 then [], xs
        else match xs with
        | [] -> [], []
        | x :: xs' -> let provided, remaining = split (n - 1) xs' in x :: provided, remaining
      in split n_tm_args inst_arg_sources
    in
    
    (* Check each provided term argument against its corresponding source type *)
    let tm_args_typed = List.map2 (check_typ defs ctx) tm_args provided_arg_sources in
    
    (* Build function type for remaining term arguments, ending with return type *)
    let result_with_remaining_args = 
      List.fold_right (fun source_ty acc -> TyFun (source_ty, acc))
        remaining_arg_sources inst_return
    in
    
    (* Wrap with universal quantification for remaining type variables *)
    let final_result =
      List.fold_right (fun (x, k) acc -> TyAll ((x, k), acc))
        remaining_quantified result_with_remaining_args
    in
    
    (final_result, TyTmDtor (dtor, ty_args, tm_args_typed, final_result))

  | TmLam (x, ty_opt, body) ->
    (match ty_opt with
    | None -> failwith "cannot infer type of unannotated lambda"
    | Some ty_arg ->
        let ctx' = {ctx with types = Ident.add x ty_arg ctx.types} in
        let ty_body, body_typed = infer_typ defs ctx' body in
        let ty = TyFun (ty_arg, ty_body) in
        (ty, TyTmLam (x, ty_arg, body_typed, ty)))

  | TmAll ((a, k), body) ->
    (* Extend kind context with the bound type variable *)
    let ctx' = {ctx with kinds = Ident.add a k ctx.kinds} in
    (* Infer type of body (which may mention type variable a) *)
    let ty_body, body_typed = infer_typ defs ctx' body in
    (* Return universal type *)
    let ty = TyAll ((a, k), ty_body) in
    (ty, TyTmAll ((a, k), body_typed, ty))

  | TmIns (t, ty_arg) ->
    (* Infer the type of t *)
    let t_ty, t_typed = infer_typ defs ctx t in
    (* Reduce to see if it's a universal type *)
    (match reduce defs.type_defs t_ty with
    | TyAll ((a, k), ty_body) ->
        (* Check that ty_arg has the expected kind *)
        check_kind defs.type_defs ctx.kinds ty_arg k;
        (* Instantiate ty_body with ty_arg substituted for a *)
        let subst_env = Ident.add a ty_arg Ident.emptytbl in
        let result_ty = subst subst_env ty_body in
        (result_ty, TyTmIns (t_typed, ty_arg, k, result_ty))
    | _ -> failwith "type instantiation expects a polymorphic type")

  | TmLet (x, t, u) ->
    (* Infer the type of the bound expression *)
    let t_ty, t_typed = infer_typ defs ctx t in
    (* Extend context with x:t_ty and infer type of body *)
    let ctx' = {ctx with types = Ident.add x t_ty ctx.types} in
    let u_ty, u_typed = infer_typ defs ctx' u in
    (u_ty, TyTmLet (x, t_typed, u_typed, u_ty))

  | _ ->
    failwith ("cannot infer type of: ")

and check_typ (defs: definitions) (ctx: context) (tm: term) (ty: typ) : typed_term =
  match tm with
  | TmMatch (t, cs) ->
    let t_ty, t_typed = infer_typ defs ctx t in
    (match reduce defs.type_defs t_ty with
    | TyDef (Data (td : ty_dec)) ->
      (* Check each clause against its corresponding constructor *)
      let cs_typed = List.map (fun ((clause_xtor, type_binders, term_binders, body) : clause) ->
        (* 1. Find the matching constructor in the normalized GADT *)
        let xtor : ty_xtor = 
          match List.find_opt (fun (x : ty_xtor) -> 
            Path.equal x.symbol clause_xtor.symbol
          ) td.xtors with
          | Some x -> x
          | None -> failwith ("constructor " ^ Path.name clause_xtor.symbol ^ " not in type")
        in
        
        (* 2. Verify |ai's| = |xtor.quantified| and |xi's| = |xtor.sources| *)
        if List.length type_binders <> List.length xtor.quantified then
          failwith ("wrong number of type arguments for " ^ Path.name xtor.symbol);
        if List.length term_binders <> List.length xtor.sources then
          failwith ("wrong number of term arguments for " ^ Path.name xtor.symbol);
        
        (* 3. Build constraint substitution σ from xtor.constraints *)
        let constraint_subst = 
          match xtor.constraints with
          | None -> Ident.emptytbl
          | Some constraints -> 
            List.fold_left (fun acc (var, ty) ->
              Ident.add var ty acc
            ) Ident.emptytbl constraints
        in
        
        (* 4. Create positional mapping ρ: bi ↦ ai (xtor's vars to user's vars) *)
        let type_var_map =
          List.fold_left2 (fun acc (xtor_var, _) user_var ->
            Ident.add xtor_var (TyVar user_var) acc
          ) Ident.emptytbl xtor.quantified type_binders
        in
        
        (* Combine: rename first, then apply constraints (so constraints override) *)
        let combined_subst = Ident.join constraint_subst type_var_map in
        
        (* 5. Extend term context with pattern variables and their specialized types *)
        let ctx' = {ctx with types =
          List.fold_left2 (fun acc term_var source_ty ->
            let specialized_ty = subst combined_subst source_ty in
            Ident.add term_var specialized_ty acc
          ) ctx.types term_binders xtor.sources
        } in
        
        (* 7. Check the body has the expected type in the extended context *)
        let body_typed = check_typ defs ctx' body ty in
        (clause_xtor, type_binders, term_binders, body_typed)
      ) cs in
      
      (* 8. Verify all td.xtors covered and no duplicate clauses *)
      let covered = List.map (fun ((clause_xtor, _, _, _) : typed_clause) -> clause_xtor.symbol) cs_typed in
      List.iter (fun (expected_xtor : ty_xtor) ->
        if not (List.exists (Path.equal expected_xtor.symbol) covered) then
          failwith ("missing case for constructor" ^ Path.name expected_xtor.symbol)
      ) td.xtors;
      
      (* Check no duplicate clauses *)
      let rec check_duplicates seen = function
        | [] -> ()
        | ((clause_xtor, _, _, _) : typed_clause) :: rest ->
          if List.exists (Path.equal clause_xtor.symbol) seen then
            failwith ("duplicate case for constructor " ^ Path.name clause_xtor.symbol)
          else
            check_duplicates (clause_xtor.symbol :: seen) rest
      in
      check_duplicates [] cs_typed;
      
      TyTmMatch (t_typed, cs_typed, ty)
      
    | _ -> failwith "expected data type in match")

  | TmNew (Some ty_annot, cs) ->
    (* When TmNew has a type annotation, verify it matches the expected type,
       then check as if it were TmNew (None, cs) *)
    if not (equivalent defs.type_defs ty_annot ty) then
      failwith ("new expression type mismatch: expected " ^ 
               typ_to_string false ty ^ " but annotation says " ^ 
               typ_to_string false ty_annot);
    (* Now check the destructor implementations *)
    (match reduce defs.type_defs ty with
    | TyDef (Code td) ->
      (* Check each clause against its corresponding destructor *)
      let cs_typed = List.map (fun ((clause_dtor, type_binders, term_binders, body) : clause) ->
        (* 1. Find the matching destructor in the normalized codata *)
        let dtor : ty_xtor = 
          match List.find_opt (fun (x : ty_xtor) -> 
            Path.equal x.symbol clause_dtor.symbol
          ) td.xtors with
          | Some x -> x
          | None -> failwith ("destructor " ^ Path.name clause_dtor.symbol ^ " not in type")
        in
        
        (* 2. Verify |ai's| = |dtor.quantified| and |xi's| = |dtor.sources| *)
        if List.length type_binders <> List.length dtor.quantified then
          failwith ("wrong number of type arguments for " ^ Path.name dtor.symbol);
        if List.length term_binders <> List.length dtor.sources then
          failwith ("wrong number of term arguments for " ^ Path.name dtor.symbol);
        
        (* 3. Build constraint substitution σ from dtor.constraints *)
        let constraint_subst = 
          match dtor.constraints with
          | None -> Ident.emptytbl
          | Some constraints -> 
            List.fold_left (fun acc (var, ty) ->
              Ident.add var ty acc
            ) Ident.emptytbl constraints
        in
        
        (* 4. Map destructor's quantified variables to parent type's arguments *)
        let parent_type_args = List.filter_map fst td.arguments in
        if List.length parent_type_args <> List.length dtor.quantified then
          failwith ("destructor quantified variables don't match parent type arguments");
        let type_var_map =
          List.fold_left2 (fun acc (dtor_var, _) parent_arg ->
            Ident.add dtor_var parent_arg acc
          ) Ident.emptytbl dtor.quantified parent_type_args
        in
        
        (* Combine: rename first, then apply constraints (so constraints override) *)
        let combined_subst = Ident.join constraint_subst type_var_map in
        
        (* 5. Split sources into init (arguments) and last (return type) *)
        let rec split_last lst =
          match lst with
          | [] -> failwith "expected at least one source type"
          | [x] -> [], x
          | x :: xs -> let init, last = split_last xs in x :: init, last
        in
        
        let inst_sources = List.map (subst combined_subst) dtor.sources in
        let arg_sources, return_ty = split_last inst_sources in
        
        (* 6. Build the codata type (this type) from parent and arguments *)
        let inst_arguments = List.map (subst combined_subst) dtor.arguments in
        let this_ty =
          List.fold_left (fun acc arg -> TyApp (acc, arg))
            (TySym dtor.parent) inst_arguments
        in
        
        (* 7. Split term binders into this and the rest *)
        let this_var, arg_vars = match term_binders with
          | [] -> failwith ("destructor " ^ Path.name dtor.symbol ^ " must have at least one argument (this)")
          | t :: rest -> t, rest
        in
        
        if List.length arg_vars <> List.length arg_sources then
          failwith ("destructor " ^ Path.name dtor.symbol ^ 
                    " argument count mismatch: expected " ^ string_of_int (List.length arg_sources) ^
                    " arguments after this, got " ^ string_of_int (List.length arg_vars));
        
        (* 8. Extend context with this:this_ty and args:arg_sources *)
        let ctx' = {ctx with types = Ident.add this_var this_ty ctx.types} in
        let ctx'' = {ctx' with types = List.fold_left2 (fun acc arg_var arg_ty ->
          Ident.add arg_var arg_ty acc
        ) ctx'.types arg_vars arg_sources} in
        
        (* 9. Check the body has the return type in the extended context *)
        let body_typed = check_typ defs ctx'' body return_ty in
        (clause_dtor, type_binders, term_binders, body_typed)
      ) cs in
      
      (* 10. Verify all td.xtors covered and no duplicate clauses *)
      let covered = List.map (fun ((clause_dtor, _, _, _) : typed_clause) -> clause_dtor.symbol) cs_typed in
      List.iter (fun (expected_dtor : ty_xtor) ->
        if not (List.exists (Path.equal expected_dtor.symbol) covered) then
          failwith ("missing case for destructor " ^ Path.name expected_dtor.symbol)
      ) td.xtors;
      
      (* Check no duplicate clauses *)
      let rec check_duplicates seen = function
        | [] -> ()
        | ((clause_dtor, _, _, _) : typed_clause) :: rest ->
          if List.exists (Path.equal clause_dtor.symbol) seen then
            failwith ("duplicate case for destructor " ^ Path.name clause_dtor.symbol)
          else
            check_duplicates (clause_dtor.symbol :: seen) rest
      in
      check_duplicates [] cs_typed;
      
      TyTmNew (Some ty_annot, cs_typed, ty)
    | _ -> failwith "expected codata type in new")

  | TmNew (None, cs) ->
    (* TmNew without type annotation - must check destructor implementations *)
    (match reduce defs.type_defs ty with
    | TyDef (Code td) ->
      (* Reuse the same logic as TmNew (Some _, cs) above *)
      (* Check each clause against its corresponding destructor *)
      let cs_typed = List.map (fun ((clause_dtor, type_binders, term_binders, body) : clause) ->
        (* 1. Find the matching destructor in the normalized codata *)
        let dtor : ty_xtor = 
          match List.find_opt (fun (x : ty_xtor) -> 
            Path.equal x.symbol clause_dtor.symbol
          ) td.xtors with
          | Some x -> x
          | None -> failwith ("destructor " ^ Path.name clause_dtor.symbol ^ " not in type")
        in
        
        (* 2. Verify |ai's| = |dtor.quantified| and |xi's| = |dtor.sources| *)
        if List.length type_binders <> List.length dtor.quantified then
          failwith ("wrong number of type arguments for " ^ Path.name dtor.symbol);
        if List.length term_binders <> List.length dtor.sources then
          failwith ("wrong number of term arguments for " ^ Path.name dtor.symbol);
        
        (* 3. Build constraint substitution σ from dtor.constraints *)
        let constraint_subst = 
          match dtor.constraints with
          | None -> Ident.emptytbl
          | Some constraints -> 
            List.fold_left (fun acc (var, ty) ->
              Ident.add var ty acc
            ) Ident.emptytbl constraints
        in
        
        (* 4. Map destructor's quantified variables to parent type's arguments *)
        let parent_type_args = List.filter_map fst td.arguments in
        if List.length parent_type_args <> List.length dtor.quantified then
          failwith ("destructor quantified variables don't match parent type arguments");
        let type_var_map =
          List.fold_left2 (fun acc (dtor_var, _) parent_arg ->
            Ident.add dtor_var parent_arg acc
          ) Ident.emptytbl dtor.quantified parent_type_args
        in
        
        (* Combine: rename first, then apply constraints (so constraints override) *)
        let combined_subst = Ident.join constraint_subst type_var_map in
        
        (* 5. Split sources into init (arguments) and last (return type) *)
        let rec split_last lst =
          match lst with
          | [] -> failwith "expected at least one source type"
          | [x] -> [], x
          | x :: xs -> let init, last = split_last xs in x :: init, last
        in
        
        let inst_sources = List.map (subst combined_subst) dtor.sources in
        let arg_sources, return_ty = split_last inst_sources in
        
        (* 6. Build the codata type (this type) from parent and arguments *)
        let inst_arguments = List.map (subst combined_subst) dtor.arguments in
        let this_ty =
          List.fold_left (fun acc arg -> TyApp (acc, arg))
            (TySym dtor.parent) inst_arguments
        in
        
        (* 7. Split term binders into this and the rest *)
        let this_var, arg_vars = match term_binders with
          | [] -> failwith ("destructor " ^ Path.name dtor.symbol ^ " must have at least one argument (this)")
          | t :: rest -> t, rest
        in
        
        if List.length arg_vars <> List.length arg_sources then
          failwith ("destructor " ^ Path.name dtor.symbol ^ 
                    " argument count mismatch: expected " ^ string_of_int (List.length arg_sources) ^
                    " arguments after this, got " ^ string_of_int (List.length arg_vars));
        
        (* 8. Extend context with this:this_ty and args:arg_sources *)
        let ctx' = {ctx with types = Ident.add this_var this_ty ctx.types} in
        let ctx'' = {ctx' with types = List.fold_left2 (fun acc arg_var arg_ty ->
          Ident.add arg_var arg_ty acc
        ) ctx'.types arg_vars arg_sources} in
        
        (* 9. Check the body has the return type in the extended context *)
        let body_typed = check_typ defs ctx'' body return_ty in
        (clause_dtor, type_binders, term_binders, body_typed)
      ) cs in
      
      (* 10. Verify all td.xtors covered and no duplicate clauses *)
      let covered = List.map (fun ((clause_dtor, _, _, _) : typed_clause) -> clause_dtor.symbol) cs_typed in
      List.iter (fun (expected_dtor : ty_xtor) ->
        if not (List.exists (Path.equal expected_dtor.symbol) covered) then
          failwith ("missing case for destructor " ^ Path.name expected_dtor.symbol)
      ) td.xtors;
      
      (* Check no duplicate clauses *)
      let rec check_duplicates seen = function
        | [] -> ()
        | ((clause_dtor, _, _, _) : typed_clause) :: rest ->
          if List.exists (Path.equal clause_dtor.symbol) seen then
            failwith ("duplicate case for destructor " ^ Path.name clause_dtor.symbol)
          else
            check_duplicates (clause_dtor.symbol :: seen) rest
      in
      check_duplicates [] cs_typed;
      
      TyTmNew (None, cs_typed, ty)
    | _ -> failwith "expected codata type in new")

  | TmLam (x, ty_opt, body) ->
    (match reduce defs.type_defs ty with
    | TyFun (ty_arg, ty_body) ->
      (* If annotated, check annotation matches expected *)
      (match ty_opt with
      | Some ty_annot ->
          if not (equivalent defs.type_defs ty_annot ty_arg) then
            failwith ("lambda annotation mismatch: expected " ^ 
                     typ_to_string false ty_arg ^ " but got " ^ 
                     typ_to_string false ty_annot)
      | None -> ());
      (* Check body in extended context *)
      let ctx' = {ctx with types = Ident.add x ty_arg ctx.types} in
      let body_typed = check_typ defs ctx' body ty_body in
      TyTmLam (x, ty_arg, body_typed, ty)
    | _ -> failwith "expected function type for lambda")

  | TmAll ((a, k), body) ->
    (match reduce defs.type_defs ty with
    | TyAll ((a', k'), ty_body') ->
        (* Check kinds match *)
        if k <> k' then
          failwith ("polymorphic term kind mismatch: expected " ^ 
                   kind_to_string k' ^ " but got " ^ kind_to_string k);
        (* Rename a' to a in ty_body' *)
        let rename_subst = Ident.add a' (TyVar a) Ident.emptytbl in
        let ty_body = subst rename_subst ty_body' in
        (* Check body has the renamed type in extended kind context *)
        let ctx' = {ctx with kinds = Ident.add a k ctx.kinds} in
        let body_typed = check_typ defs ctx' body ty_body in
        TyTmAll ((a, k), body_typed, ty)
    | _ -> failwith "expected universal type for polymorphic term")

  | TmIns (t, ty_arg) ->
    (* Infer the kind of ty_arg using the kind context *)
    let k = infer_kind defs.type_defs ctx.kinds ty_arg in
    (* Create a fresh type variable for checking *)
    let a = Ident.mk "a" in
    (* Check t against the polymorphic type TyAll((a, k), ty) *)
    let t_typed = check_typ defs ctx t (TyAll ((a, k), ty)) in
    TyTmIns (t_typed, ty_arg, k, ty)

  | TmLet (x, t, u) ->
    (* Infer the type of the bound expression *)
    let t_ty, t_typed = infer_typ defs ctx t in
    (* Extend context with x:t_ty and check body against expected type *)
    let ctx' = {ctx with types = Ident.add x t_ty ctx.types} in
    let u_typed = check_typ defs ctx' u ty in
    TyTmLet (x, t_typed, u_typed, ty)

  | _ ->
    let inferred_ty, tm_typed = infer_typ defs ctx tm in
    if not (equivalent defs.type_defs inferred_ty ty) then
      failwith ("type mismatch: expected " ^ typ_to_string false ty ^ 
                " but got " ^ typ_to_string false inferred_ty)
    else
      tm_typed
        
(* checking a collection of mutually recursive definitions *)
let check_all (defs: definitions) : typed_definitions =
  let typed_term_defs = List.map (fun (path, (td : term_def)) ->
    (* Build context from type and term parameters *)
    let ctx = {
      kinds = List.fold_left (fun acc (type_var, k) ->
        Ident.add type_var k acc
      ) Ident.emptytbl td.type_args;
      types = List.fold_left (fun acc (arg_name, arg_ty) ->
        Ident.add arg_name arg_ty acc
      ) Ident.emptytbl td.term_args
    } in
    (* Check body against declared return type *)
    let body_typed = check_typ defs ctx td.body td.return_type in
    let typed_td : typed_term_def = {
      name = td.name;
      type_args = td.type_args;
      term_args = td.term_args;
      return_type = td.return_type;
      body = body_typed
    } in
    (path, typed_td)
  ) defs.term_defs in
  { type_defs = defs.type_defs
  ; term_defs = typed_term_defs
  }


(* Conversion to Core terms is now in the Convert module at the top level *)