open Common.Identifiers
open Types

type variable = Ident.t
type symbol = Path.t

(** Description of an external import *)
type import =
  { name: Path.t
  ; parameter_types: chiral_tpe list
  ; clauses_types: (chiral_tpe list) list
  }

(** Type annotated abstract syntax of terms *)
type term =
  | Variable of variable (** Variable or covariable *)
  | Match of signature * branch list (** Match, consuming data *)
  | Constructor of xtor * tpe list * term list (** Constructor, producing data *)
  | New of signature * branch list (** New, producing codata *)
  | Destructor of xtor * tpe list * term list (** Destructor, consuming codata *)
  | MuLhsPos of tpe * variable * command (** Mu binding covariable at positive type *)
  | MuRhsPos of tpe * variable * command (** MuTilde binding variable at positive type *)
  | MuLhsNeg of tpe * variable * command (** Mu binding covariable at negative type *)
  | MuRhsNeg of tpe * variable * command (** MuTilde binding variable at negative type *)

(** A branch in a match/case new/cocase term *)
and branch =
  { xtor: xtor
  ; type_vars: (variable * kind) list
  ; term_vars: variable list
  ; command: command
  }

(** Type annotated computational commands *)
and command =
  | CutPos of tpe * term * term (** Type must be positive *)
  | CutNeg of tpe * term * term (** Type must be negative *)
  | Extern of import * term list * clause list (** External call *)
  | Call of symbol * tpe list * term list (** Internal call or jump *)
  | End

(** A clause (similar to branch) in an external call *)
and clause =
  { parameters: variable list
  ; body: command
  }

type definition =
  { name: symbol
  ; type_params: (variable * kind) list
  ; term_params: (variable * chiral_tpe) list
  ; body: command
  }

module Env = struct
  (** A top-level environment for type checking *)
  type t =
    { terms: definition Path.tbl
    ; signatures: signatures
    ; imports: import Path.tbl
    }
  let empty =
    { terms = Path.emptytbl
    ; signatures = Path.emptytbl
    ; imports = Path.emptytbl
    }
  let add_definition env def =
    {env with terms = Path.add def.name def env.terms}
  let get_definition env name =
    Path.find name env.terms
  let add_signature env pol sgn =
    {env with signatures = Types.add_def env.signatures pol sgn}
  let get_signature env name =
    Types.get_def env.signatures name
  let add_import env (imp : import) =
    {env with imports = Path.add imp.name imp env.imports}
  let get_import env name =
    Path.find name env.imports
end

module Ctx = struct
  (** Local context for type checking *)
  type t = {types: chiral_tpe Ident.tbl ; kinds: kind Ident.tbl}
  let empty = {types = Ident.emptytbl; kinds = Ident.emptytbl}
  let add_type ctx x t = {ctx with types = Ident.add x t ctx.types}
  let get_type ctx x = Ident.find x ctx.types
  let add_kind ctx x k = {ctx with kinds = Ident.add x k ctx.kinds}
  let get_kind ctx x = Ident.find x ctx.kinds
end

exception TypeMismatchCommand of command * tpe * tpe
exception TypeMismatchTerm of term * tpe * tpe
exception ChiralityMismatchTerm of term * chiral_tpe * chiral_tpe
exception PolarityMismatchCommand of command * polarity * polarity
exception PolarityMismatchTerm of term * polarity * polarity
exception UndefinedTerm of symbol
exception TypeArgumentNumberMismatch
exception TermArgumentNumberMismatch
exception ClauseNumberMismatch
exception ClauseParameterNumberMismatch
exception BranchNumberMismatch
exception CannotInferTypeOfCommand of command
exception CannotInferTypeOfTerm of term
exception MissingBranch of xtor
exception DuplicateBranch of xtor
exception NewOfNonCodataType of term
exception MatchOfNonDataType of term
exception ConstructorOfNonDataType of term
exception DestructorOfNonCodataType of term

let chiralities_equivalent (env: Env.t) (inf: chiral_tpe) (tty: chiral_tpe) =
  match inf, tty with
  | Lhs t1, Lhs t2
  | Rhs t1, Rhs t2 ->
    Types.equivalent env.signatures t1 t2
  | _ -> false

let rec check_term (env: Env.t) (ctx: Ctx.t) (trm: term) (typ: chiral_tpe) =
  match trm with
  | New (trm_sgn, branches) ->
    let ty_normalized = chiral_tpe_map (Types.reduce env.signatures) typ in
    (match ty_normalized with
    | Lhs ty -> check_case_or_cocase env ctx Negative trm_sgn branches ty
    | _ -> raise (PolarityMismatchTerm (trm, Negative, Positive)))
  
  | Match (trm_sgn, branches) ->
    let ty_normalized = chiral_tpe_map (Types.reduce env.signatures) typ in
    (match ty_normalized with
    | Rhs ty -> check_case_or_cocase env ctx Positive trm_sgn branches ty
    | _ -> raise (PolarityMismatchTerm (trm, Positive, Negative)))
  
  | MuLhsPos (t, u, c) ->
    (match typ with
    | Lhs ty ->
      if not (Types.equivalent env.signatures t ty) then
        raise (TypeMismatchTerm (trm, t, ty));
      (match infer_polarity env.signatures ctx.kinds t with
      | Positive ->
        let ctx' = Ctx.add_type ctx u (Rhs ty) in (* Bind covariable *)
        check_command env ctx' c
      | Negative ->
        raise (PolarityMismatchTerm (trm, Positive, Negative)))
    | Rhs _ ->
      raise (ChiralityMismatchTerm (trm, typ, Lhs t)))
  
  | MuLhsNeg (t, u, c) ->
    (match typ with
    | Lhs ty ->
      if not (Types.equivalent env.signatures t ty) then
        raise (TypeMismatchTerm (trm, t, ty));
      (match infer_polarity env.signatures ctx.kinds t with
      | Negative ->
        let ctx' = Ctx.add_type ctx u (Rhs ty) in (* Bind covariable *)
        check_command env ctx' c
      | Positive ->
        raise (PolarityMismatchTerm (trm, Negative, Positive)))
    | Rhs _ ->
      raise (ChiralityMismatchTerm (trm, typ, Lhs t)))

  | MuRhsPos (t, x, c) ->
    (match typ with
    | Rhs ty ->
      if not (Types.equivalent env.signatures t ty) then
        raise (TypeMismatchTerm (trm, t, ty));
      (match infer_polarity env.signatures ctx.kinds t with
      | Positive ->
        let ctx' = Ctx.add_type ctx x (Lhs ty) in (* Bind variable *)
        check_command env ctx' c
      | Negative ->
        raise (PolarityMismatchTerm (trm, Positive, Negative)))
    | Lhs _ ->
      raise (ChiralityMismatchTerm (trm, typ, Rhs t)))

  | MuRhsNeg (t, x, c) ->
    (match typ with
    | Rhs ty ->
      if not (Types.equivalent env.signatures t ty) then
        raise (TypeMismatchTerm (trm, t, ty));
      (match infer_polarity env.signatures ctx.kinds t with
      | Negative ->
        let ctx' = Ctx.add_type ctx x (Lhs ty) in (* Bind variable *)
        check_command env ctx' c
      | Positive ->
        raise (PolarityMismatchTerm (trm, Negative, Positive)))
    | Lhs _ ->
      raise (ChiralityMismatchTerm (trm, typ, Rhs t)))

  | _ ->
    let inferred = infer_term env ctx trm in
    if not (chiralities_equivalent env inferred typ) then
      raise (ChiralityMismatchTerm (trm, inferred, typ))
  
and check_case_or_cocase
    (env: Env.t) (ctx: Ctx.t) (pol: polarity) (trm_sgn: signature) (branches: branch list) (typ: tpe) =
  match typ with
  | TyPos sgn | TyNeg sgn ->
    (match pol with
    | Negative ->
      if not (Types.equivalent env.signatures (TyNeg trm_sgn) (TyNeg sgn)) then
        raise (TypeMismatchTerm (New (trm_sgn, branches), TyNeg trm_sgn, TyNeg sgn));
    | Positive ->
      if not (Types.equivalent env.signatures (TyPos trm_sgn) (TyPos sgn)) then
        raise (TypeMismatchTerm (New (trm_sgn, branches), TyPos trm_sgn, TyPos sgn)));

    (* Check each branch *)
    List.iter (fun (branch: branch) ->
      let xtor = branch.xtor in
        
      (* Check type variable count *)
      if List.length branch.type_vars <> List.length xtor.quantified then
        raise TypeArgumentNumberMismatch;
      
      (* Apply constraints from type instantiation first *)
      let initial_subst = match xtor.constraints with
        | None -> Ident.emptytbl
        | Some constraints ->
          List.fold_left (fun acc (qv, ty) -> Ident.add qv ty acc
          ) Ident.emptytbl constraints
      in
      
      (* Then map remaining quantified vars to pattern type vars *)
      let ty_subst = List.fold_left2 (fun acc (tv, k) (qv, k') ->
        if k <> k' then
          raise (Types.KindMismatch (TyVar tv, k, k'));
        match Ident.find_opt qv acc with
        | Some _ -> acc  (* Already constrained, keep it *)
        | None -> Ident.add qv (TyVar tv) acc
      ) initial_subst branch.type_vars xtor.quantified in
      
      (* Apply substitution to get actual types *)
      let param_tys = List.map (chiral_tpe_map (Types.subst ty_subst)) xtor.parameters in
      
      (* Extend context with pattern bindings *)
      let ctx' =
        try List.fold_left2 Ctx.add_type ctx branch.term_vars param_tys
        with Invalid_argument _ -> raise TermArgumentNumberMismatch
      in
      
      (* Check the body statement - just ensure it type checks *)
      check_command env ctx' branch.command
    ) branches;
    
    (* Check exhaustivity: all destructors covered *)
    let covered = List.map (fun (b: branch) -> b.xtor.name) branches in
    List.iter (fun (xtor: xtor) ->
      if not (List.exists (Path.equal xtor.name) covered) then
        raise (MissingBranch xtor)
    ) sgn.xtors;
    
    (* Check no duplicates *)
    let rec check_dups seen = function
      | [] -> ()
      | branch :: rest ->
        if List.exists (Path.equal branch.xtor.name) seen then
          raise (DuplicateBranch branch.xtor)
        else
          check_dups (branch.xtor.name :: seen) rest
    in
    check_dups [] branches
    
  | TyVar _ ->
    (* Type variable - skip checking, we can't verify constructors/destructors *)
    (* Just check the pattern bodies with the type variable in scope *)
    List.iter (fun (branch: branch) ->
      (* Add type variables from pattern to context *)
      let ctx' = List.fold_left (fun (acc: Ctx.t) (tv, k) ->
        Ctx.add_kind acc tv k
      ) ctx branch.type_vars in
      
      (* Add (co)variables to context *)
      let ty =
        (match pol with
        | Negative -> Rhs typ
        | Positive -> Lhs typ)
      in
      let ctx'' = List.fold_left (fun acc var ->
        Ctx.add_type acc var ty
      ) ctx' branch.term_vars in
      
      (* Check the body statement - just ensure it type checks *)
      check_command env ctx'' branch.command
    ) branches;
  
  | _ ->
    match pol with
    | Negative -> raise (NewOfNonCodataType (New (trm_sgn, branches)))
    | Positive -> raise (MatchOfNonDataType (New (trm_sgn, branches)))

and infer_term (env: Env.t) (ctx: Ctx.t) (trm: term) : chiral_tpe =
  match trm with
  | Variable x -> Ctx.get_type ctx x
  | Constructor (xtor, tys, args) -> infer_xtor env ctx Positive xtor tys args
  | Destructor (xtor, tys, args) -> infer_xtor env ctx Negative xtor tys args
  | _ -> raise (CannotInferTypeOfTerm trm)

and infer_xtor
    (env: Env.t) (ctx: Ctx.t) (pol: polarity) (xtor: xtor) (tys: tpe list) (args: term list) =
  let sgn, p, _ = Env.get_signature env xtor.parent in
  match p, pol with
  | Positive, Positive
  | Negative, Negative ->
    if not (List.exists (fun (xt: xtor) -> Path.equal xt.name xtor.name) sgn.xtors) then
      raise (UndefinedTerm xtor.name);
    (* Build substitution from quantified variables to provided types *)
    let ty_subst =
      try
        List.fold_left2 (fun acc (tv, _) ty -> Ident.add tv ty acc
        ) Ident.emptytbl xtor.quantified tys
      with
      | Invalid_argument _ -> raise TypeArgumentNumberMismatch
    in
    
    (* Apply substitution to parameter types *)
    let param_tys =
      List.map (chiral_tpe_map (Types.subst ty_subst)) xtor.parameters
    in
    
    (* Check arguments *)
    (try
      List.iter2 (check_term env ctx) args param_tys
    with
    | Invalid_argument _ -> raise TermArgumentNumberMismatch);
    
    (* Build the result type: parent applied to instantiated arguments *)
    let arg_tys = List.map (Types.subst ty_subst) xtor.parent_arguments in
    let result_ty = List.fold_left (fun acc arg -> TyApp (acc, arg)
    ) (TySym xtor.parent) arg_tys in
    (match pol with
    | Positive -> Lhs result_ty
    | Negative -> Rhs result_ty)

  | Negative, Positive -> raise (ConstructorOfNonDataType (Constructor (xtor, tys, args)))
  | Positive, Negative -> raise (DestructorOfNonCodataType (Destructor (xtor, tys, args)))

and check_command (env: Env.t) (ctx: Ctx.t) (cmd: command): unit =
  match cmd with
  | CutPos (t, trm1, trm2) ->
    (match infer_polarity env.signatures ctx.kinds t with
    | Positive ->
      check_term env ctx trm1 (Lhs t);
      check_term env ctx trm2 (Rhs t)
    | Negative ->
      raise (PolarityMismatchCommand (cmd, Positive, Negative)))
  | CutNeg (t, trm1, trm2) ->
    (match infer_polarity env.signatures ctx.kinds t with
    | Negative ->
      check_term env ctx trm1 (Lhs t);
      check_term env ctx trm2 (Rhs t)
    | Positive ->
      raise (PolarityMismatchCommand (cmd, Negative, Positive)))
  | Call (sym, tys, args) ->
    (* Look up the function definition to get its type *)
    let def = Env.get_definition env sym in
    (* Check we have the right kinds of type arguments *)
    (try
      List.iter2 (fun ty (_, k) ->
        check_kind env.signatures ctx.kinds ty k
      ) tys def.type_params;
    with
    | Invalid_argument _ ->  raise TypeArgumentNumberMismatch);
    (* Build type substitution *)
    let ty_subst = List.fold_left2 (fun acc (tv, _) ty ->
      Ident.add tv ty acc
    ) Ident.emptytbl def.type_params tys
    in
    (* Check term arguments with substituted types *)
    (try
      List.iter2 (fun prod (_, arg_ty) ->
        let instantiated_ty = chiral_tpe_map (Types.subst ty_subst) arg_ty in
        check_term env ctx prod instantiated_ty
      ) args def.term_params;
    with
    | Invalid_argument _ -> raise TermArgumentNumberMismatch);
  | Extern (imp, args, clauses) ->
    (* Look up the import to get its type *)
    let imp_def = Env.get_import env imp.name in
    (* Check term arguments *)
    (try
      List.iter2 (check_term env ctx) args imp_def.parameter_types
    with
    | Invalid_argument _ -> raise TermArgumentNumberMismatch);
    (* Check clauses *)
    (try
      List.iter2 (fun clause clause_tys ->
        let ctx' =
          try
            List.fold_left2 (Ctx.add_type) ctx clause.parameters clause_tys
          with
          | Invalid_argument _ -> raise ClauseParameterNumberMismatch
        in
        check_command env ctx' clause.body
      ) clauses imp_def.clauses_types
    with
    | Invalid_argument _ -> raise ClauseNumberMismatch
    | e -> raise e)
  | End -> ()



