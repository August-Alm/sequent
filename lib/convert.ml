(**
  Module: Convert
  Description: Conversion from Lang terms to Core terms
*)

open Common.Identifiers

(* Conversion of Lang terms to Core terms *)
module CTm = Core.Terms
module CTy = Common.Types
module LTm = Lang.Terms
module LTy = Lang.Types

let rec convert_typ (t: LTy.typ) : CTy.typ =
  match t with
  | TySym s -> CTy.TySym s
  | TyVar x -> CTy.TyVar x
  | TyApp (t1, t2) -> CTy.TyApp (convert_typ t1, convert_typ t2)
  | TyFun (t1, t2) ->
    CTy.TyApp (CTy.TyApp (CTy.Prim.fun_typ, convert_typ t1), convert_typ t2) 
  | TyAll ((x, k), t) ->
    CTy.TyApp (CTy.Prim.all_typ x k, convert_typ t)
  | TyDef (Prim (s, k)) ->
    CTy.TyDef (CTy.Prim (s, k))
  | TyDef (Data td) ->
    CTy.TyDef (CTy.Data (convert_data td))
  | TyDef (Code td) ->
    CTy.TyDef (CTy.Code (convert_code td))

and convert_data (td: LTy.ty_dec) : CTy.ty_dec =
  { CTy.symbol = td.symbol
  ; CTy.arguments = List.map (fun (t_opt, k) ->
      (Option.map convert_typ t_opt, k)
    ) td.arguments
  ; CTy.xtors = List.map convert_ctor td.xtors
  }

and convert_ctor (ctor: LTy.ty_xtor) : CTy.ty_xtor =
  { CTy.parent = ctor.parent
  ; CTy.symbol = ctor.symbol
  ; CTy.quantified = List.map (fun (x, k) -> (x, k)) ctor.quantified
  ; CTy.producers = List.map convert_typ ctor.sources
  ; CTy.consumers = []
  ; CTy.arguments = List.map convert_typ ctor.arguments
  ; CTy.constraints =
    Option.map (List.map (fun (x, t) -> (x, convert_typ t))) ctor.constraints
  }

and convert_code (td: LTy.ty_dec) : CTy.ty_dec =
  { CTy.symbol = td.symbol
  ; CTy.arguments = List.map (fun (t_opt, k) ->
      (Option.map convert_typ t_opt, k)
    ) td.arguments
  ; CTy.xtors = List.map convert_dtor td.xtors
  }

and convert_dtor (dtor: LTy.ty_xtor) : CTy.ty_xtor =
  let srcs, c =
    match List.rev dtor.sources with
    | [] -> failwith "code destructor must have at least one source"
    | last :: rest_rev -> (List.rev rest_rev, last)
  in
  { CTy.parent = dtor.parent
  ; CTy.symbol = dtor.symbol
  ; CTy.quantified = List.map (fun (x, k) -> (x, k)) dtor.quantified
  ; CTy.producers = List.map convert_typ srcs
  ; CTy.consumers = [convert_typ c]
  ; CTy.arguments = List.map convert_typ dtor.arguments
  ; CTy.constraints =
    Option.map (List.map (fun (x, t) -> (x, convert_typ t))) dtor.constraints
  }
  

(* Helper: Count the number of function arrows in a type *)
let rec count_fun_arrows (ty: LTy.typ) : int =
  match ty with
  | LTy.TyAll (_, t2) -> count_fun_arrows t2  (* Skip type abstraction *)
  | LTy.TyFun (_, t2) -> 1 + count_fun_arrows t2
  | _ -> 0

(* Helper: Collect arguments from nested applications *)
let rec collect_args (tm: LTm.typed_term) : (LTm.typed_term * LTm.typed_term list) =
  match tm with
  | LTm.TyTmApp (t, u, _) ->
    let (head, args) = collect_args t in
    (head, args @ [u])
  | _ -> (tm, [])

(* Helper: Collect both type arguments and term arguments from
  nested applications and instantiations *)
let rec collect_type_and_term_args (tm: LTm.typed_term) 
    : (LTm.typed_term * LTy.typ list * LTm.typed_term list) =
  match tm with
  | LTm.TyTmApp (t, u, _) ->
    let (head, ty_args, tm_args) = collect_type_and_term_args t in
    (head, ty_args, tm_args @ [u])
  | LTm.TyTmIns (t, ty_arg, _, _) ->
    let (head, ty_args, tm_args) = collect_type_and_term_args t in
    (head, ty_args @ [ty_arg], tm_args)
  | _ -> (tm, [], [])

(* Helper: Get function argument types from a function type *)
let rec get_arg_types (ty: LTy.typ) : LTy.typ list =
  match ty with
  | LTy.TyFun (t1, t2) -> t1 :: get_arg_types t2
  | _ -> []

let rec get_return_type (ty: LTy.typ) : LTy.typ =
  match ty with
  | LTy.TyFun (_, t2) -> get_return_type t2
  | _ -> ty

let rec convert (tm: LTm.typed_term) : CTm.producer =
  match tm with
  | LTm.TyTmInt (n, _ty) ->
    CTm.Int n

  | LTm.TyTmVar (x, _ty) ->
    CTm.Var x

  | LTm.TyTmSym (sym, _ty) ->
    (* Top-level symbol reference - always use Call *)
    let alpha = Ident.fresh () in
    let ty_args = [] in (* TODO: extract actual type instantiations *)
    CTm.Mu (alpha, CTm.Call (sym, ty_args, [], [CTm.Covar alpha]))

  | LTm.TyTmApp (t, u, ty_ret) ->
    (* Collect all type and term arguments from nested applications and instantiations *)
    let (head, ty_args, tm_args) = collect_type_and_term_args (LTm.TyTmApp (t, u, ty_ret)) in
    (match head with
    | LTm.TyTmSym (sym, sym_ty) ->
      (* This is an application of a top-level symbol *)
      let required_arity = count_fun_arrows sym_ty in
      let provided_arity = List.length tm_args in
      
      if provided_arity = required_arity then
        (* Fully applied - generate Call statement with type arguments *)
        let alpha = Ident.fresh () in
        CTm.Mu (alpha, CTm.Call (sym, List.map convert_typ ty_args, List.map convert tm_args, [CTm.Covar alpha]))
      
      else if provided_arity < required_arity then
        (* Partially applied - generate lambda for remaining arguments *)
        (* foo(u) where foo: a -> b -> c becomes:
           fun (y: b) => foo(u, y) 
           which is: new { $app(this, y, α) => μβ.Call(foo, [u, y], [β]) | α } *)
        let arg_types = get_arg_types sym_ty in
        let remaining_arg_types = Utility.drop provided_arity arg_types in
        let final_return_ty = get_return_type sym_ty in  (* The final return type, not the partial app type *)
        
        (* Generate nested lambdas for each remaining argument *)
        let rec make_lambdas remaining_tys provided_args =
          match remaining_tys with
          | [] -> 
            (* All arguments provided - make the call *)
            let alpha = Ident.fresh () in
            (* TODO: extract actual type instantiations *)
            let ty_args = [] in
            CTm.Mu (alpha, CTm.Call (sym, List.map convert_typ ty_args, List.map convert provided_args, [CTm.Covar alpha]))
          | arg_ty :: rest_tys ->
            (* Create lambda for this argument *)
            let x = Ident.fresh () in
            let y = Ident.fresh () in
            let ta = Ident.fresh () in
            let tb = Ident.fresh () in
            (* The result type after applying this and all remaining arguments *)
            let result_ty = 
              if rest_tys = [] then convert_typ final_return_ty
              else List.fold_right (fun arg_ty acc -> 
                CTy.TyApp (CTy.TyApp (CTy.TyDef (CTy.Prim (CTy.Prim.fun_sym, CTy.KArrow (CTy.KStar, CTy.KArrow (CTy.KStar, CTy.KStar)))), convert_typ arg_ty), acc)
              ) rest_tys (convert_typ final_return_ty)
            in
            CTm.Cocase [{
              CTm.xtor = CTy.Prim.app_dtor_sym;
              CTm.type_vars = [ta; tb];
              CTm.variables = [x];
              CTm.covariables = [y];
              CTm.statement = CTm.Cut (
                make_lambdas rest_tys (provided_args @ [LTm.TyTmVar (x, arg_ty)]),
                result_ty,
                CTm.Covar y
              )
            }]
        in
        make_lambdas remaining_arg_types tm_args
      
      else
        (* Over-applied - this shouldn't happen in well-typed code *)
        failwith "convert: over-applied function (type checking should have caught this)"
    | _ ->
      (* General application using $app destructor *)
      let ty_arg = LTm.get_type u in
      let x = Ident.fresh () in
      (* μx.< conv t | $apply{ty_arg}{ty_ret}(x, conv u) > *)
      CTm.Mu (x, CTm.Cut (
        convert t,
        (* Function type: ty_arg -> ty_ret *)
        CTy.TyApp (CTy.TyApp (CTy.TyDef (CTy.Prim (CTy.Prim.fun_sym,
          CTy.KArrow (CTy.KStar, CTy.KArrow (CTy.KStar, CTy.KStar)))),
            convert_typ ty_arg), convert_typ ty_ret),
        CTm.Destructor (CTy.Prim.app_dtor_sym, (
          [convert_typ ty_arg; convert_typ ty_ret],
          [CTm.Var x],
          [CTm.MuTilde (x, CTm.Cut (convert u, convert_typ ty_arg, CTm.Covar x))]
        ))
      ))
    )

  | LTm.TyTmIns (t, ty_arg, k, ty_result) ->
    (* Type instantiation: check if this is part of a function call pattern *)
    (* If t is a symbol or becomes a symbol after collecting args, handle as Call *)
    let (head, all_ty_args, all_tm_args) = collect_type_and_term_args (LTm.TyTmIns (t, ty_arg, k, ty_result)) in
    (match head with
    | LTm.TyTmSym (_, _) when all_ty_args <> [] && all_tm_args = [] ->
      (* Just type instantiation, no term args yet *)
      let x = Ident.fresh () in
      CTm.Mu (x, CTm.Cut (
        convert t,
        CTy.TyApp (CTy.TyDef (CTy.Prim (CTy.Prim.all_sym k, CTy.KArrow (CTy.KArrow (k, CTy.KStar), CTy.KStar))), convert_typ ty_result),
        CTm.Destructor (CTy.Prim.ins_dtor_sym k, (
          [convert_typ ty_result; convert_typ ty_arg],
          [],
          [CTm.Covar x]
        ))
      ))
    | _ ->
      (* Use old forall encoding *)
      let x = Ident.fresh () in
      CTm.Mu (x, CTm.Cut (
        convert t,
        CTy.TyApp (CTy.TyDef (CTy.Prim (CTy.Prim.all_sym k, CTy.KArrow (CTy.KArrow (k, CTy.KStar), CTy.KStar))), convert_typ ty_result),
        CTm.Destructor (CTy.Prim.ins_dtor_sym k, (
          [convert_typ ty_result; convert_typ ty_arg],
          [],
          [CTm.Covar x]
        ))
      ))
    )

  | LTm.TyTmLam (x, _a, body, _ty) ->
    let b = LTm.get_type body in
    let y = Ident.fresh () in
    let ta = Ident.fresh () in
    let tb = Ident.fresh () in
    (* new $fun{a}{b} { $apply{a}{b}(this, x, y) => < conv body | y > } *)
    CTm.Cocase [{
      CTm.xtor = CTy.Prim.app_dtor_sym;
      CTm.type_vars = [ta; tb];
      CTm.variables = [x];
      CTm.covariables = [y];
      CTm.statement = CTm.Cut (convert body, convert_typ b, CTm.Covar y)
    }]

  | LTm.TyTmAll ((a, k), body, _ty) ->
    let b = LTm.get_type body in
    let y = Ident.fresh () in
    (* new $forall{k} { $inst{a: k}(y) => < conv body | y > } *)
    CTm.Cocase [{
      CTm.xtor = CTy.Prim.ins_dtor_sym k;
      CTm.type_vars = [a];
      CTm.variables = [];
      CTm.covariables = [y];
      CTm.statement = CTm.Cut (convert body, convert_typ b, CTm.Covar y)
    }]

  | LTm.TyTmLet (x, t, u, ty) ->
    let t_ty = LTm.get_type t in
    let y = Ident.fresh () in
    (* μy.< conv t | μ̃x.< conv u | y > > *)
    CTm.Mu (y, CTm.Cut (
      convert t,
      convert_typ t_ty,
      CTm.MuTilde (x, CTm.Cut (convert u, convert_typ ty, CTm.Covar y))
    ))

  | LTm.TyTmMatch (t, clauses, ty) ->
    let t_ty = LTm.get_type t in
    let y = Ident.fresh () in
    (* μy.< conv t | case { ctor_i{type_vars}(term_vars) => < conv body_i | y > } > *)
    let patterns = List.map (fun (xtor, type_vars, term_vars, body) ->
      { CTm.xtor = xtor.LTy.symbol
      ; CTm.type_vars = type_vars
      ; CTm.variables = term_vars
      ; CTm.covariables = []  (* Case patterns don't have covariables *)
      ; CTm.statement = CTm.Cut (convert body, convert_typ ty, CTm.Covar y)
      }
    ) clauses in
    CTm.Mu (y, CTm.Cut (
      convert t,
      convert_typ t_ty,
      CTm.Case patterns
    ))

  | LTm.TyTmNew (_ty_opt, clauses, _ty) ->
    (* In Lang: new stream(a) { head{_} => x ; tail{_} => const_stream(x) }
       In Core: cocase { head{a}(k) => <x | k> ; tail{a}(k) => <...| k> }
       
       Note: In Lang, self is implicit (not in pattern bindings).
       In Core, cocase patterns have NO producer variables (no self).
       They only have consumer variables for the return continuation.
       Self appears in destructor APPLICATIONS, not in cocase pattern definitions.
       
       Extract type arguments from the result type to use as type variables in patterns.
       For `new stream(a)`, the type is `TyApp(TyCtor(stream), TyVar(a))`, so we extract `[a]`.
    *)
    let rec extract_type_vars (ty: LTy.typ) : Ident.t list =
      match ty with
      | LTy.TyVar x -> [x]
      | LTy.TyApp (t1, t2) -> extract_type_vars t1 @ extract_type_vars t2
      | _ -> []
    in
    let type_vars_from_result = extract_type_vars _ty in
    
    let patterns = List.map (fun (xtor, _lang_type_vars, term_vars, body) ->
      let body_ty = LTm.get_type body in
      let y = Ident.fresh () in
      { CTm.xtor = xtor.LTy.symbol
      ; CTm.type_vars = type_vars_from_result  (* Use type vars from result type, not Lang pattern *)
      ; CTm.variables = term_vars  (* Just the non-return arguments (empty for head/tail) *)
      ; CTm.covariables = [y]
      ; CTm.statement = CTm.Cut (convert body, convert_typ body_ty, CTm.Covar y)
      }
    ) clauses in
    CTm.Cocase patterns

  | LTm.TyTmCtor (ctor, ty_args, tm_args, _ty) ->
    (* ctor{(Convert.typ ty_args)}((conv tm_args), []) *)
    CTm.Constructor (ctor.LTy.symbol, (
      List.map convert_typ ty_args,
      List.map convert tm_args,
      []
    ))

  | LTm.TyTmDtor (dtor, ty_args, tm_args, _ty) ->
    (* The first tm_arg should be 'self' *)
    (match tm_args with
    | [] -> failwith "convert: destructor must have at least 'self' argument"
    | self :: rest ->
      let self_ty = LTm.get_type self in
      let y = Ident.fresh () in
      (* μy.< conv self | dtor{(Convert.typ ty_args)}((conv rest), y) > *)
      CTm.Mu (y, CTm.Cut (
        convert self,
        convert_typ self_ty,
        CTm.Destructor (dtor.LTy.symbol, (
          List.map convert_typ ty_args,
          List.map convert rest,
          [CTm.Covar y]
        ))
      ))
    )

(* Convert a typed term definition to a Core term definition *)
let convert_term_def (td: LTm.typed_term_def) : CTm.term_def =
  (* Producer arguments: for each term argument (x: t), create (x: Prd (convert t)) *)
  let prod_args = List.map (fun (x, ty) ->
    (x, convert_typ ty)
  ) td.LTm.term_args in
  
  (* Consumer argument: create a fresh covariable α: Cns (convert return_type) *)
  let alpha = Ident.fresh () in
  let cons_args = [(alpha, convert_typ td.LTm.return_type)] in
  
  (* Body: convert the body directly without type abstraction wrapper *)
  (* In Core, type parameters are part of the function signature, not the body *)
  let body_producer = convert td.LTm.body in
  
  let body_statement =
    CTm.Cut (body_producer, convert_typ td.LTm.return_type, CTm.Covar alpha)
  in
  
  { CTm.name = td.LTm.name
  ; CTm.type_args = td.LTm.type_args  (* Keep type parameters in signature *)
  ; CTm.prod_args = prod_args
  ; CTm.cons_args = cons_args
  ; CTm.return_type = convert_typ td.LTm.return_type
  ; CTm.body = body_statement
  }

(* Collect all kinds used in TyTmAll nodes *)
let rec collect_forall_kinds (tm: LTm.typed_term) : CTy.kind list =
  match tm with
  | LTm.TyTmInt _ -> []
  | LTm.TyTmVar _ -> []
  | LTm.TyTmSym _ -> []
  | LTm.TyTmApp (t, u, _) ->
    collect_forall_kinds t @ collect_forall_kinds u
  | LTm.TyTmIns (t, _, _, _) ->
    collect_forall_kinds t
  | LTm.TyTmLam (_, _, body, _) ->
    collect_forall_kinds body
  | LTm.TyTmAll ((_, k), body, _) ->
    k :: collect_forall_kinds body
  | LTm.TyTmLet (_, t, u, _) ->
    collect_forall_kinds t @ collect_forall_kinds u
  | LTm.TyTmMatch (t, clauses, _) ->
    let clause_kinds = List.concat_map (fun (_, _, _, body) ->
      collect_forall_kinds body
    ) clauses in
    collect_forall_kinds t @ clause_kinds
  | LTm.TyTmNew (_, clauses, _) ->
    List.concat_map (fun (_, _, _, body) ->
      collect_forall_kinds body
    ) clauses
  | LTm.TyTmCtor (_, _, args, _) ->
    List.concat_map collect_forall_kinds args
  | LTm.TyTmDtor (_, _, args, _) ->
    List.concat_map collect_forall_kinds args

let collect_all_forall_kinds (defs: LTm.typed_definitions) : CTy.kind list =
  let kinds = List.concat_map (fun (_, td) ->
    collect_forall_kinds td.LTm.body
  ) defs.LTm.term_defs in
  (* Remove duplicates by converting to a set-like structure *)
  let rec unique = function
    | [] -> []
    | k :: rest ->
      if List.mem k rest then unique rest
      else k :: unique rest
  in
  unique kinds

(* Convert typed definitions to Core definitions *)
let convert_definitions (defs: LTm.typed_definitions) : CTm.definitions =
  let core_term_defs = List.map (fun (path, td) ->
    (path, convert_term_def td)
  ) defs.LTm.term_defs in
  
  (* Convert type definitions *)
  let core_type_defs = List.map (fun (path, (ty_def, kind)) ->
    match ty_def with
    | LTy.Data td ->
      (path, (CTy.Data (convert_data td), kind))
    | LTy.Code td ->
      (path, (CTy.Code (convert_code td), kind))
    | LTy.Prim (s, k) ->
      (path, (CTy.Prim (s, k), kind))
  ) defs.LTm.type_defs in
  
  (* Collect all kinds used in TyTmAll and generate $forall{k} definitions *)
  let forall_kinds = collect_all_forall_kinds defs in
  let forall_type_defs = List.map (fun k ->
    let a = Ident.fresh () in
    let forall_def = CTy.Prim.all_def a k in
    let forall_kind = CTy.KArrow (CTy.KArrow (k, CTy.KStar), CTy.KStar) in
    (CTy.Prim.all_sym k, (forall_def, forall_kind))
  ) forall_kinds in
  
  (* Add primitive type definitions (int, $fun) and $forall{k} types *)
  let all_type_defs = CTy.primitive_ty_defs @ forall_type_defs @ core_type_defs in
  
  { CTm.type_defs = all_type_defs
  ; CTm.term_defs = core_term_defs
  }
