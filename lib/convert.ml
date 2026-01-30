(**
  Module: Convert
  Description: Conversion from Lang terms to Core terms
*)

open Common.Identifiers

(* Conversion of Lang terms to Core terms *)
module CT = Core.Terms

(* Helper: Count the number of function arrows in a type *)
let rec count_fun_arrows (ty: Lang.Types.typ) : int =
  match ty with
  | Lang.Types.TyAll (_, t2) -> count_fun_arrows t2  (* Skip type abstraction *)
  | Lang.Types.TyFun (_, t2) -> 1 + count_fun_arrows t2
  | _ -> 0

(* Helper: Collect arguments from nested applications *)
let rec collect_args (tm: Lang.Terms.typed_term) : (Lang.Terms.typed_term * Lang.Terms.typed_term list) =
  match tm with
  | Lang.Terms.TyTmApp (t, u, _) ->
    let (head, args) = collect_args t in
    (head, args @ [u])
  | _ -> (tm, [])

(* Helper: Collect both type arguments and term arguments from nested applications and instantiations *)
let rec collect_type_and_term_args (tm: Lang.Terms.typed_term) 
    : (Lang.Terms.typed_term * Lang.Types.typ list * Lang.Terms.typed_term list) =
  match tm with
  | Lang.Terms.TyTmApp (t, u, _) ->
    let (head, ty_args, tm_args) = collect_type_and_term_args t in
    (head, ty_args, tm_args @ [u])
  | Lang.Terms.TyTmIns (t, ty_arg, _, _) ->
    let (head, ty_args, tm_args) = collect_type_and_term_args t in
    (head, ty_args @ [ty_arg], tm_args)
  | _ -> (tm, [], [])

(* Helper: Get function argument types from a function type *)
let rec get_arg_types (ty: Lang.Types.typ) : Lang.Types.typ list =
  match ty with
  | Lang.Types.TyFun (t1, t2) -> t1 :: get_arg_types t2
  | _ -> []

let rec get_return_type (ty: Lang.Types.typ) : Lang.Types.typ =
  match ty with
  | Lang.Types.TyFun (_, t2) -> get_return_type t2
  | _ -> ty

let rec convert (tm: Lang.Terms.typed_term) : CT.producer =
  match tm with
  | Lang.Terms.TyTmInt (n, _ty) ->
    CT.Int n

  | Lang.Terms.TyTmVar (x, _ty) ->
    CT.Var x

  | Lang.Terms.TyTmSym (sym, _ty) ->
    (* Top-level symbol reference - always use Call *)
    let alpha = Ident.fresh () in
    let ty_args = [] in (* TODO: extract actual type instantiations *)
    CT.Mu (alpha, CT.Call (sym, ty_args, [], [CT.Covar alpha]))

  | Lang.Terms.TyTmApp (t, u, ty_ret) ->
    (* Collect all type and term arguments from nested applications and instantiations *)
    let (head, ty_args, tm_args) = collect_type_and_term_args (Lang.Terms.TyTmApp (t, u, ty_ret)) in
    (match head with
    | Lang.Terms.TyTmSym (sym, sym_ty) ->
      (* This is an application of a top-level symbol *)
      let required_arity = count_fun_arrows sym_ty in
      let provided_arity = List.length tm_args in
      
      if provided_arity = required_arity then
        (* Fully applied - generate Call statement with type arguments *)
        let alpha = Ident.fresh () in
        CT.Mu (alpha, CT.Call (sym, List.map Lang.Types.Convert.typ ty_args, List.map convert tm_args, [CT.Covar alpha]))
      
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
            CT.Mu (alpha, CT.Call (sym, ty_args, List.map convert provided_args, [CT.Covar alpha]))
          | arg_ty :: rest_tys ->
            (* Create lambda for this argument *)
            let x = Ident.fresh () in
            let y = Ident.fresh () in
            let ta = Ident.fresh () in
            let tb = Ident.fresh () in
            (* The result type after applying this and all remaining arguments *)
            let result_ty = 
              if rest_tys = [] then Lang.Types.Convert.typ final_return_ty
              else List.fold_right (fun arg_ty acc -> 
                Common.Types.TyApp (Common.Types.TyApp (Common.Types.TyDef (Common.Types.Prim (Common.Types.Prim.fun_sym, Common.Types.KArrow (Common.Types.KStar, Common.Types.KArrow (Common.Types.KStar, Common.Types.KStar)))), Lang.Types.Convert.typ arg_ty), acc)
              ) rest_tys (Lang.Types.Convert.typ final_return_ty)
            in
            CT.Cocase [{
              CT.xtor = Common.Types.Prim.app_dtor_sym;
              CT.type_vars = [ta; tb];
              CT.variables = [x];
              CT.covariables = [y];
              CT.statement = CT.Cut (
                make_lambdas rest_tys (provided_args @ [Lang.Terms.TyTmVar (x, arg_ty)]),
                result_ty,
                CT.Covar y
              )
            }]
        in
        make_lambdas remaining_arg_types tm_args
      
      else
        (* Over-applied - this shouldn't happen in well-typed code *)
        failwith "convert: over-applied function (type checking should have caught this)"
    | _ ->
      (* General application using $app destructor *)
      let ty_arg = Lang.Terms.get_type u in
      let x = Ident.fresh () in
      (* μx.< conv t | $apply{ty_arg}{ty_ret}(x, conv u) > *)
      CT.Mu (x, CT.Cut (
        convert t,
        (* Function type: ty_arg -> ty_ret *)
        Common.Types.TyApp (Common.Types.TyApp (Common.Types.TyDef (Common.Types.Prim (Common.Types.Prim.fun_sym, Common.Types.KArrow (Common.Types.KStar, Common.Types.KArrow (Common.Types.KStar, Common.Types.KStar)))), Lang.Types.Convert.typ ty_arg), Lang.Types.Convert.typ ty_ret),
        CT.Destructor (Common.Types.Prim.app_dtor_sym, (
          [Lang.Types.Convert.typ ty_arg; Lang.Types.Convert.typ ty_ret],
          [CT.Var x],
          [CT.MuTilde (x, CT.Cut (convert u, Lang.Types.Convert.typ ty_arg, CT.Covar x))]
        ))
      ))
    )

  | Lang.Terms.TyTmIns (t, ty_arg, k, ty_result) ->
    (* Type instantiation: check if this is part of a function call pattern *)
    (* If t is a symbol or becomes a symbol after collecting args, handle as Call *)
    let (head, all_ty_args, all_tm_args) = collect_type_and_term_args (Lang.Terms.TyTmIns (t, ty_arg, k, ty_result)) in
    (match head with
    | Lang.Terms.TyTmSym (_, _) when all_ty_args <> [] && all_tm_args = [] ->
      (* Just type instantiation, no term args yet *)
      let x = Ident.fresh () in
      CT.Mu (x, CT.Cut (
        convert t,
        Common.Types.TyApp (Common.Types.TyDef (Common.Types.Prim (Common.Types.Prim.all_sym k, Common.Types.KArrow (Common.Types.KArrow (k, Common.Types.KStar), Common.Types.KStar))), Lang.Types.Convert.typ ty_result),
        CT.Destructor (Common.Types.Prim.ins_dtor_sym k, (
          [Lang.Types.Convert.typ ty_result; Lang.Types.Convert.typ ty_arg],
          [],
          [CT.Covar x]
        ))
      ))
    | _ ->
      (* Use old forall encoding *)
      let x = Ident.fresh () in
      CT.Mu (x, CT.Cut (
        convert t,
        Common.Types.TyApp (Common.Types.TyDef (Common.Types.Prim (Common.Types.Prim.all_sym k, Common.Types.KArrow (Common.Types.KArrow (k, Common.Types.KStar), Common.Types.KStar))), Lang.Types.Convert.typ ty_result),
        CT.Destructor (Common.Types.Prim.ins_dtor_sym k, (
          [Lang.Types.Convert.typ ty_result; Lang.Types.Convert.typ ty_arg],
          [],
          [CT.Covar x]
        ))
      ))
    )

  | Lang.Terms.TyTmLam (x, _a, body, _ty) ->
    let b = Lang.Terms.get_type body in
    let y = Ident.fresh () in
    let ta = Ident.fresh () in
    let tb = Ident.fresh () in
    (* new $fun{a}{b} { $apply{a}{b}(this, x, y) => < conv body | y > } *)
    CT.Cocase [{
      CT.xtor = Common.Types.Prim.app_dtor_sym;
      CT.type_vars = [ta; tb];
      CT.variables = [x];
      CT.covariables = [y];
      CT.statement = CT.Cut (convert body, Lang.Types.Convert.typ b, CT.Covar y)
    }]

  | Lang.Terms.TyTmAll ((a, k), body, _ty) ->
    let b = Lang.Terms.get_type body in
    let y = Ident.fresh () in
    (* new $forall{k} { $inst{a: k}(y) => < conv body | y > } *)
    CT.Cocase [{
      CT.xtor = Common.Types.Prim.ins_dtor_sym k;
      CT.type_vars = [a];
      CT.variables = [];
      CT.covariables = [y];
      CT.statement = CT.Cut (convert body, Lang.Types.Convert.typ b, CT.Covar y)
    }]

  | Lang.Terms.TyTmLet (x, t, u, ty) ->
    let t_ty = Lang.Terms.get_type t in
    let y = Ident.fresh () in
    (* μy.< conv t | μ̃x.< conv u | y > > *)
    CT.Mu (y, CT.Cut (
      convert t,
      Lang.Types.Convert.typ t_ty,
      CT.MuTilde (x, CT.Cut (convert u, Lang.Types.Convert.typ ty, CT.Covar y))
    ))

  | Lang.Terms.TyTmMatch (t, clauses, ty) ->
    let t_ty = Lang.Terms.get_type t in
    let y = Ident.fresh () in
    (* μy.< conv t | case { ctor_i{type_vars}(term_vars) => < conv body_i | y > } > *)
    let patterns = List.map (fun (xtor, type_vars, term_vars, body) ->
      { CT.xtor = xtor.Lang.Types.symbol
      ; CT.type_vars = type_vars
      ; CT.variables = term_vars
      ; CT.covariables = []  (* Case patterns don't have covariables *)
      ; CT.statement = CT.Cut (convert body, Lang.Types.Convert.typ ty, CT.Covar y)
      }
    ) clauses in
    CT.Mu (y, CT.Cut (
      convert t,
      Lang.Types.Convert.typ t_ty,
      CT.Case patterns
    ))

  | Lang.Terms.TyTmNew (_ty_opt, clauses, _ty) ->
    (* In Lang: new stream(a) { head{_} => x ; tail{_} => const_stream(x) }
       In Core: cocase { head{a}(k) => <x | k> ; tail{a}(k) => <...| k> }
       
       Note: In Lang, self is implicit (not in pattern bindings).
       In Core, cocase patterns have NO producer variables (no self).
       They only have consumer variables for the return continuation.
       Self appears in destructor APPLICATIONS, not in cocase pattern definitions.
       
       Extract type arguments from the result type to use as type variables in patterns.
       For `new stream(a)`, the type is `TyApp(TyCtor(stream), TyVar(a))`, so we extract `[a]`.
    *)
    let rec extract_type_vars (ty: Lang.Types.typ) : Ident.t list =
      match ty with
      | Lang.Types.TyVar x -> [x]
      | Lang.Types.TyApp (t1, t2) -> extract_type_vars t1 @ extract_type_vars t2
      | _ -> []
    in
    let type_vars_from_result = extract_type_vars _ty in
    
    let patterns = List.map (fun (xtor, _lang_type_vars, term_vars, body) ->
      let body_ty = Lang.Terms.get_type body in
      let y = Ident.fresh () in
      { CT.xtor = xtor.Lang.Types.symbol
      ; CT.type_vars = type_vars_from_result  (* Use type vars from result type, not Lang pattern *)
      ; CT.variables = term_vars  (* Just the non-return arguments (empty for head/tail) *)
      ; CT.covariables = [y]
      ; CT.statement = CT.Cut (convert body, Lang.Types.Convert.typ body_ty, CT.Covar y)
      }
    ) clauses in
    CT.Cocase patterns

  | Lang.Terms.TyTmCtor (ctor, ty_args, tm_args, _ty) ->
    (* ctor{(Convert.typ ty_args)}((conv tm_args), []) *)
    CT.Constructor (ctor.Lang.Types.symbol, (
      List.map Lang.Types.Convert.typ ty_args,
      List.map convert tm_args,
      []
    ))

  | Lang.Terms.TyTmDtor (dtor, ty_args, tm_args, _ty) ->
    (* The first tm_arg should be 'self' *)
    (match tm_args with
    | [] -> failwith "convert: destructor must have at least 'self' argument"
    | self :: rest ->
      let self_ty = Lang.Terms.get_type self in
      let y = Ident.fresh () in
      (* μy.< conv self | dtor{(Convert.typ ty_args)}((conv rest), y) > *)
      CT.Mu (y, CT.Cut (
        convert self,
        Lang.Types.Convert.typ self_ty,
        CT.Destructor (dtor.Lang.Types.symbol, (
          List.map Lang.Types.Convert.typ ty_args,
          List.map convert rest,
          [CT.Covar y]
        ))
      ))
    )

(* Convert a typed term definition to a Core term definition *)
let convert_term_def (td: Lang.Terms.typed_term_def) : CT.term_def =
  (* Producer arguments: for each term argument (x: t), create (x: Prd (convert t)) *)
  let prod_args = List.map (fun (x, ty) ->
    (x, Lang.Types.Convert.typ ty)
  ) td.Lang.Terms.term_args in
  
  (* Consumer argument: create a fresh covariable α: Cns (convert return_type) *)
  let alpha = Ident.fresh () in
  let cons_args = [(alpha, Lang.Types.Convert.typ td.Lang.Terms.return_type)] in
  
  (* Body: convert the body directly without type abstraction wrapper *)
  (* In Core, type parameters are part of the function signature, not the body *)
  let body_producer = convert td.Lang.Terms.body in
  
  let body_statement =
    CT.Cut (body_producer, Lang.Types.Convert.typ td.Lang.Terms.return_type, CT.Covar alpha)
  in
  
  { CT.name = td.Lang.Terms.name
  ; CT.type_args = td.Lang.Terms.type_args  (* Keep type parameters in signature *)
  ; CT.prod_args = prod_args
  ; CT.cons_args = cons_args
  ; CT.return_type = Lang.Types.Convert.typ td.Lang.Terms.return_type
  ; CT.body = body_statement
  }

(* Collect all kinds used in TyTmAll nodes *)
let rec collect_forall_kinds (tm: Lang.Terms.typed_term) : Common.Types.kind list =
  match tm with
  | Lang.Terms.TyTmInt _ -> []
  | Lang.Terms.TyTmVar _ -> []
  | Lang.Terms.TyTmSym _ -> []
  | Lang.Terms.TyTmApp (t, u, _) ->
    collect_forall_kinds t @ collect_forall_kinds u
  | Lang.Terms.TyTmIns (t, _, _, _) ->
    collect_forall_kinds t
  | Lang.Terms.TyTmLam (_, _, body, _) ->
    collect_forall_kinds body
  | Lang.Terms.TyTmAll ((_, k), body, _) ->
    k :: collect_forall_kinds body
  | Lang.Terms.TyTmLet (_, t, u, _) ->
    collect_forall_kinds t @ collect_forall_kinds u
  | Lang.Terms.TyTmMatch (t, clauses, _) ->
    let clause_kinds = List.concat_map (fun (_, _, _, body) ->
      collect_forall_kinds body
    ) clauses in
    collect_forall_kinds t @ clause_kinds
  | Lang.Terms.TyTmNew (_, clauses, _) ->
    List.concat_map (fun (_, _, _, body) ->
      collect_forall_kinds body
    ) clauses
  | Lang.Terms.TyTmCtor (_, _, args, _) ->
    List.concat_map collect_forall_kinds args
  | Lang.Terms.TyTmDtor (_, _, args, _) ->
    List.concat_map collect_forall_kinds args

let collect_all_forall_kinds (defs: Lang.Terms.typed_definitions) : Common.Types.kind list =
  let kinds = List.concat_map (fun (_, td) ->
    collect_forall_kinds td.Lang.Terms.body
  ) defs.Lang.Terms.term_defs in
  (* Remove duplicates by converting to a set-like structure *)
  let rec unique = function
    | [] -> []
    | k :: rest ->
      if List.mem k rest then unique rest
      else k :: unique rest
  in
  unique kinds

(* Convert typed definitions to Core definitions *)
let convert_definitions (defs: Lang.Terms.typed_definitions) : CT.definitions =
  let core_term_defs = List.map (fun (path, td) ->
    (path, convert_term_def td)
  ) defs.Lang.Terms.term_defs in
  
  (* Convert type definitions *)
  let core_type_defs = List.map (fun (path, (ty_def, kind)) ->
    match ty_def with
    | Lang.Types.Data td ->
      (path, (Common.Types.Data (Lang.Types.Convert.data_to_sc td), kind))
    | Lang.Types.Code td ->
      (path, (Common.Types.Code (Lang.Types.Convert.code_to_sc td), kind))
    | Lang.Types.Prim (s, k) ->
      (path, (Common.Types.Prim (s, k), kind))
  ) defs.Lang.Terms.type_defs in
  
  (* Collect all kinds used in TyTmAll and generate $forall{k} definitions *)
  let forall_kinds = collect_all_forall_kinds defs in
  let forall_type_defs = List.map (fun k ->
    let a = Ident.fresh () in
    let forall_def = Common.Types.Prim.all_def a k in
    let forall_kind = Common.Types.KArrow (Common.Types.KArrow (k, Common.Types.KStar), Common.Types.KStar) in
    (Common.Types.Prim.all_sym k, (forall_def, forall_kind))
  ) forall_kinds in
  
  (* Add primitive type definitions (int, $fun) and $forall{k} types *)
  let all_type_defs = Common.Types.primitive_ty_defs @ forall_type_defs @ core_type_defs in
  
  { CT.type_defs = all_type_defs
  ; CT.term_defs = core_term_defs
  }
