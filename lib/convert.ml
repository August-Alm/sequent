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
  | Lang.Types.TyFun (_, t2) -> 1 + count_fun_arrows t2
  | _ -> 0

(* Helper: Collect arguments from nested applications *)
let rec collect_args (tm: Lang.Terms.typed_term) : (Lang.Terms.typed_term * Lang.Terms.typed_term list) =
  match tm with
  | Lang.Terms.TyTmApp (t, u, _) ->
    let (head, args) = collect_args t in
    (head, args @ [u])
  | _ -> (tm, [])

(* Helper: Get function argument types from a function type *)
let rec get_arg_types (ty: Lang.Types.typ) : Lang.Types.typ list =
  match ty with
  | Lang.Types.TyFun (t1, t2) -> t1 :: get_arg_types t2
  | _ -> []

let rec convert (tm: Lang.Terms.typed_term) : CT.producer =
  match tm with
  | Lang.Terms.TyTmInt (n, _ty) ->
    CT.Int n

  | Lang.Terms.TyTmVar (x, _ty) ->
    CT.Var x

  | Lang.Terms.TyTmSym (sym, ty) ->
    (* Check if this is a top-level constant (no arguments) *)
    let arity = count_fun_arrows ty in
    if arity = 0 then
      (* Top-level constant - treat as variable for now *)
      (* TODO: Could inline the body here if we had access to definitions *)
      (match Path.as_ident sym with
      | Some id -> CT.Var id
      | None -> CT.Var (Ident.mk (Path.name sym))
      )
    else
      (* Function symbol without application - treat as variable *)
      (match Path.as_ident sym with
      | Some id -> CT.Var id
      | None -> CT.Var (Ident.mk (Path.name sym))
      )

  | Lang.Terms.TyTmApp (t, u, ty_ret) ->
    (* Collect all arguments from nested applications *)
    let (head, args) = collect_args (Lang.Terms.TyTmApp (t, u, ty_ret)) in
    (match head with
    | Lang.Terms.TyTmSym (sym, sym_ty) ->
      (* This is an application of a top-level symbol *)
      let required_arity = count_fun_arrows sym_ty in
      let provided_arity = List.length args in
      
      if provided_arity = required_arity then
        (* Fully applied - generate Call statement *)
        let alpha = Ident.fresh () in
        CT.Mu (alpha, CT.Call (sym, List.map convert args, [CT.Covar alpha]))
      
      else if provided_arity < required_arity then
        (* Partially applied - generate lambda for remaining arguments *)
        (* foo(u) where foo: a -> b -> c becomes:
           fun (y: b) => foo(u, y) 
           which is: new { $app(this, y, α) => μβ.Call(foo, [u, y], [β]) | α } *)
        let arg_types = get_arg_types sym_ty in
        let remaining_arg_types = Utility.drop provided_arity arg_types in
        
        (* Generate nested lambdas for each remaining argument *)
        let rec make_lambdas remaining_tys provided_args =
          match remaining_tys with
          | [] -> 
            (* All arguments provided - make the call *)
            let alpha = Ident.fresh () in
            CT.Mu (alpha, CT.Call (sym, List.map convert provided_args, [CT.Covar alpha]))
          | arg_ty :: rest_tys ->
            (* Create lambda for this argument *)
            let x = Ident.fresh () in
            let y = Ident.fresh () in
            CT.Cocase [{
              CT.xtor = Common.Types.Prim.app_dtor_sym;
              CT.type_vars = [];
              CT.variables = [x];
              CT.covariables = [y];
              CT.statement = CT.Cut (
                make_lambdas rest_tys (provided_args @ [Lang.Terms.TyTmVar (x, arg_ty)]),
                CT.Covar y
              )
            }]
        in
        make_lambdas remaining_arg_types args
      
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
        CT.Destructor (Common.Types.Prim.app_dtor_sym, (
          [Lang.Types.Convert.typ ty_arg; Lang.Types.Convert.typ ty_ret],
          [CT.Var x],
          [CT.MuTilde (x, CT.Cut (convert u, CT.Covar x))]
        ))
      ))
    )

  | Lang.Terms.TyTmIns (t, ty_arg, ty_result) ->
    (* Type instantiation was already checked - extract the kind from ty_arg *)
    (* We need the kind k for the $inst destructor symbol *)
    let k = match t with
      | Lang.Terms.TyTmAll ((_, k), _, _) -> k
      | _ -> Common.Types.KStar  (* default to * if we can't determine *)
    in
    let x = Ident.fresh () in
    (* μx.< conv t | $inst{ty_result}{ty_arg}(x) > *)
    CT.Mu (x, CT.Cut (
      convert t,
      CT.Destructor (Common.Types.Prim.ins_dtor_sym k, (
        [Lang.Types.Convert.typ ty_result; Lang.Types.Convert.typ ty_arg],
        [],
        [CT.Covar x]
      ))
    ))

  | Lang.Terms.TyTmLam (x, _a, body, _ty) ->
    let _b = Lang.Terms.get_type body in
    let y = Ident.fresh () in
    (* new $fun{a}{b} { $apply{a}{b}(this, x, y) => < conv body | y > } *)
    CT.Cocase [{
      CT.xtor = Common.Types.Prim.app_dtor_sym;
      CT.type_vars = [];
      CT.variables = [x];
      CT.covariables = [y];
      CT.statement = CT.Cut (convert body, CT.Covar y)
    }]

  | Lang.Terms.TyTmAll ((a, k), body, _ty) ->
    let _b = Lang.Terms.get_type body in
    let y = Ident.fresh () in
    (* new $forall{k} { $inst{a: k}(y) => < conv body | y > } *)
    CT.Cocase [{
      CT.xtor = Common.Types.Prim.ins_dtor_sym k;
      CT.type_vars = [a];
      CT.variables = [];
      CT.covariables = [y];
      CT.statement = CT.Cut (convert body, CT.Covar y)
    }]

  | Lang.Terms.TyTmLet (x, t, u, _ty) ->
    let y = Ident.fresh () in
    (* μy.< conv t | μ̃x.< conv u | y > > *)
    CT.Mu (y, CT.Cut (
      convert t,
      CT.MuTilde (x, CT.Cut (convert u, CT.Covar y))
    ))

  | Lang.Terms.TyTmMatch (t, clauses, _ty) ->
    let y = Ident.fresh () in
    (* μy.< conv t | case { ctor_i{type_vars}(term_vars, y) => < conv body_i | y > } > *)
    let patterns = List.map (fun (xtor, type_vars, term_vars, body) ->
      { CT.xtor = xtor.Lang.Types.symbol
      ; CT.type_vars = type_vars
      ; CT.variables = term_vars
      ; CT.covariables = [y]
      ; CT.statement = CT.Cut (convert body, CT.Covar y)
      }
    ) clauses in
    CT.Mu (y, CT.Cut (
      convert t,
      CT.Case patterns
    ))

  | Lang.Terms.TyTmNew (_ty_opt, clauses, _ty) ->
    (* cocase { dtor_i{type_vars}(this, term_vars, y_i) => < conv body_i | y_i > } *)
    let patterns = List.map (fun (xtor, _type_vars, term_vars, body) ->
      (* Split term_vars into this and args *)
      let _this_var, arg_vars = match term_vars with
        | [] -> failwith "convert: destructor must have at least 'this' argument"
        | t :: rest -> t, rest
      in
      let y = Ident.fresh () in
      { CT.xtor = xtor.Lang.Types.symbol
      ; CT.type_vars = _type_vars
      ; CT.variables = arg_vars
      ; CT.covariables = [y]
      ; CT.statement = CT.Cut (convert body, CT.Covar y)
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
      let y = Ident.fresh () in
      (* μy.< conv self | dtor{(Convert.typ ty_args)}((conv rest), y) > *)
      CT.Mu (y, CT.Cut (
        convert self,
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
  
  (* Body: ⟨convert body | α⟩ *)
  let body_producer = convert td.Lang.Terms.body in
  let body_statement = CT.Cut (body_producer, CT.Covar alpha) in
  
  { CT.name = td.Lang.Terms.name
  ; CT.type_args = td.Lang.Terms.type_args
  ; CT.prod_args = prod_args
  ; CT.cons_args = cons_args
  ; CT.return_type = Lang.Types.Convert.typ td.Lang.Terms.return_type
  ; CT.body = body_statement
  }

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
  
  { CT.type_defs = core_type_defs
  ; CT.term_defs = core_term_defs
  }
