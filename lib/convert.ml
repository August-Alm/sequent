(**
  Module: Convert
  Description: Conversion from Lang terms to Core terms
*)

open Common.Identifiers

(* Conversion of Lang terms to Core terms *)
module CT = Core.Terms

let rec convert (tm: Lang.Terms.typed_term) : CT.producer =
  match tm with
  | Lang.Terms.TyTmInt (n, _ty) ->
    CT.Int n

  | Lang.Terms.TyTmVar (x, _ty) ->
    CT.Var x

  | Lang.Terms.TyTmSym (sym, _ty) ->
    (* Symbols become variables using the last component of the path *)
    (match Path.as_ident sym with
    | Some id -> CT.Var id
    | None ->
      (* If it's a dotted path, create a variable from the name *)
      CT.Var (Ident.mk (Path.name sym))
    )

  | Lang.Terms.TyTmApp (t, u, ty_ret) ->
    (* Application was already type-checked, we know it's valid *)
    (* Extract argument type from u and result type from the typed term *)
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
