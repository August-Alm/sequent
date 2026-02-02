(**
  Module: Collapsing
  Pass 2: Collapsing (Core -> Cut)
  
  Applies the 4 symmetric transformation rules from normalization.txt:
  
  ⟨C(Γ) | µ˜x.s ⟩                & ⟨µα.s |D(Γ)⟩                      → let v = m(Γ); s
  ⟨x | case {C(Γ) ⇒ s, ... }⟩    & ⟨cocase {D(Γ) ⇒ s, ... } | α⟩     → switch v {m(Γ) ⇒ s, ...}
  ⟨µα.s | case {C(Γ) ⇒ s, ... }⟩ & ⟨cocase {D(Γ) ⇒ s, ... } | µ˜x.s⟩ → new v = {m(Γ) ⇒ s, ...}; s
  ⟨C(Γ) | α⟩                     & ⟨x | D(Γ)⟩                        → invoke v m(Γ)
  
  Key insight: Variables change chirality during collapse:
  - let v = ... → v is Prd (producer)
  - switch v ... → v is Prd (producer)  
  - new v = ... → v is Cns (consumer)
  - invoke v ... → v is Cns (consumer)
*)

open Common.Identifiers
open Common.Types
module CT = Core.Terms
module CutT = Cut.Terms
module CutTypes = Cut.Types

type collapse_context = {
  defs: CT.definitions;
  chirality_reqs: Shrinking.chirality_context;
  signatures: CutTypes.signature_defs;
}

(** Simple dummy type for now - avoids infinite recursion in type conversion *)
let dummy_type = CutTypes.TyPrim (Path.of_primitive 0 "_", CutTypes.KStar)

(** Convert Core kind to Cut kind *)
let rec core_kind_to_cut_kind (k: kind) : CutTypes.kind =
  match k with
  | KStar -> CutTypes.KStar
  | KArrow (k1, k2) -> CutTypes.KArrow (core_kind_to_cut_kind k1, core_kind_to_cut_kind k2)

(** Extract Cut signature from Core type declaration *)
let rec extract_cut_signature (ty_defs: ty_defs) (td: ty_dec) : CutTypes.signature =
  { symbol = td.symbol
  ; parameters = List.filter_map (fun (ty_opt, k) ->
      match ty_opt with
      | Some (TyVar id) -> Some (id, core_kind_to_cut_kind k)
      | _ -> None
    ) td.arguments
  ; methods = List.map (fun xtor -> {
      CutTypes.parent = xtor.parent;
      symbol = xtor.symbol;
      quantified = List.map (fun (id, k) -> (id, core_kind_to_cut_kind k)) xtor.quantified;
      producers = List.map (fun ty -> (Ident.mk "_p", CutTypes.Prd (core_type_to_cut_type_inner ty_defs ty))) xtor.producers;
      consumers = List.map (fun ty -> (Ident.mk "_c", CutTypes.Cns (core_type_to_cut_type_inner ty_defs ty))) xtor.consumers;
      result_type = (match xtor.arguments with
        | ty :: _ -> core_type_to_cut_type_inner ty_defs ty
        | [] -> dummy_type);
      constraints = [];
    }) td.xtors
  }

(** Convert Core type to Cut type - used for types appearing inside signatures *)
and core_type_to_cut_type_inner (ty_defs: ty_defs) (ty: typ) : CutTypes.typ =
  match ty with
  | TySym path -> 
    (* When appearing inside signatures, just convert to type application or primitive *)
    (match List.assoc_opt path ty_defs with
    | Some (Prim (p, k), _) -> CutTypes.TyPrim (p, core_kind_to_cut_kind k)
    | _ -> CutTypes.TyPrim (path, CutTypes.KStar))  (* Keep as primitive reference *)
  | TyVar id -> CutTypes.TyVar id
  | TyApp (t1, t2) -> CutTypes.TyApp (core_type_to_cut_type_inner ty_defs t1, core_type_to_cut_type_inner ty_defs t2)
  | TyDef (Prim (path, kind)) -> CutTypes.TyPrim (path, core_kind_to_cut_kind kind)
  | TyDef (Data td) -> CutTypes.TyPrim (td.symbol, CutTypes.KStar)  (* Don't recurse *)
  | TyDef (Code td) -> CutTypes.TyPrim (td.symbol, CutTypes.KStar)  (* Don't recurse *)

(** Convert Core type to Cut type *)
and core_type_to_cut_type (ty_defs: ty_defs) (ty: typ) : CutTypes.typ =
  match ty with
  | TySym path ->
    (* Look up the type symbol in definitions *)
    (match List.assoc_opt path ty_defs with
    | Some (Data td, _) -> CutTypes.TySig (extract_cut_signature ty_defs td)
    | Some (Code td, _) -> CutTypes.TySig (extract_cut_signature ty_defs td)
    | Some (Prim (p, k), _) -> CutTypes.TyPrim (p, core_kind_to_cut_kind k)
    | None -> dummy_type)  (* Unknown type, use dummy *)
  | TyVar id -> CutTypes.TyVar id
  | TyApp (t1, t2) -> CutTypes.TyApp (core_type_to_cut_type ty_defs t1, core_type_to_cut_type ty_defs t2)
  | TyDef (Prim (path, kind)) -> CutTypes.TyPrim (path, core_kind_to_cut_kind kind)
  | TyDef (Data td) -> CutTypes.TySig (extract_cut_signature ty_defs td)
  | TyDef (Code td) -> CutTypes.TySig (extract_cut_signature ty_defs td)

(** Look up constructor/destructor and get typed parameters *)
let get_xtor_types (ctx: collapse_context) (xtor_symbol: Path.t) : (typ list * typ list) option =
  (* Search through all type definitions for the constructor/destructor *)
  List.find_map (fun (_, (ty_def, _)) ->
    match ty_def with
    | Data td | Code td ->
      List.find_map (fun xtor ->
        if Path.equal xtor.symbol xtor_symbol then
          Some (xtor.producers, xtor.consumers)
        else None
      ) td.xtors
    | Prim _ -> None
  ) ctx.defs.type_defs

(** Look up method signature from extracted signatures and get the actual parameter identifiers *)
let get_method_params (sigs: CutTypes.signature_defs) (method_symbol: Path.t) 
    : (CutTypes.typed_param list * CutTypes.typed_param list) option =
  (* Search through all signatures for the method *)
  List.find_map (fun (_, (sig_def, _)) ->
    List.find_map (fun msig ->
      if Path.equal msig.CutTypes.symbol method_symbol then
        Some (msig.CutTypes.producers, msig.CutTypes.consumers)
      else None
    ) sig_def.CutTypes.methods
  ) sigs




(** Main collapsing transformation *)
let rec collapse_statement (ctx: collapse_context) (s: CT.statement) : CutT.statement =
  match s with
  | CT.Cut (p, ty, c) -> collapse_cut ctx p ty c
  | CT.Call (f, _ty_args, prods, cons) ->
    let args = (List.map (function 
      | CT.Var x -> x 
      | _ -> failwith "Expected variable after shrinking") prods) @
      (List.map (function 
      | CT.Covar a -> a 
      | _ -> failwith "Expected covariable after shrinking") cons) in
    (* Call needs to be converted to invoke on first arg *)
    if args = [] then failwith "Empty call"
    else CutT.Invoke (List.hd args, f, [], List.tl args)

(** Collapse a cut into one of the 4 symmetric forms *)
and collapse_cut (ctx: collapse_context) (p: CT.producer) (_ty: Common.Types.typ) (c: CT.consumer) : CutT.statement =
  match (p, c) with
  
  (* FORM 1: ⟨C(Γ) | µ˜x.s⟩ → let x = C(Γ); s 
     x becomes a PRODUCER *)
  | (CT.Constructor (ctor, (_ty_args, prods, cons)), CT.MuTilde (x, s)) ->
    let args_env = 
      (List.map (fun p -> match p with 
        | CT.Var v -> (v, CutTypes.Prd (CutTypes.TyPrim (Path.of_primitive 0 "_", CutTypes.KStar)))
        | _ -> failwith "Expected variable") prods) @
      (List.map (fun c -> match c with
        | CT.Covar a -> (a, CutTypes.Cns (CutTypes.TyPrim (Path.of_primitive 0 "_", CutTypes.KStar)))
        | _ -> failwith "Expected covariable") cons) in
    CutT.Let (x, ctor, [], args_env, collapse_statement ctx s)
  
  (* FORM 1: ⟨µα.s | D(Γ)⟩ → let α = D(Γ); s 
     α becomes a PRODUCER *)
  | (CT.Mu (alpha, s), CT.Destructor (dtor, (_ty_args, prods, cons))) ->
    let args_env =
      (List.map (fun p -> match p with
        | CT.Var v -> (v, CutTypes.Prd (CutTypes.TyPrim (Path.of_primitive 0 "_", CutTypes.KStar)))
        | _ -> failwith "Expected variable") prods) @
      (List.map (fun c -> match c with
        | CT.Covar a -> (a, CutTypes.Cns (CutTypes.TyPrim (Path.of_primitive 0 "_", CutTypes.KStar)))
        | _ -> failwith "Expected covariable") cons) in
    CutT.Let (alpha, dtor, [], args_env, collapse_statement ctx s)
  
  (* FORM 2: ⟨x | case {C(Γ) ⇒ s, ...}⟩ → switch x {C(Γ) ⇒ s, ...} 
     x is a PRODUCER *)
  | (CT.Var x, CT.Case patterns) ->
    let branches = List.map (fun (pat: CT.pattern) ->
      (* Build branch environment using pattern variables with types from signature *)
      let args_env = match get_method_params ctx.signatures pat.CT.xtor with
        | Some (prod_params, cons_params) ->
          (* Use pattern variables with types from signature *)
          (List.map2 (fun v (_, chi_ty) -> (v, chi_ty)) pat.CT.variables prod_params) @
          (List.map2 (fun a (_, chi_ty) -> (a, chi_ty)) pat.CT.covariables cons_params)
        | None ->
          (* Fallback: use pattern variables with dummy types *)
          (List.map (fun v -> (v, CutTypes.Prd dummy_type)) pat.CT.variables) @
          (List.map (fun a -> (a, CutTypes.Cns dummy_type)) pat.CT.covariables)
      in
      (* Collapse the statement - linearization will handle substitutions *)
      let body = collapse_statement ctx pat.CT.statement in
      (pat.CT.xtor, [], args_env, body)
    ) patterns in
    CutT.Switch (x, branches)
  
  (* FORM 2: ⟨cocase {D(Γ) ⇒ s, ...} | α⟩ → switch α {D(Γ) ⇒ s, ...} 
     α (covariable) becomes variable and is a PRODUCER *)
  | (CT.Cocase patterns, CT.Covar alpha) ->
    let branches = List.map (fun (pat: CT.pattern) ->
      (* Build branch environment using pattern variables with types from signature *)
      let args_env = match get_method_params ctx.signatures pat.CT.xtor with
        | Some (prod_params, cons_params) ->
          (* Use pattern variables with types from signature *)
          (List.map2 (fun v (_, chi_ty) -> (v, chi_ty)) pat.CT.variables prod_params) @
          (List.map2 (fun a (_, chi_ty) -> (a, chi_ty)) pat.CT.covariables cons_params)
        | None ->
          (List.map (fun v -> (v, CutTypes.Prd dummy_type)) pat.CT.variables) @
          (List.map (fun a -> (a, CutTypes.Cns dummy_type)) pat.CT.covariables)
      in
      (* Collapse the statement - linearization will handle substitutions *)
      let body = collapse_statement ctx pat.CT.statement in
      (pat.CT.xtor, [], args_env, body)
    ) patterns in
    CutT.Switch (alpha, branches)
  
  (* FORM 3: ⟨µα.s1 | case {C(Γ) ⇒ s2, ...}⟩ → new α = {C(Γ) ⇒ s2, ...}; s1 
     α is a CONSUMER *)
  | (CT.Mu (alpha, s1), CT.Case patterns) ->
    let branches = List.map (fun (pat: CT.pattern) ->
      let args_env = match get_method_params ctx.signatures pat.CT.xtor with
        | Some (prod_params, cons_params) ->
          (List.map2 (fun v (_, chi_ty) -> (v, chi_ty)) pat.CT.variables prod_params) @
          (List.map2 (fun a (_, chi_ty) -> (a, chi_ty)) pat.CT.covariables cons_params)
        | None ->
          (List.map (fun v -> (v, CutTypes.Prd dummy_type)) pat.CT.variables) @
          (List.map (fun a -> (a, CutTypes.Cns dummy_type)) pat.CT.covariables)
      in
      let body = collapse_statement ctx pat.CT.statement in
      (pat.CT.xtor, [], args_env, body)
    ) patterns in
    CutT.New (alpha, dummy_type, [], branches, collapse_statement ctx s1)
  
  (* FORM 3: ⟨cocase {D(Γ) ⇒ s2, ...} | µ˜x.s1⟩ → new x = {D(Γ) ⇒ s2, ...}; s1 
     x is a CONSUMER *)
  | (CT.Cocase patterns, CT.MuTilde (x, s1)) ->
    let branches = List.map (fun (pat: CT.pattern) ->
      let args_env = match get_method_params ctx.signatures pat.CT.xtor with
        | Some (prod_params, cons_params) ->
          (List.map2 (fun v (_, chi_ty) -> (v, chi_ty)) pat.CT.variables prod_params) @
          (List.map2 (fun a (_, chi_ty) -> (a, chi_ty)) pat.CT.covariables cons_params)
        | None ->
          (List.map (fun v -> (v, CutTypes.Prd dummy_type)) pat.CT.variables) @
          (List.map (fun a -> (a, CutTypes.Cns dummy_type)) pat.CT.covariables)
      in
      let body = collapse_statement ctx pat.CT.statement in
      (pat.CT.xtor, [], args_env, body)
    ) patterns in
    CutT.New (x, dummy_type, [], branches, collapse_statement ctx s1)
  
  (* FORM 4: ⟨C(Γ) | α⟩ → invoke α C(Γ) 
     α (covariable) becomes variable and is a CONSUMER *)
  | (CT.Constructor (ctor, (_ty_args, prods, cons)), CT.Covar alpha) ->
    let args = 
      (List.map (function CT.Var v -> v | _ -> failwith "Expected variable") prods) @
      (List.map (function CT.Covar a -> a | _ -> failwith "Expected covariable") cons) in
    CutT.Invoke (alpha, ctor, [], args)
  
  (* FORM 4: ⟨x | D(Γ)⟩ → invoke x D(Γ) 
     x is a CONSUMER *)
  | (CT.Var x, CT.Destructor (dtor, (_ty_args, prods, cons))) ->
    let args =
      (List.map (function CT.Var v -> v | _ -> failwith "Expected variable") prods) @
      (List.map (function CT.Covar a -> a | _ -> failwith "Expected covariable") cons) in
    CutT.Invoke (x, dtor, [], args)
  
  (* Fallback: Should have been handled by shrinking phase *)
  | (CT.Var x, CT.Covar alpha) ->
    failwith (Printf.sprintf "Unexpected cut form: ⟨%s | %s⟩ - should have been η-expanded in shrinking"
      (Ident.name x) (Ident.name alpha))
  | _ -> failwith "Unexpected cut form after shrinking"

(** Collapse a term definition into a Cut label definition *)
let collapse_term_def (ctx: collapse_context) (name: Path.t) (def: CT.term_def) : CutT.label * CutT.typ_env * CutT.statement =
  let label = CutT.MkLabel name in
  
  (* Build environment with chirality information - producers are Prd, consumers are Cns *)
  let typ_env = 
    (List.map (fun (v, ty) -> (v, CutTypes.Prd (core_type_to_cut_type ctx.defs.type_defs ty))) def.prod_args) @
    (List.map (fun (v, ty) -> (v, CutTypes.Cns (core_type_to_cut_type ctx.defs.type_defs ty))) def.cons_args) in
  
  let body = collapse_statement ctx def.body in
  
  (label, typ_env, body)

(** Extract signatures from Core type definitions *)
let extract_signatures_from_defs (defs: CT.definitions) : CutTypes.signature_defs =
  List.filter_map (fun (_, (ty_def, _)) ->
    match ty_def with
    | Data td -> 
      let sig_def = extract_cut_signature defs.type_defs td in
      let kind = List.fold_right (fun (_, k) acc -> 
        CutTypes.KArrow (core_kind_to_cut_kind k, acc)
      ) td.arguments CutTypes.KStar in
      Some (td.symbol, (sig_def, kind))
    | Code td -> 
      let sig_def = extract_cut_signature defs.type_defs td in
      let kind = List.fold_right (fun (_, k) acc -> 
        CutTypes.KArrow (core_kind_to_cut_kind k, acc)
      ) td.arguments CutTypes.KStar in
      Some (td.symbol, (sig_def, kind))
    | Prim _ -> None
  ) defs.type_defs

(** Entry point *)
let collapse_definitions (defs: CT.definitions) (chirality_reqs: Shrinking.chirality_context) 
  : CutT.definitions =
  let signatures = extract_signatures_from_defs defs in
  let ctx = { defs; chirality_reqs; signatures } in
  
  let program = List.map (fun (name, def) -> collapse_term_def ctx name def) defs.term_defs in
  
  { CutT.signatures; program }
