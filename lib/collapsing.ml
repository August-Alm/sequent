(**
  Module: Collapsing
  Pass 2: Collapsing (Core -> Cut)
  
  ⟨C(Γ) | µ˜x.s ⟩                    → let_prd v = m(Γ); s
  ⟨x | case {C(Γ) ⇒ s, ... }⟩        → switch_prd v {m(Γ) ⇒ s, ...}
  ⟨µα.s | case {C(Γ) ⇒ s, ... }⟩     → new_cns v = {m(Γ) ⇒ s, ...}; s
  ⟨C(Γ) | α⟩                         → invoke_cns v m(Γ)
  
  ⟨µα.s |D(Γ)⟩                       → let_cns v = m(Γ); s
  ⟨cocase {D(Γ) ⇒ s, ... } | α⟩      → switch_cns v {m(Γ) ⇒ s, ...}
  ⟨cocase {D(Γ) ⇒ s, ... } | µ˜x.s⟩  → new_prd v = {m(Γ) ⇒ s, ...}; s
  ⟨x | D(Γ)⟩                         → invoke_prd v m(Γ)
*)

open Common.Identifiers
open Common.Types
module CT = Core.Terms
module CutT = Cut.Terms
module CutTypes = Cut.Types

type collapse_context =
  { defs: CT.definitions
  ; signatures: CutTypes.signature_defs
  ; typ_env: (Ident.t * CutTypes.chirality_type) list
  }

let get_chirality_opt (ctx: collapse_context) (x: Ident.t) : CutTypes.chirality_type option =
  let rec go typ_env x =
    match typ_env with
    | [] -> None
    | (y, chi_ty) :: rest -> if Ident.equal x y then Some chi_ty else go rest x
  in
  go ctx.typ_env x

(** Convert Core kind to Cut kind *)
let rec core_kind_to_cut_kind (k: kind) : CutTypes.kind =
  match k with
  | KStar -> CutTypes.KStar
  | KArrow (k1, k2) -> CutTypes.KArrow (core_kind_to_cut_kind k1, core_kind_to_cut_kind k2)

(** Extract Cut signature from Core type declaration *)
let rec extract_cut_signature (ty_defs: ty_defs) (td: ty_dec) : CutTypes.signature =
  { symbol = td.symbol
  ; parameters = List.map (fun (ty_opt, k) ->
      (Option.map (core_type_to_cut_type ty_defs) ty_opt, core_kind_to_cut_kind k)) td.arguments
  ; methods = List.map (fun xtor -> 
      (* Build unified environment with polarized types *)
      let prod_env = List.mapi (fun i ty -> 
        let var_name = Ident.mk (Printf.sprintf "p%d" i) in
        (var_name, CutTypes.Prd (core_type_to_cut_type_inner ty_defs (Some td.symbol) ty))
      ) xtor.producers in
      let cons_env = List.mapi (fun i ty ->
        let var_name = Ident.mk (Printf.sprintf "c%d" i) in
        (var_name, CutTypes.Cns (core_type_to_cut_type_inner ty_defs (Some td.symbol) ty))
      ) xtor.consumers in
      (* Build polarized result type *)
      let parent_ty = List.fold_left (fun acc arg ->
          Common.Types.TyApp (acc, arg)
        ) (Common.Types.TySym xtor.parent) xtor.arguments in
      let result_cut_type = core_type_to_cut_type_inner ty_defs (Some td.symbol) parent_ty in
      (* Determine if this is a constructor (producers, prd result) or destructor (consumers, cns result) *)
      let result_chirality = 
        if xtor.consumers = [] then CutTypes.Prd result_cut_type  (* constructor *)
        else CutTypes.Cns result_cut_type  (* destructor *)
      in
      {
        CutTypes.parent = xtor.parent;
        symbol = xtor.symbol;
        quantified = List.map (fun (id, k) -> (id, core_kind_to_cut_kind k)) xtor.quantified;
        environment = prod_env @ cons_env;
        result_type = result_chirality;
        constraints = None;
      }) td.xtors
  }

(** Convert Core type to Cut type - used for types appearing inside signatures
    @param ty_defs Type definitions
    @param inside_decl If Some(symbol), we're inside this type declaration and shouldn't expand it
    @param ty The type to convert
*)
and core_type_to_cut_type_inner (ty_defs: ty_defs) (inside_decl: Path.t option) (ty: typ) : CutTypes.typ =
  match ty with
  | TySym path -> 
    (* Check if this is the type we're currently defining - if so, create reference *)
    (match inside_decl with
    | Some parent when Path.equal path parent ->
      (* We're referencing the parent type from inside its own declaration - use symbol reference *)
      CutTypes.TySym path
    | _ ->
      (* Different type or not inside a declaration - expand normally *)
      (match get_def_opt ty_defs path with
      | Some (Data td, _) -> CutTypes.TyDef (extract_cut_signature ty_defs td)
      | Some (Code td, _) -> CutTypes.TyDef (extract_cut_signature ty_defs td)
      | Some (Prim (p, k), _) -> CutTypes.TyPrim (p, core_kind_to_cut_kind k)
      | None -> failwith (Printf.sprintf "Unknown type symbol: %s" (Path.name path))))
  | TyVar id -> CutTypes.TyVar id
  | TyApp (t1, t2) -> CutTypes.TyApp (core_type_to_cut_type_inner ty_defs inside_decl t1, core_type_to_cut_type_inner ty_defs inside_decl t2)
  | TyDef (Prim (path, kind)) -> CutTypes.TyPrim (path, core_kind_to_cut_kind kind)
  | TyDef (Data td) -> CutTypes.TyDef (extract_cut_signature ty_defs td)
  | TyDef (Code td) -> CutTypes.TyDef (extract_cut_signature ty_defs td)

(** Convert Core type to Cut type *)
and core_type_to_cut_type (ty_defs: ty_defs) (ty: typ) : CutTypes.typ =
  match ty with
  | TySym path ->
    (* Look up the type symbol in definitions *)
    (match get_def_opt ty_defs path with
    | Some (Data td, _) -> CutTypes.TyDef (extract_cut_signature ty_defs td)
    | Some (Code td, _) -> CutTypes.TyDef (extract_cut_signature ty_defs td)
    | Some (Prim (p, k), _) -> CutTypes.TyPrim (p, core_kind_to_cut_kind k)
    | None -> failwith (Printf.sprintf "Unknown type symbol: %s" (Path.name path)))
  | TyVar id -> CutTypes.TyVar id
  | TyApp (t1, t2) -> CutTypes.TyApp (core_type_to_cut_type ty_defs t1, core_type_to_cut_type ty_defs t2)
  | TyDef (Prim (path, kind)) -> CutTypes.TyPrim (path, core_kind_to_cut_kind kind)
  | TyDef (Data td) -> CutTypes.TyDef (extract_cut_signature ty_defs td)
  | TyDef (Code td) -> CutTypes.TyDef (extract_cut_signature ty_defs td)

(** Extract type arguments from an applied type *)
let rec extract_type_args (type_defs: ty_defs) (ty: Common.Types.typ) : CutTypes.typ list =
  match ty with
  | Common.Types.TyApp (t1, t2) ->
    (* Recursively extract type arguments from type applications *)
    extract_type_args type_defs t1 @ [core_type_to_cut_type type_defs t2]
  | _ -> []

(** Extract type arguments from a type, keeping them as Core types for substitution *)
let rec extract_core_type_args (ty: Common.Types.typ) : Common.Types.typ list =
  match ty with
  | Common.Types.TyApp (t1, t2) ->
    extract_core_type_args t1 @ [t2]
  | _ -> []

(** Main collapsing transformation *)
let rec collapse_statement (ctx: collapse_context) (s: CT.statement) : CutT.statement =
  match s with
  | CT.Cut (p, ty, c) -> collapse_cut ctx p ty c
  | CT.Add (p1, p2, c) ->
    (* Convert Add statement to extern call: add(n1, n2, α) *)
    let n1 = (match p1 with
      | CT.Int n -> n
      | CT.Var x -> failwith ("Expected integer literal in Add, got variable " ^ Ident.name x)
      | _ -> failwith "Expected integer literal in Add after shrinking") in
    let n2 = (match p2 with
      | CT.Int n -> n
      | CT.Var x -> failwith ("Expected integer literal in Add, got variable " ^ Ident.name x)
      | _ -> failwith "Expected integer literal in Add after shrinking") in
    let v = Ident.fresh () in
    let n = Ident.mk (string_of_int (n1 + n2)) in
    let int_ty = Common.Types.TyDef (Common.Types.Prim.int_def) in
    let int_ty_cut = CutTypes.Ext.int_typ in
    let s = collapse_cut ctx (CT.Var n) int_ty c in
    CutT.Extern (Common.Types.Prim.add_sym, [v], [[(n, CutTypes.Ext int_ty_cut)], s])
  | CT.Call (f, ty_args, prods, cons) ->
    (* Call f[τ̄](x̄, ᾱ) compiles to: substitute [params → args]; jump f[τ̄] *)
    
    let ty_args_cut = List.map (core_type_to_cut_type ctx.defs.type_defs) ty_args in
    (* Extract actual argument variables *)
    let arg_vars = (List.map (function 
      | CT.Var x -> x 
      | _ -> failwith "Expected variable after shrinking in Call collapse (prods)") prods) @
      (List.map (function 
      | CT.Covar a -> a 
      | _ -> failwith "Expected covariable after shrinking") cons) in
    (* Look up target function's parameter names *)
    let target_def = CT.get_term_def ctx.defs f in
    let target_params = (List.map fst target_def.prod_args) @ (List.map fst target_def.cons_args) in
    (* Build substitution: target params ← actual args *)
    let subst = List.combine target_params arg_vars in
    CutT.Substitute (subst, CutT.Jump (CutT.MkLabel f, ty_args_cut))

(** Collapse a cut into one of the 4 symmetric forms *)
and collapse_cut (ctx: collapse_context) (p: CT.producer) (ty: Common.Types.typ) (c: CT.consumer) : CutT.statement =
  (* Extract type arguments from the cut type for instantiation *)
  let type_args_cut = extract_type_args ctx.defs.type_defs ty in
  let type_args_core = extract_core_type_args ty in
  
  match (p, c) with
  
  (* FORM 1a: ⟨C(Γ) | µ˜x.s⟩ → let x = C(Γ); s 
     x becomes a PRODUCER *)
  | (CT.Constructor (ctor, (_ty_args, prods, cons)), CT.MuTilde (x, s)) ->
    (* Get constructor info from Core type definitions *)
    let xtor_decl = CT.get_xtor ctx.defs ctor in
    (* Build type substitution from quantified variables to provided type_args *)
    let ty_subst = if List.length type_args_core = List.length xtor_decl.quantified then
      List.fold_left2 (fun acc (tv, _) ty ->
        Ident.add tv ty acc
      ) Ident.emptytbl xtor_decl.quantified type_args_core
    else
      Ident.emptytbl
    in
    (* Apply substitution to producer and consumer types *)
    let prod_types = List.map (Type.subst ty_subst) xtor_decl.producers in
    let cons_types = List.map (Type.subst ty_subst) xtor_decl.consumers in
    (* Convert to Cut types *)
    let prod_types_cut = List.map (core_type_to_cut_type ctx.defs.type_defs) prod_types in
    let cons_types_cut = List.map (core_type_to_cut_type ctx.defs.type_defs) cons_types in
    (* Get Core variable identifiers *)
    let prod_ids = List.map (fun p -> match p with 
      | CT.Var v -> v
      | _ -> failwith "Expected variable") prods in
    let cons_ids = List.map (fun c -> match c with
      | CT.Covar a -> a
      | _ -> failwith "Expected covariable") cons in
    (* Pair Core IDs with instantiated types *)
    let args_env = (List.map2 (fun id ty -> (id, CutTypes.Prd ty)) prod_ids prod_types_cut) @
                   (List.map2 (fun id ty -> (id, CutTypes.Cns ty)) cons_ids cons_types_cut) in
    CutT.LetPrd (x, ctor, type_args_cut, args_env, collapse_statement ctx s)
  
  (* FORM 1b: ⟨µα.s | D(Γ)⟩ → letcns α = D(Γ); s 
     α becomes a CONSUMER (dual of Form 1a) *)
  | (CT.Mu (alpha, s), CT.Destructor (dtor, (_ty_args, prods, cons))) ->
    (* Get destructor info from Core type definitions *)
    let xtor_decl = CT.get_xtor ctx.defs dtor in
    (* Build type substitution from quantified variables to provided type_args *)
    let ty_subst = if List.length type_args_core = List.length xtor_decl.quantified then
      List.fold_left2 (fun acc (tv, _) ty ->
        Ident.add tv ty acc
      ) Ident.emptytbl xtor_decl.quantified type_args_core
    else
      Ident.emptytbl
    in
    (* Apply substitution to producer and consumer types *)
    let prod_types = List.map (Type.subst ty_subst) xtor_decl.producers in
    let cons_types = List.map (Type.subst ty_subst) xtor_decl.consumers in
    (* Convert to Cut types *)
    let prod_types_cut = List.map (core_type_to_cut_type ctx.defs.type_defs) prod_types in
    let cons_types_cut = List.map (core_type_to_cut_type ctx.defs.type_defs) cons_types in
    (* Get Core variable identifiers *)
    let prod_ids = List.map (fun p -> match p with 
      | CT.Var v -> v
      | _ -> failwith "Expected variable") prods in
    let cons_ids = List.map (fun c -> match c with
      | CT.Covar a -> a
      | _ -> failwith "Expected covariable") cons in
    (* Pair Core IDs with instantiated types - preserving Core chiralities *)
    let args_env = (List.map2 (fun id ty -> (id, CutTypes.Prd ty)) prod_ids prod_types_cut) @
                   (List.map2 (fun id ty -> (id, CutTypes.Cns ty)) cons_ids cons_types_cut) in
    CutT.LetCns (alpha, dtor, type_args_cut, args_env, collapse_statement ctx s)
  
  (* FORM 2a: ⟨x | case {C(Γ) ⇒ s, ...}⟩ → switch x {C(Γ) ⇒ s, ...} 
     x is a PRODUCER *)
  | (CT.Var x, CT.Case patterns) ->
    let branches = List.map (fun (pat: CT.pattern) ->
      (* Get constructor info from Core type definitions *)
      let xtor_decl = CT.get_xtor ctx.defs pat.CT.xtor in
      (* Build type substitution *)
      let ty_subst = if List.length type_args_core = List.length xtor_decl.quantified then
        List.fold_left2 (fun acc (tv, _) ty ->
          Ident.add tv ty acc
        ) Ident.emptytbl xtor_decl.quantified type_args_core
      else
        Ident.emptytbl
      in
      (* Apply substitution and convert to Cut types *)
      let prod_types_cut = List.map (fun ty -> core_type_to_cut_type ctx.defs.type_defs (Type.subst ty_subst ty)) xtor_decl.producers in
      let cons_types_cut = List.map (fun ty -> core_type_to_cut_type ctx.defs.type_defs (Type.subst ty_subst ty)) xtor_decl.consumers in
      (* Build args_env *)
      let args_env = (List.map2 (fun v ty -> (v, CutTypes.Prd ty)) pat.CT.variables prod_types_cut) @
                     (List.map2 (fun a ty -> (a, CutTypes.Cns ty)) pat.CT.covariables cons_types_cut) in
      (* Collapse the statement *)
      let body = collapse_statement ctx pat.CT.statement in
      (pat.CT.xtor, type_args_cut, args_env, body)
    ) patterns in
    CutT.SwitchPrd (x, branches)
  
  (* FORM 2b: ⟨cocase {D(Γ) ⇒ s, ...} | α⟩ → switchcns α {D(Γ) ⇒ s, ...} 
     α (covariable) becomes variable and is a CONSUMER (dual of Form 2a) *)
  | (CT.Cocase patterns, CT.Covar alpha) ->
    let branches = List.map (fun (pat: CT.pattern) ->
      (* Get destructor info from Core type definitions *)
      let xtor_decl = CT.get_xtor ctx.defs pat.CT.xtor in
      (* Build type substitution *)
      let ty_subst = if List.length type_args_core = List.length xtor_decl.quantified then
        List.fold_left2 (fun acc (tv, _) ty ->
          Ident.add tv ty acc
        ) Ident.emptytbl xtor_decl.quantified type_args_core
      else
        Ident.emptytbl
      in
      (* Apply substitution and convert to Cut types *)
      let prod_types_cut = List.map (fun ty -> core_type_to_cut_type ctx.defs.type_defs (Type.subst ty_subst ty)) xtor_decl.producers in
      let cons_types_cut = List.map (fun ty -> core_type_to_cut_type ctx.defs.type_defs (Type.subst ty_subst ty)) xtor_decl.consumers in
      (* Build args_env *)
      let args_env = (List.map2 (fun v ty -> (v, CutTypes.Prd ty)) pat.CT.variables prod_types_cut) @
                     (List.map2 (fun a ty -> (a, CutTypes.Cns ty)) pat.CT.covariables cons_types_cut) in
      (* Collapse the statement *)
      let body = collapse_statement ctx pat.CT.statement in
      (pat.CT.xtor, type_args_cut, args_env, body)
    ) patterns in
    (* Alpha is a consumer (codata) - use SwitchCns *)
    CutT.SwitchCns (alpha, branches)
  
  (* FORM 3a: ⟨µα.s1 | case {C(Γ) ⇒ s2, ...}⟩ → new α = {C(Γ) ⇒ s2, ...}; s1 
     α is a CONSUMER (Mu in producer position binds consumer) *)
  | (CT.Mu (alpha, s1), CT.Case patterns) ->
    (* Compute free variables from all case branches *)
    let all_free_vars = List.concat_map (fun (pat: CT.pattern) ->
      let bound_vars = pat.CT.variables @ pat.CT.covariables in
      let free_in_pat = Core.Free_vars.free_vars_statement pat.CT.statement in
      List.filter (fun v -> not (List.mem v bound_vars) && not (Ident.equal v alpha)) free_in_pat
    ) patterns in
    let unique_free_vars = List.sort_uniq Ident.compare all_free_vars in
    
    (* Build gamma from free variables, looking up their types *)
    let gamma = List.filter_map (fun v ->
      get_chirality_opt ctx v |> Option.map (fun chi_ty -> (v, chi_ty))
    ) unique_free_vars in
    
    let branches = List.map (fun (pat: CT.pattern) ->
      (* Get constructor info from Core definitions *)
      let xtor_decl = CT.get_xtor ctx.defs pat.CT.xtor in
      (* Build type substitution *)
      let ty_subst = if List.length type_args_core = List.length xtor_decl.quantified then
        List.fold_left2 (fun acc (tv, _) ty ->
          Ident.add tv ty acc
        ) Ident.emptytbl xtor_decl.quantified type_args_core
      else
        Ident.emptytbl
      in
      (* Apply substitution and convert to Cut types *)
      let prod_types_cut = List.map (fun ty -> core_type_to_cut_type ctx.defs.type_defs (Type.subst ty_subst ty)) xtor_decl.producers in
      let cons_types_cut = List.map (fun ty -> core_type_to_cut_type ctx.defs.type_defs (Type.subst ty_subst ty)) xtor_decl.consumers in
      (* Build args_env *)
      let args_env = (List.map2 (fun v ty -> (v, CutTypes.Prd ty)) pat.CT.variables prod_types_cut) @
                     (List.map2 (fun a ty -> (a, CutTypes.Cns ty)) pat.CT.covariables cons_types_cut) in
      (* Collapse the statement with extended environment *)
      let ctx_ext = { ctx with typ_env = args_env @ ctx.typ_env } in
      let body = collapse_statement ctx_ext pat.CT.statement in
      (pat.CT.xtor, [], args_env, body)
    ) patterns in
    let result_ty = core_type_to_cut_type ctx.defs.type_defs ty in
    CutT.NewCns (alpha, result_ty, gamma, branches, collapse_statement ctx s1)
  
  (* FORM 3b: ⟨cocase {D(Γ) ⇒ s2, ...} | µ˜x.s1⟩ → newprd x = {D(Γ) ⇒ s2, ...}; s1 
     x is a PRODUCER (MuTilde in consumer position binds producer) *)
  | (CT.Cocase patterns, CT.MuTilde (x, s1)) ->
    (* Compute free variables from all cocase branches *)
    let all_free_vars = List.concat_map (fun (pat: CT.pattern) ->
      let bound_vars = pat.CT.variables @ pat.CT.covariables in
      let free_in_pat = Core.Free_vars.free_vars_statement pat.CT.statement in
      List.filter (fun v -> not (List.mem v bound_vars) && not (Ident.equal v x)) free_in_pat
    ) patterns in
    let unique_free_vars = List.sort_uniq Ident.compare all_free_vars in
    
    (* Build gamma from free variables, looking up their types *)
    let gamma = List.filter_map (fun v ->
      get_chirality_opt ctx v |> Option.map (fun chi_ty -> (v, chi_ty))
    ) unique_free_vars in
    
    let branches = List.map (fun (pat: CT.pattern) ->
      (* Get destructor info from Core type definitions *)
      let xtor_decl = CT.get_xtor ctx.defs pat.CT.xtor in
      (* Build type substitution *)
      let ty_subst = if List.length type_args_core = List.length xtor_decl.quantified then
        List.fold_left2 (fun acc (tv, _) ty ->
          Ident.add tv ty acc
        ) Ident.emptytbl xtor_decl.quantified type_args_core
      else
        Ident.emptytbl
      in
      (* Apply substitution and convert to Cut types *)
      let prod_types_cut = List.map (fun ty -> core_type_to_cut_type ctx.defs.type_defs (Type.subst ty_subst ty)) xtor_decl.producers in
      let cons_types_cut = List.map (fun ty -> core_type_to_cut_type ctx.defs.type_defs (Type.subst ty_subst ty)) xtor_decl.consumers in
      (* Build args_env *)
      let args_env = (List.map2 (fun v ty -> (v, CutTypes.Prd ty)) pat.CT.variables prod_types_cut) @
                     (List.map2 (fun a ty -> (a, CutTypes.Cns ty)) pat.CT.covariables cons_types_cut) in
      (* Collapse the statement with extended environment *)
      let ctx_ext = { ctx with typ_env = args_env @ ctx.typ_env } in
      let body = collapse_statement ctx_ext pat.CT.statement in
      (pat.CT.xtor, [], args_env, body)
    ) patterns in
    let result_ty = core_type_to_cut_type ctx.defs.type_defs ty in
    CutT.NewPrd (x, result_ty, gamma, branches, collapse_statement ctx s1)
  
  (* FORM 4a: ⟨x | D(Γ)⟩ → invoke x D(Γ) 
     x is a CONSUMER (receives codata value) *)
  | (CT.Var x, CT.Destructor (dtor, (_ty_args, prods, cons))) ->
    let args =
      (List.map (function CT.Var v -> v | _ -> failwith "Expected variable") prods) @
      (List.map (function CT.Covar a -> a | _ -> failwith "Expected covariable") cons) in
    CutT.InvokeCns (x, dtor, [], args)
  
  (* FORM 4b: ⟨C(Γ) | α⟩ → invoke α C(Γ) 
     α (covariable) is a CONSUMER (receives data value) *)
  | (CT.Constructor (ctor, (_ty_args, prods, cons)), CT.Covar alpha) ->
    let args = 
      (List.map (function CT.Var v -> v | _ -> failwith "Expected variable") prods) @
      (List.map (function CT.Covar a -> a | _ -> failwith "Expected covariable") cons) in
    CutT.InvokeCns (alpha, ctor, [], args)
  
  (* These should have been handled by shrinking *)
  | (CT.Mu (_alpha, _s), CT.Covar _k) ->
    failwith "⟨µα.s | k⟩ should have been eliminated by shrinking"
  
  | (CT.Var _x, CT.MuTilde (_y, _s)) ->
    failwith "⟨x | µ˜y.s⟩ should have been eliminated by shrinking"
  
  (* Fallback: ⟨x | k⟩ where types don't support eta-expansion *)
  | (CT.Var x, CT.Covar alpha) ->
    (* Polymorphic or external type - emit Return statement *)
    CutT.Return (x, alpha)
  | _ -> failwith "Unexpected cut form after shrinking"

(** Collapse a term definition into a Cut label definition *)
let collapse_term_def (ctx: collapse_context) (name: Path.t) (def: CT.term_def) : CutT.label * CutT.typ_env * CutT.statement =
  let label = CutT.MkLabel name in
  
  (* Build environment preserving Core chiralities *)
  let typ_env = 
    (List.map (fun (v, ty) -> 
      let cut_ty = core_type_to_cut_type ctx.defs.type_defs ty in
      (v, CutTypes.Prd cut_ty)  (* Producer arguments stay as producers *)
    ) def.prod_args) @
    (List.map (fun (v, ty) -> 
      let cut_ty = core_type_to_cut_type ctx.defs.type_defs ty in
      (v, CutTypes.Cns cut_ty)  (* Consumer arguments stay as consumers *)
    ) def.cons_args) in
  
  (* Create context with type environment for collapsing the body *)
  let ctx_with_env = { ctx with typ_env } in
  
  (* Collapse the body *)
  let body = collapse_statement ctx_with_env def.body in
  
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
let collapse_definitions (defs: CT.definitions) : CutT.definitions =
  let signatures = extract_signatures_from_defs defs in
  let ctx = { defs; signatures; typ_env = [] } in
  
  let program = List.map (fun (name, def) -> 
    collapse_term_def ctx name def
  ) defs.term_defs in
  
  { CutT.signatures; program }
