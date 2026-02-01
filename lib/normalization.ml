(**
  Module: Normalization
  Description: Transformation from Core to Cut (Pass A: Naming, Shrinking, Collapsing)
  
  This module implements the first pass of normalization, which:
  1. Names subterms (lifts non-variable arguments using μ/μ̃ bindings)
  2. Shrinks by removing redundant statement forms
  3. Collapses data/codata symmetry into unified Cut syntax
*)

open Common.Identifiers

module CTy = Common.Types
module CT = Core.Terms
module CutT = Cut.Terms

(** Helper: Check if a producer is a variable *)
let is_var_producer (p: CT.producer) : Ident.t option =
  match p with
  | CT.Var x -> Some x
  | _ -> None

(** Helper: Check if a consumer is a covariable *)
let is_covar_consumer (c: CT.consumer) : Ident.t option =
  match c with
  | CT.Covar alpha -> Some alpha
  | _ -> None

(** Helper: Get type symbol from a type *)
let get_type_symbol (defs: CT.definitions) (ty: CTy.typ) : Path.t option =
  match CTy.reduce defs.type_defs ty with
  | CTy.TySym s -> Some s
  | CTy.TyDef (CTy.Data td) -> Some td.symbol
  | CTy.TyDef (CTy.Code td) -> Some td.symbol
  | _ -> None

(** Helper: Get constructors/destructors for a type *)
let get_xtors (defs: CT.definitions) (ty: CTy.typ) : CTy.ty_xtor list option =
  match CTy.reduce defs.type_defs ty with
  | CTy.TyDef (CTy.Data td) -> Some td.xtors
  | CTy.TyDef (CTy.Code td) -> Some td.xtors
  | _ -> None

(** Helper: Determine if a type is data or codata *)
let is_data_type (defs: CT.definitions) (ty: CTy.typ) : bool option =
  match CTy.reduce defs.type_defs ty with
  | CTy.TyDef (CTy.Data _) -> Some true
  | CTy.TyDef (CTy.Code _) -> Some false
  | _ -> None

(** Convert Core kind to Cut kind *)
let rec core_kind_to_cut_kind (k: CTy.kind) : Cut.Types.kind =
  match k with
  | CTy.KStar -> Cut.Types.KStar
  | CTy.KArrow (k1, k2) -> Cut.Types.KArrow (core_kind_to_cut_kind k1, core_kind_to_cut_kind k2)

(** Convert Core type to Cut type 
    @param defs Core definitions for looking up type symbols
    @param ty Core type to convert
*)
let rec core_type_to_cut_type (defs: CT.definitions) (ty: CTy.typ) : Cut.Types.typ =
  match ty with
  | CTy.TySym s -> 
    (* Type symbol - look up in definitions to get the actual type *)
    (match List.assoc_opt s defs.type_defs with
    | Some (CTy.Data td, _) -> 
      Cut.Types.TySig { symbol = td.symbol; parameters = []; methods = [] }
    | Some (CTy.Code td, _) -> 
      Cut.Types.TySig { symbol = td.symbol; parameters = []; methods = [] }
    | Some (CTy.Prim (prim_sym, kind), _) ->
      Cut.Types.TyPrim (prim_sym, core_kind_to_cut_kind kind)
    | None -> 
      (* If not found, might be a type variable that wasn't substituted *)
      failwith ("Type symbol not found in definitions: " ^ Path.name s))
  | CTy.TyDef (CTy.Data td) -> 
    (* Data type becomes signature reference *)
    Cut.Types.TySig { symbol = td.symbol; parameters = []; methods = [] }
  | CTy.TyDef (CTy.Code td) -> 
    (* Codata type becomes signature reference *)
    Cut.Types.TySig { symbol = td.symbol; parameters = []; methods = [] }
  | CTy.TyApp (ty1, ty2) -> 
    (* Type application *)
    Cut.Types.TyApp (core_type_to_cut_type defs ty1, core_type_to_cut_type defs ty2)
  | CTy.TyVar v -> 
    (* Type variable *)
    Cut.Types.TyVar v
  | CTy.TyDef (CTy.Prim (s, kind)) -> 
    (* Primitive type *)
    Cut.Types.TyPrim (s, core_kind_to_cut_kind kind)

(** Convert Core type to Cut chirality type *)
let type_to_chirality (defs: CT.definitions) (ty: CTy.typ) : Cut.Types.chirality_type =
  let cut_ty = core_type_to_cut_type defs ty in
  match is_data_type defs ty with
  | Some true -> Cut.Types.Prd cut_ty
  | Some false -> Cut.Types.Cns cut_ty
  | None -> 
    (* For primitive/external types, default to Ext *)
    Cut.Types.Ext cut_ty

(** Apply substitution to an identifier in Core terms *)
let apply_subst_core (subst: (Ident.t * Ident.t) list) (v: Ident.t) : Ident.t =
  match List.assoc_opt v subst with
  | Some v' -> v'
  | None -> v

(** Apply substitution to a Core producer *)
let rec subst_core_producer (subst: (Ident.t * Ident.t) list) (p: CT.producer) : CT.producer =
  if subst = [] then p else
  match p with
  | CT.Var x -> CT.Var (apply_subst_core subst x)
  | CT.Mu (alpha, s) -> CT.Mu (apply_subst_core subst alpha, subst_core_statement subst s)
  | CT.Constructor (ctor, (ty_args, prods, cons)) ->
    CT.Constructor (ctor, (ty_args, 
                           List.map (subst_core_producer subst) prods,
                           List.map (subst_core_consumer subst) cons))
  | CT.Cocase patterns ->
    CT.Cocase (List.map (subst_core_pattern subst) patterns)
  | CT.Int n -> CT.Int n

(** Apply substitution to a Core consumer *)
and subst_core_consumer (subst: (Ident.t * Ident.t) list) (c: CT.consumer) : CT.consumer =
  if subst = [] then c else
  match c with
  | CT.Covar alpha -> CT.Covar (apply_subst_core subst alpha)
  | CT.MuTilde (x, s) -> CT.MuTilde (apply_subst_core subst x, subst_core_statement subst s)
  | CT.Destructor (dtor, (ty_args, prods, cons)) ->
    CT.Destructor (dtor, (ty_args,
                          List.map (subst_core_producer subst) prods,
                          List.map (subst_core_consumer subst) cons))
  | CT.Case patterns ->
    CT.Case (List.map (subst_core_pattern subst) patterns)

(** Apply substitution to a Core statement *)
and subst_core_statement (subst: (Ident.t * Ident.t) list) (s: CT.statement) : CT.statement =
  if subst = [] then s else
  match s with
  | CT.Cut (p, ty, c) ->
    CT.Cut (subst_core_producer subst p, ty, subst_core_consumer subst c)
  | CT.Call (f, ty_args, prods, cons) ->
    CT.Call (f, ty_args,
             List.map (subst_core_producer subst) prods,
             List.map (subst_core_consumer subst) cons)

(** Apply substitution to a Core pattern *)
and subst_core_pattern (subst: (Ident.t * Ident.t) list) (pat: CT.pattern) : CT.pattern =
  if subst = [] then pat else
  { pat with
    variables = List.map (apply_subst_core subst) pat.variables;
    covariables = List.map (apply_subst_core subst) pat.covariables;
    statement = subst_core_statement subst pat.statement;
  }

(** Normalize a producer, lifting non-variable subterms *)
let rec normalize_producer (defs: CT.definitions) (sigs: CutT.signatures) (p: CT.producer) 
    (k: Ident.t -> CutT.statement) : CutT.statement =
  match p with
  | CT.Var x -> k x
  
  | CT.Mu (alpha, s) ->
    (* μα.s is already a binding, continue with normalizing the statement *)
    let norm_s = normalize_statement defs sigs s in
    k_consume_mu norm_s k alpha
  
  | CT.Constructor (ctor, (_ty_args, prod_args, cons_args)) ->
    (* Look up constructor to get argument types *)
    let xtor_info = CT.get_xtor defs ctor in
    (* Producers have Prd chirality, Consumers have Cns chirality *)
    let prod_chi = List.map (fun ty -> Cut.Types.Prd (core_type_to_cut_type defs ty)) xtor_info.producers in
    let cons_chi = List.map (fun ty -> Cut.Types.Cns (core_type_to_cut_type defs ty)) xtor_info.consumers in
    let all_chi = prod_chi @ cons_chi in
    
    (* Lift all non-variable arguments *)
    lift_xtor_args defs sigs prod_args cons_args (fun vars ->
      (* Once all args are variables, create constructor and bind to continuation *)
      (* Create let statement: let v = ctor(Γ); s *)
      let v = Ident.fresh () in
      let var_env = List.map2 (fun x chi -> (x, chi)) vars all_chi in
      CutT.Let (v, ctor, [],
        var_env,
        k v)
    )
  
  | CT.Cocase patterns ->
    (* Cocase is a producer, need to bind it *)
    let v = Ident.fresh () in
    (* Infer type from the first pattern's parent xtor *)
    let cocase_ty = 
      match patterns with
      | [] -> failwith "Empty cocase patterns"
      | pat :: _ ->
        let xtor_info = CT.get_xtor defs pat.xtor in
        (* Build a type application from the parent and the pattern's type arguments *)
        let parent_sym = xtor_info.parent in
        (* If there are type arguments in the pattern, apply them *)
        List.fold_left (fun acc ty_arg -> 
          CTy.TyApp (acc, ty_arg)
        ) (CTy.TySym parent_sym) (List.map (fun ty_var -> 
          CTy.TyVar ty_var
        ) pat.type_vars)
    in
    let branches = normalize_cocase_patterns defs sigs cocase_ty patterns in
    (* The cocase will be bound in the continuation *)
    k_consume_cocase branches k v

  | CT.Int _n ->
    (* Integer literal - for now, treat as external value *)
    (* In a full implementation, this would use an extern statement *)
    let v = Ident.fresh () in
    let int_sym = CTy.Prim.int_sym in
    (* Create a let binding for the integer *)
    let lit_sym = Path.of_string "lit" in
    CutT.Extern (lit_sym, [], 
      [([(v, Cut.Types.Ext (Cut.Types.TyPrim (int_sym, Cut.Types.KStar)))], k v)])

(** Normalize a consumer, lifting non-variable subterms *)
and normalize_consumer (defs: CT.definitions) (sigs: CutT.signatures) (c: CT.consumer)
    (k: Ident.t -> CutT.statement) : CutT.statement =
  match c with
  | CT.Covar alpha -> k alpha
  
  | CT.MuTilde (x, s) ->
    (* μ̃x.s is already a binding, continue *)
    let norm_s = normalize_statement defs sigs s in
    k_consume_mutilde norm_s k x
  
  | CT.Destructor (dtor, (_ty_args, prod_args, cons_args)) ->
    (* Lift all non-variable arguments *)
    lift_xtor_args defs sigs prod_args cons_args (fun vars ->
      (* Create invoke: invoke v dtor(Γ) *)
      let v = Ident.fresh () in
      CutT.Invoke (v, dtor, [], vars)
    )
  
  | CT.Case patterns ->
    (* Case is a consumer, need to bind it *)
    let v = Ident.fresh () in
    let branches = normalize_case_patterns defs sigs patterns in
    k_consume_case branches k v

(** Main normalization for statements *)
and normalize_statement (defs: CT.definitions) (sigs: CutT.signatures) (s: CT.statement) : CutT.statement =
  match s with
  | CT.Cut (p, ty, c) ->
    (* The core case - normalize both sides then apply shrinking rules *)
    normalize_cut defs sigs p ty c
  
  | CT.Call (f, _ty_args, prod_args, cons_args) ->
    (* Function call - convert to jump with proper environment setup *)
    (* For now, treat as external call *)
    let call_label = CutT.MkLabel f in
    (* Lift all arguments to variables *)
    lift_xtor_args defs sigs prod_args cons_args (fun _vars ->
      CutT.Jump call_label
    )

(** Normalize a cut, applying shrinking rules *)
and normalize_cut (defs: CT.definitions) (sigs: CutT.signatures) (p: CT.producer) 
    (ty: CTy.typ) (c: CT.consumer) : CutT.statement =
  match (p, c) with
  (* Rule: ⟨x | μ̃y.s⟩ → s{y → x} (renaming) *)
  | (CT.Var x, CT.MuTilde (y, s)) ->
    normalize_statement defs sigs (subst_core_statement [(y, x)] s)
  
  (* Rule: ⟨μβ.s | α⟩ → s{β → α} (renaming) *)
  | (CT.Mu (beta, s), CT.Covar alpha) ->
    normalize_statement defs sigs (subst_core_statement [(beta, alpha)] s)
  
  (* Rule: ⟨C(Γ₀) | case {..., C(Γ) ⇒ s, ...}⟩ → s{Γ → Γ₀} (known cut) *)
  | (CT.Constructor (ctor, (_, prods, cons)), CT.Case patterns) ->
    (match find_matching_pattern ctor patterns with
    | Some (_, vars, covars, body) ->
      (* Substitute pattern variables with constructor arguments *)
      normalize_known_cut defs sigs prods cons vars covars body
    | None ->
      failwith ("Constructor " ^ Path.name ctor ^ " not found in case patterns"))
  
  (* Rule: ⟨cocase {..., D(Γ) ⇒ s, ...} | D(Γ₀)⟩ → s{Γ → Γ₀} (known cut) *)
  | (CT.Cocase patterns, CT.Destructor (dtor, (_, prods, cons))) ->
    (match find_matching_pattern dtor patterns with
    | Some (_, vars, covars, body) ->
      normalize_known_cut defs sigs prods cons vars covars body
    | None ->
      failwith ("Destructor " ^ Path.name dtor ^ " not found in cocase patterns"))
  
  (* Rule: ⟨cocase {...} | α⟩ → new v = cocase; substitute α := v *)
  | (CT.Cocase patterns, CT.Covar alpha) ->
    let v = Ident.fresh () in
    let branches = normalize_cocase_patterns defs sigs ty patterns in
    (* Create the cocase object and make it available to the continuation via substitution *)
    (* The jump to "cocase_done" is a placeholder - at top level, execution completes here *)
    CutT.New (v, core_type_to_cut_type defs ty, [], branches, 
      CutT.Substitute ([(alpha, v)], CutT.Jump (CutT.MkLabel (Path.of_string "cocase_done"))))
  
  (* Rule: ⟨x | α⟩ → η-expand (unknown cut) *)
  | (CT.Var x, CT.Covar alpha) ->
    normalize_unknown_cut defs sigs x alpha ty
  
  (* Rule: ⟨μα.s₁ | μ̃x.s₂⟩ → η-expand (critical pair) *)
  | (CT.Mu (alpha, s1), CT.MuTilde (x, s2)) ->
    normalize_critical_pair defs sigs alpha s1 x s2 ty
  
  (* Default cases: lift non-variable subterms *)
  | (p, c) ->
    (* First normalize producer to a variable *)
    normalize_producer defs sigs p (fun p_var ->
      (* Then normalize consumer to a covariable *)
      normalize_consumer defs sigs c (fun c_var ->
        (* Now we have ⟨p_var | c_var⟩, which is an unknown cut needing η-expansion *)
        normalize_unknown_cut defs sigs p_var c_var ty
      )
    )

(** η-expand unknown cut ⟨x | α⟩ *)
and normalize_unknown_cut (defs: CT.definitions) (sigs: CutT.signatures) (x: Ident.t) (alpha: Ident.t)
    (ty: CTy.typ) : CutT.statement =
  match get_xtors defs ty with
  | Some xtors ->
    (match is_data_type defs ty with
    | Some true ->
      (* Data type: expand consumer with case *)
      (* Look up signature to get variable names *)
      let ty_sym = match get_type_symbol defs ty with
        | Some sym -> sym
        | None -> failwith "Cannot get type symbol for η-expansion"
      in
      let (sig_def, _) = try List.assoc ty_sym sigs with Not_found -> 
        failwith ("Signature not found for type: " ^ Path.name ty_sym)
      in
      let branches = List.map (fun (xtor: CTy.ty_xtor) ->
        (* Try to find method signature for this constructor *)
        let var_env = 
          try
            let msig = List.find (fun (m: Cut.Types.method_sig) -> m.symbol = xtor.symbol) sig_def.methods in
            List.map (fun (v, chi) -> (v, chi)) (msig.producers @ msig.consumers)
          with Not_found ->
            (* Fallback: use fresh variables if signature not found *)
            let vars = List.map (fun _ -> Ident.fresh ()) xtor.producers in
            List.map (fun v -> (v, type_to_chirality defs ty)) vars
        in
        (* ⟨C(Γ) | α⟩ → invoke α C(Γ) *)
        let pattern_vars = List.map fst var_env in
        (xtor.symbol, [], var_env, CutT.Invoke (alpha, xtor.symbol, [], pattern_vars))
      ) xtors in
      CutT.Switch (x, branches)
    
    | Some false ->
      (* Codata type: expand producer with cocase *)
      (* Look up signature to get variable names *)
      let ty_sym = match get_type_symbol defs ty with
        | Some sym -> sym
        | None -> failwith "Cannot get type symbol for η-expansion"
      in
      let (sig_def, _) = try List.assoc ty_sym sigs with Not_found -> 
        failwith ("Signature not found for type: " ^ Path.name ty_sym)
      in
      let branches = List.map (fun (xtor: CTy.ty_xtor) ->
        (* Try to find method signature for this destructor *)
        let var_env = 
          try
            let msig = List.find (fun (m: Cut.Types.method_sig) -> m.symbol = xtor.symbol) sig_def.methods in
            List.map (fun (v, chi) -> (v, chi)) (msig.producers @ msig.consumers)
          with Not_found ->
            (* Fallback: use fresh variables if signature not found *)
            let vars = List.map (fun _ -> Ident.fresh ()) xtor.producers in
            List.map (fun v -> (v, type_to_chirality defs ty)) vars
        in
        (* ⟨x | D(Γ)⟩ → invoke x D(Γ) *)
        let pattern_vars = List.map fst var_env in
        (xtor.symbol, [], var_env, CutT.Invoke (x, xtor.symbol, [], pattern_vars))
      ) xtors in
      let v = Ident.fresh () in
      (* Create new consumer v, then substitute α with v *)
      CutT.New (v, core_type_to_cut_type defs ty, [], branches, 
        CutT.Substitute ([(alpha, v)], CutT.Jump (CutT.MkLabel (Path.of_string "η_expand"))))
    
    | None -> failwith "Cannot determine if type is data or codata for η-expansion")
  | None -> failwith "Cannot get constructors/destructors for η-expansion"

(** η-expand critical pair ⟨μα.s₁ | μ̃x.s₂⟩ *)
and normalize_critical_pair (defs: CT.definitions) (sigs: CutT.signatures)
    (alpha: Ident.t) (s1: CT.statement)
    (x: Ident.t) (s2: CT.statement)
    (ty: CTy.typ) : CutT.statement =
  match get_xtors defs ty with
  | Some xtors ->
    let norm_s1 = normalize_statement defs sigs s1 in
    let norm_s2 = normalize_statement defs sigs s2 in
    (match is_data_type defs ty with
    | Some true ->
      (* Data type: expand μ̃x.s₂ with case *)
      (* Look up signature to get variable names *)
      let ty_sym = match get_type_symbol defs ty with
        | Some sym -> sym
        | None -> failwith "Cannot get type symbol for critical pair"
      in
      let (sig_def, _) = try List.assoc ty_sym sigs with Not_found -> 
        failwith ("Signature not found for type: " ^ Path.name ty_sym)
      in
      let branches = List.map (fun (xtor: CTy.ty_xtor) ->
        let var_env = 
          try
            let msig = List.find (fun (m: Cut.Types.method_sig) -> m.symbol = xtor.symbol) sig_def.methods in
            List.map (fun (v, chi) -> (v, chi)) (msig.producers @ msig.consumers)
          with Not_found ->
            let vars = List.map (fun _ -> Ident.fresh ()) xtor.producers in
            List.map (fun v -> (v, type_to_chirality defs ty)) vars
        in
        (xtor.symbol, [], var_env, norm_s2)
      ) xtors in
      CutT.New (alpha, core_type_to_cut_type defs ty, [], branches, norm_s2)
    
    | Some false ->
      (* Codata type: expand μα.s₁ with cocase *)
      (* Look up signature to get variable names *)
      let ty_sym = match get_type_symbol defs ty with
        | Some sym -> sym
        | None -> failwith "Cannot get type symbol for critical pair"
      in
      let (sig_def, _) = try List.assoc ty_sym sigs with Not_found -> 
        failwith ("Signature not found for type: " ^ Path.name ty_sym)
      in
      let branches = List.map (fun (xtor: CTy.ty_xtor) ->
        let var_env = 
          try
            let msig = List.find (fun (m: Cut.Types.method_sig) -> m.symbol = xtor.symbol) sig_def.methods in
            List.map (fun (v, chi) -> (v, chi)) (msig.producers @ msig.consumers)
          with Not_found ->
            let vars = List.map (fun _ -> Ident.fresh ()) xtor.producers in
            List.map (fun v -> (v, type_to_chirality defs ty)) vars
        in
        (xtor.symbol, [], var_env, norm_s1)
      ) xtors in
      CutT.New (x, core_type_to_cut_type defs ty, [], branches, norm_s1)
    
    | None -> failwith "Cannot determine if type is data or codata for critical pair")
  | None -> failwith "Cannot get constructors/destructors for critical pair"

(** Lift non-variable arguments *)
and lift_xtor_args (defs: CT.definitions) (sigs: CutT.signatures)
    (prods: CT.producer list) (cons: CT.consumer list)
    (k: Ident.t list -> CutT.statement) : CutT.statement =
  (* Lift producers, then consumers, accumulating bound variables *)
  let rec lift_prods ps acc_vars =
    match ps with
    | [] -> lift_cons cons acc_vars
    | p :: rest ->
      match is_var_producer p with
      | Some x -> 
        (* Already a variable, just accumulate it *)
        lift_prods rest (x :: acc_vars)
      | None ->
        (* Not a variable - normalize it, which binds it to a fresh variable *)
        normalize_producer defs sigs p (fun x ->
          lift_prods rest (x :: acc_vars)
        )
  and lift_cons cs acc_vars =
    match cs with
    | [] -> 
      (* All arguments lifted, call continuation with variables in correct order *)
      k (List.rev acc_vars)
    | c :: rest ->
      match is_covar_consumer c with
      | Some alpha -> 
        (* Already a covariable, just accumulate it *)
        lift_cons rest (alpha :: acc_vars)
      | None ->
        (* Not a covariable - normalize it, which binds it to a fresh covariable *)
        normalize_consumer defs sigs c (fun alpha ->
          lift_cons rest (alpha :: acc_vars)
        )
  in
  lift_prods prods []

(** Normalize case patterns *)
and normalize_case_patterns (defs: CT.definitions) (sigs: CutT.signatures) (patterns: CT.pattern list) 
    : CutT.branches =
  List.map (fun (pat: CT.pattern) ->
    let norm_s = normalize_statement defs sigs pat.statement in
    (* Look up constructor to get argument types *)
    let xtor_info = CT.get_xtor defs pat.xtor in
    (* Constructors take producers, so use Prd chirality *)
    let var_env = List.map2 (fun v ty -> 
      (v, Cut.Types.Prd (core_type_to_cut_type defs ty))
    ) pat.variables xtor_info.producers in
    (pat.xtor, [], var_env, norm_s)
  ) patterns

(** Normalize cocase patterns *)
and normalize_cocase_patterns (defs: CT.definitions) (sigs: CutT.signatures) 
    (ty: CTy.typ) (patterns: CT.pattern list)
    : CutT.branches =
  (* Extract type arguments from the type to instantiate polymorphic types *)
  let rec extract_type_args acc t =
    match t with
    | CTy.TyApp (t1, t2) -> extract_type_args (t2 :: acc) t1
    | _ -> acc
  in
  let type_args = extract_type_args [] ty in
  
  List.map (fun (pat: CT.pattern) ->
    let norm_s = normalize_statement defs sigs pat.statement in
    (* Look up destructor to get argument types *)
    let xtor_info = CT.get_xtor defs pat.xtor in
    
    (* Find the parent type to look up the signature for canonical variable names *)
    let parent_sym = xtor_info.parent in
    
    (* Try to find the signature to get canonical variable names and apply type instantiation *)
    let (sig_vars, instantiated_prod_types, instantiated_cons_types) = 
      try
        let (sig_def, _) = List.assoc parent_sym sigs in
        let msig = List.find (fun (m: Cut.Types.method_sig) -> 
          Path.equal m.symbol pat.xtor
        ) sig_def.methods in
        
        (* Build type substitution from signature's type params to actual type args *)
        let type_params = List.map fst sig_def.parameters in
        let cut_type_args = List.map (core_type_to_cut_type defs) type_args in
        let type_subst = 
          if List.length type_params <> List.length cut_type_args then (
            Printf.eprintf "ERROR: Type parameter count mismatch for %s:\n" (Path.name parent_sym);
            Printf.eprintf "  Expected %d type params, got %d type args\n" 
              (List.length type_params) (List.length cut_type_args);
            failwith "Type parameter count mismatch"
          ) else
            List.combine type_params cut_type_args in
        
        (* Apply substitution to the chirality types from the signature *)
        let inst_prods = List.map (fun (v, chi_ty) ->
          (v, Cut.Types.substitute_chirality type_subst chi_ty)
        ) msig.producers in
        let inst_cons = List.map (fun (v, chi_ty) ->
          (v, Cut.Types.substitute_chirality type_subst chi_ty)
        ) msig.consumers in
        
        (* Extract variable names and types *)
        let vars = List.map fst (inst_prods @ inst_cons) in
        let prod_tys = List.map (fun (_, chi_ty) -> 
          match chi_ty with Cut.Types.Prd t -> t | _ -> failwith "Expected Prd"
        ) inst_prods in
        let cons_tys = List.map (fun (_, chi_ty) ->
          match chi_ty with Cut.Types.Cns t -> t | _ -> failwith "Expected Cns"
        ) inst_cons in
        
        (vars, prod_tys, cons_tys)
      with Not_found ->
        (* Fallback: use pattern's own variables and uninstantiated types *)
        let sig_vars = pat.variables @ pat.covariables in
        let prod_tys = List.map (core_type_to_cut_type defs) xtor_info.producers in
        let cons_tys = List.map (core_type_to_cut_type defs) xtor_info.consumers in
        (sig_vars, prod_tys, cons_tys)
    in
    
    (* Create environment with instantiated types *)
    let n_prods = List.length instantiated_prod_types in
    let prod_vars = List.take n_prods sig_vars in
    let cons_vars = List.drop n_prods sig_vars in
    
    let prod_env = List.map2 (fun v ty -> (v, Cut.Types.Prd ty)) prod_vars instantiated_prod_types in
    let cons_env = List.map2 (fun v ty -> (v, Cut.Types.Cns ty)) cons_vars instantiated_cons_types in
    let var_env = prod_env @ cons_env in
    
    (* Build substitution from pattern variables to signature variables *)
    let pat_vars = pat.variables @ pat.covariables in
    let var_subst = 
      if List.length pat_vars <> List.length sig_vars then (
        Printf.eprintf "ERROR: Variable count mismatch for pattern %s:\n" (Path.name pat.xtor);
        Printf.eprintf "  Pattern has %d vars, signature has %d vars\n"
          (List.length pat_vars) (List.length sig_vars);
        Printf.eprintf "  Pattern vars: %s\n"
          (String.concat ", " (List.map Ident.name pat_vars));
        Printf.eprintf "  Signature vars: %s\n"
          (String.concat ", " (List.map Ident.name sig_vars));
        failwith "Variable count mismatch"
      ) else
        List.combine pat_vars sig_vars in
    
    (* Apply substitution to the normalized statement *)
    let subst_s = apply_cut_substitution var_subst norm_s in
    
    (* Convert type_args to Cut types for the branch *)
    let branch_type_args = List.map (core_type_to_cut_type defs) type_args in
    
    (pat.xtor, branch_type_args, var_env, subst_s)
  ) patterns

(** Apply variable substitution to a Cut statement *)
and apply_cut_substitution (subst: (Ident.t * Ident.t) list) (s: CutT.statement) : CutT.statement =
  if subst = [] then s else
  let apply_var v = 
    match List.assoc_opt v subst with Some v' -> v' | None -> v
  in
  let rec go_stmt = function
    | CutT.Jump label -> CutT.Jump label
    | CutT.Substitute (pairs, s') ->
      let pairs' = List.map (fun (v1, v2) -> (apply_var v1, apply_var v2)) pairs in
      CutT.Substitute (pairs', go_stmt s')
    | CutT.Extern (f, vars, branches) ->
      CutT.Extern (f, List.map apply_var vars, List.map go_extern_branch branches)
    | CutT.Let (v, m, ty_args, gamma, s') ->
      let gamma' = List.map (fun (x, chi) -> (apply_var x, chi)) gamma in
      CutT.Let (apply_var v, m, ty_args, gamma', go_stmt s')
    | CutT.New (v, ty, gamma, branches, s') ->
      let gamma' = List.map (fun (x, chi) -> (apply_var x, chi)) gamma in
      CutT.New (apply_var v, ty, gamma', List.map go_branch branches, go_stmt s')
    | CutT.Switch (v, branches) ->
      CutT.Switch (apply_var v, List.map go_branch branches)
    | CutT.Invoke (v, m, ty_args, vars) ->
      CutT.Invoke (apply_var v, m, ty_args, List.map apply_var vars)
  and go_branch (m, ty_args, gamma, s) =
    (* Variables bound in gamma shadow the substitution *)
    let bound_vars = List.map fst gamma in
    let subst' = List.filter (fun (v, _) -> not (List.mem v bound_vars)) subst in
    let gamma' = List.map (fun (x, chi) -> (apply_var x, chi)) gamma in
    let s' = apply_cut_substitution subst' s in
    (m, ty_args, gamma', s')
  and go_extern_branch (gamma, s) =
    let bound_vars = List.map fst gamma in
    let subst' = List.filter (fun (v, _) -> not (List.mem v bound_vars)) subst in
    let gamma' = List.map (fun (x, chi) -> (apply_var x, chi)) gamma in
    let s' = apply_cut_substitution subst' s in
    (gamma', s')
  in
  go_stmt s

(** Helper: find matching pattern *)
and find_matching_pattern (xtor: Path.t) (patterns: CT.pattern list) 
    : (Path.t * Ident.t list * Ident.t list * CT.statement) option =
  List.find_map (fun (pat: CT.pattern) ->
    if Path.equal pat.xtor xtor then
      Some (pat.xtor, pat.variables, pat.covariables, pat.statement)
    else None
  ) patterns

(** Helper: normalize known cut by substitution *)
and normalize_known_cut (defs: CT.definitions) (sigs: CutT.signatures)
    (prods: CT.producer list) (cons: CT.consumer list)
    (vars: Ident.t list) (covars: Ident.t list)
    (body: CT.statement) : CutT.statement =
  (* Lift all arguments to variables, then substitute pattern vars with actual vars *)
  lift_xtor_args defs sigs prods cons (fun actual_vars ->
    (* Build substitution mapping: pattern variables -> actual variables *)
    (* actual_vars contains producers followed by consumers *)
    let n_prods = List.length prods in
    let actual_prod_vars = List.take n_prods actual_vars in
    let actual_cons_vars = List.drop n_prods actual_vars in
    
    (* Create substitution pairs (old_var, new_var) for Core AST substitution *)
    let subst = 
      List.combine vars actual_prod_vars @ 
      List.combine covars actual_cons_vars 
    in
    
    (* Apply substitution to Core statement, then normalize *)
    let subst_body = subst_core_statement subst body in
    normalize_statement defs sigs subst_body
  )

(** Helper: consume a Mu binding *)
and k_consume_mu (_s: CutT.statement) (k: Ident.t -> CutT.statement) 
    (alpha: Ident.t) : CutT.statement =
  (* We have normalized μα.s, now need to pass α to continuation *)
  k alpha

(** Helper: consume a MuTilde binding *)
and k_consume_mutilde (_s: CutT.statement) (k: Ident.t -> CutT.statement)
    (x: Ident.t) : CutT.statement =
  k x

(** Helper: consume a case *)
and k_consume_case (_branches: CutT.branches) (k: Ident.t -> CutT.statement)
    (v: Ident.t) : CutT.statement =
  k v

(** Helper: consume a cocase *)
and k_consume_cocase (_branches: CutT.branches) (_k: Ident.t -> CutT.statement)
    (_v: Ident.t) : CutT.statement =
  (* This should not be called - cocase should be handled directly in normalize_cut *)
  failwith "k_consume_cocase: cocase should be handled in normalize_cut"

(** Convert Core type definitions to Cut signatures
    
    Extracts data and codata type definitions from Core and converts them
    to Cut signatures. Each constructor/destructor becomes a method in the signature.
    Primitive types (int, etc.) are skipped as they should be external types.
    
    @param defs Core definitions
    @return Cut signatures mapping type symbols to signature definitions
*)
let extract_signatures (defs: CT.definitions) : CutT.signatures =
  List.filter_map (fun (ty_sym, (ty_def, kind)) ->
    match ty_def with
    | CTy.Data ty_dec | CTy.Code ty_dec ->
      (* Extract type parameters - create meaningful identifiers for them *)
      let type_params = List.mapi (fun i (_, k) ->
        (* Use meaningful names: a, b, c, ... *)
        let param_name = String.make 1 (Char.chr (Char.code 'a' + i)) in
        (Ident.mk param_name, core_kind_to_cut_kind k)
      ) ty_dec.arguments in
      
      (* Collect all type variables used in xtors to build substitution *)
      let collect_type_vars ty =
        let rec go acc t =
          match t with
          | CTy.TyVar v -> if List.mem v acc then acc else v :: acc
          | CTy.TyApp (t1, t2) -> go (go acc t1) t2
          | _ -> acc
        in go [] ty
      in
      
      let all_type_vars = List.fold_left (fun acc (xtor: CTy.ty_xtor) ->
        let prod_vars = List.fold_left (fun a ty -> List.rev_append (collect_type_vars ty) a) acc xtor.producers in
        List.fold_left (fun a ty -> List.rev_append (collect_type_vars ty) a) prod_vars xtor.consumers
      ) [] ty_dec.xtors in
      
      (* Remove duplicates and take only as many as we have parameters *)
      let unique_vars = List.sort_uniq Ident.compare all_type_vars in
      let old_type_params = List.take (List.length type_params) unique_vars in
      
      (* Build substitution from old type variables to new parameter identifiers *)
      let type_param_subst = 
        if List.length old_type_params = List.length type_params then
          List.map2 (fun old_v (new_v, _) -> (old_v, Cut.Types.TyVar new_v)) old_type_params type_params
        else [] in
      
      (* Convert each xtor to a method signature *)
      let methods = List.filter_map (fun (xtor: CTy.ty_xtor) ->
        try
          (* Build producer and consumer environments from xtor parameters *)
          (* Chirality is determined by position: producers → Prd, consumers → Cns *)
          let prod_params = List.map (fun ty -> 
            let cut_ty = core_type_to_cut_type defs ty in
            let subst_ty = Cut.Types.Type.substitute type_param_subst cut_ty in
            (Ident.fresh (), Cut.Types.Prd subst_ty)
          ) xtor.producers in
          let cons_params = List.map (fun ty ->
            let cut_ty = core_type_to_cut_type defs ty in
            let subst_ty = Cut.Types.Type.substitute type_param_subst cut_ty in
            (Ident.fresh (), Cut.Types.Cns subst_ty)
          ) xtor.consumers in
          
          (* Convert quantified type variables to Cut types *)
          let quantified_cut = List.map (fun (v, k) ->
            (v, core_kind_to_cut_kind k)
          ) xtor.quantified in
          
          (* Create method signature *)
          let method_sig : Cut.Types.method_sig = {
            parent = ty_sym;
            symbol = xtor.symbol;
            quantified = quantified_cut;
              producers = prod_params;
              consumers = cons_params;
              result_type = Cut.Types.TySig { 
                symbol = ty_sym; 
                parameters = []; 
                methods = [] (* Will be filled by parent *)
              };
              constraints = []; (* No GADT constraints for now *)
            } in
            Some method_sig
        with
        | Failure _ -> None (* Skip if conversion fails *)
      ) ty_dec.xtors in
      
      (* Create signature with methods *)
      let sig_def : Cut.Types.signature = {
        symbol = ty_sym;
        parameters = type_params;
        methods = methods;
      } in
      let cut_kind = core_kind_to_cut_kind kind in
      Some (ty_sym, (sig_def, cut_kind))
      
    | CTy.Prim (_prim_sym, _prim_kind) ->
      (* Primitive types should not become signatures - they are external types *)
      None
  ) defs.type_defs

let normalize_program (defs: CT.definitions) (sigs: CutT.signatures) : CutT.program =
  List.map (fun (path, (tdef: CT.term_def)) ->
    let label = CutT.MkLabel path in
    (* Build environment from function parameters *)
    (* prod_args are producers - use type_to_chirality to determine Prd/Cns *)
    let prod_env = List.map (fun (v, ty) -> (v, type_to_chirality defs ty)) tdef.prod_args in
    (* cons_args are consumers - always Cns regardless of base type *)
    let cons_env = List.map (fun (v, ty) -> (v, Cut.Types.Cns (core_type_to_cut_type defs ty))) tdef.cons_args in
    let gamma = prod_env @ cons_env in
    let body = normalize_statement defs sigs tdef.body in
    (label, gamma, body)
  ) defs.term_defs

(** Complete normalization pipeline: Core definitions to Cut definitions
    
    This function combines Pass A (naming, shrinking, collapsing) and Pass B (linearization)
    to produce a fully normalized Cut program with explicit substitutions and type signatures.
    
    @param defs Core definitions
    @return Cut definitions with signatures and linearized program
*)
let normalize_definitions (defs: CT.definitions) : CutT.definitions =
  (* Extract type signatures from Core type definitions *)
  let signatures = extract_signatures defs in
  (* Pass A: Naming, shrinking, collapsing - now with signatures *)
  let cut_prog = normalize_program defs signatures in
  (* Pass B: Linearization with explicit substitutions *)
  let linearized_prog = Linearization.linearize_program cut_prog in
  { CutT.signatures; CutT.program = linearized_prog }
