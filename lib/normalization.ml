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

(** Convert Core type to Cut type symbol *)
let rec type_to_symbol (ty: CTy.typ) : Path.t =
  match ty with
  | CTy.TySym s -> s
  | CTy.TyDef (CTy.Data td) -> td.symbol
  | CTy.TyDef (CTy.Code td) -> td.symbol
  | CTy.TyApp (ty1, _) -> type_to_symbol ty1
  | CTy.TyVar _ -> 
    (* For type variables, we'll need to generate a placeholder or error *)
    failwith "Cannot convert type variable to symbol in normalization"
  | CTy.TyDef (CTy.Prim (s, _)) -> s

(** Convert Core type to Cut chirality *)
let type_to_chirality (defs: CT.definitions) (ty: CTy.typ) : CutT.typ =
  match is_data_type defs ty with
  | Some true -> CutT.Prd (type_to_symbol ty)
  | Some false -> CutT.Cns (type_to_symbol ty)
  | None -> 
    (* For primitive/external types, default to Ext *)
    CutT.Ext (type_to_symbol ty)

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
let rec normalize_producer (defs: CT.definitions) (p: CT.producer) 
    (k: Ident.t -> CutT.statement) : CutT.statement =
  match p with
  | CT.Var x -> k x
  
  | CT.Mu (alpha, s) ->
    (* μα.s is already a binding, continue with normalizing the statement *)
    let norm_s = normalize_statement defs s in
    k_consume_mu norm_s k alpha
  
  | CT.Constructor (ctor, (_ty_args, prod_args, cons_args)) ->
    (* Lift all non-variable arguments *)
    lift_xtor_args defs prod_args cons_args (fun vars ->
      (* Once all args are variables, create constructor and bind to continuation *)
      (* Create let statement: let v = ctor(Γ); s *)
      let v = Ident.fresh () in
      CutT.Let (v, ctor, 
        List.map (fun x -> (x, CutT.Prd (type_to_symbol (CTy.TySym ctor)))) vars,
        k v)
    )
  
  | CT.Cocase patterns ->
    (* Cocase is a producer, need to bind it *)
    let v = Ident.fresh () in
    let branches = normalize_cocase_patterns defs patterns in
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
      [([(v, CutT.Ext int_sym)], k v)])

(** Normalize a consumer, lifting non-variable subterms *)
and normalize_consumer (defs: CT.definitions) (c: CT.consumer)
    (k: Ident.t -> CutT.statement) : CutT.statement =
  match c with
  | CT.Covar alpha -> k alpha
  
  | CT.MuTilde (x, s) ->
    (* μ̃x.s is already a binding, continue *)
    let norm_s = normalize_statement defs s in
    k_consume_mutilde norm_s k x
  
  | CT.Destructor (dtor, (_ty_args, prod_args, cons_args)) ->
    (* Lift all non-variable arguments *)
    lift_xtor_args defs prod_args cons_args (fun _vars ->
      (* Create invoke: invoke v dtor(Γ) *)
      let v = Ident.fresh () in
      CutT.Invoke (v, dtor)
    )
  
  | CT.Case patterns ->
    (* Case is a consumer, need to bind it *)
    let v = Ident.fresh () in
    let branches = normalize_case_patterns defs patterns in
    k_consume_case branches k v

(** Main normalization for statements *)
and normalize_statement (defs: CT.definitions) (s: CT.statement) : CutT.statement =
  match s with
  | CT.Cut (p, ty, c) ->
    (* The core case - normalize both sides then apply shrinking rules *)
    normalize_cut defs p ty c
  
  | CT.Call (f, _ty_args, prod_args, cons_args) ->
    (* Function call - convert to jump with proper environment setup *)
    (* For now, treat as external call *)
    let call_label = CutT.MkLabel f in
    (* Lift all arguments to variables *)
    lift_xtor_args defs prod_args cons_args (fun vars ->
      let _gamma = List.map (fun x ->
        (x, CutT.Prd (type_to_symbol (CTy.TySym f)))
      ) vars in
      CutT.Jump call_label
    )

(** Normalize a cut, applying shrinking rules *)
and normalize_cut (defs: CT.definitions) (p: CT.producer) 
    (ty: CTy.typ) (c: CT.consumer) : CutT.statement =
  match (p, c) with
  (* Rule: ⟨x | μ̃y.s⟩ → s{y → x} (renaming) *)
  | (CT.Var x, CT.MuTilde (y, s)) ->
    normalize_statement defs (subst_core_statement [(y, x)] s)
  
  (* Rule: ⟨μβ.s | α⟩ → s{β → α} (renaming) *)
  | (CT.Mu (beta, s), CT.Covar alpha) ->
    normalize_statement defs (subst_core_statement [(beta, alpha)] s)
  
  (* Rule: ⟨C(Γ₀) | case {..., C(Γ) ⇒ s, ...}⟩ → s{Γ → Γ₀} (known cut) *)
  | (CT.Constructor (ctor, (_, prods, cons)), CT.Case patterns) ->
    (match find_matching_pattern ctor patterns with
    | Some (_, vars, covars, body) ->
      (* Substitute pattern variables with constructor arguments *)
      normalize_known_cut defs prods cons vars covars body
    | None ->
      failwith ("Constructor " ^ Path.name ctor ^ " not found in case patterns"))
  
  (* Rule: ⟨cocase {..., D(Γ) ⇒ s, ...} | D(Γ₀)⟩ → s{Γ → Γ₀} (known cut) *)
  | (CT.Cocase patterns, CT.Destructor (dtor, (_, prods, cons))) ->
    (match find_matching_pattern dtor patterns with
    | Some (_, vars, covars, body) ->
      normalize_known_cut defs prods cons vars covars body
    | None ->
      failwith ("Destructor " ^ Path.name dtor ^ " not found in cocase patterns"))
  
  (* Rule: ⟨x | α⟩ → η-expand (unknown cut) *)
  | (CT.Var x, CT.Covar alpha) ->
    normalize_unknown_cut defs x alpha ty
  
  (* Rule: ⟨μα.s₁ | μ̃x.s₂⟩ → η-expand (critical pair) *)
  | (CT.Mu (alpha, s1), CT.MuTilde (x, s2)) ->
    normalize_critical_pair defs alpha s1 x s2 ty
  
  (* Default cases: lift non-variable subterms *)
  | (p, c) ->
    normalize_producer defs p (fun _p_var ->
      normalize_consumer defs c (fun _c_var ->
        (* Now both are variables, create appropriate statement *)
        match (is_data_type defs ty, p, c) with
        (* ⟨C(Γ) | μ̃x.s⟩ & ⟨μα.s | D(Γ)⟩ → let *)
        | (_, CT.Constructor (ctor, _), CT.MuTilde (x, s)) ->
          let norm_s = normalize_statement defs s in
          CutT.Let (x, ctor, [], norm_s)
        | (_, CT.Mu (alpha, s), CT.Destructor (dtor, _)) ->
          let norm_s = normalize_statement defs s in
          CutT.Let (alpha, dtor, [], norm_s)
        
        (* ⟨C(Γ) | α⟩ & ⟨x | D(Γ)⟩ → invoke *)
        | _ ->
          (* Generic case: create jump or invoke based on structure *)
          failwith "Unhandled cut case in normalization"
      )
    )

(** η-expand unknown cut ⟨x | α⟩ *)
and normalize_unknown_cut (defs: CT.definitions) (x: Ident.t) (alpha: Ident.t)
    (ty: CTy.typ) : CutT.statement =
  match get_xtors defs ty with
  | Some xtors ->
    (match is_data_type defs ty with
    | Some true ->
      (* Data type: expand consumer with case *)
      let branches = List.map (fun (xtor: CTy.ty_xtor) ->
        let vars = List.map (fun _ -> Ident.fresh ()) xtor.producers in
        let var_env = List.map (fun v -> (v, type_to_chirality defs ty)) vars in
        (* ⟨C(Γ) | α⟩ *)
        (xtor.symbol, var_env, CutT.Invoke (alpha, xtor.symbol))
      ) xtors in
      CutT.Switch (x, branches)
    
    | Some false ->
      (* Codata type: expand producer with cocase *)
      let branches = List.map (fun (xtor: CTy.ty_xtor) ->
        let vars = List.map (fun _ -> Ident.fresh ()) xtor.producers in
        let var_env = List.map (fun v -> (v, type_to_chirality defs ty)) vars in
        (* ⟨x | D(Γ)⟩ *)
        (xtor.symbol, var_env, CutT.Invoke (x, xtor.symbol))
      ) xtors in
      let v = Ident.fresh () in
      CutT.New (v, type_to_symbol ty, [], branches, CutT.Invoke (alpha, type_to_symbol ty))
    
    | None -> failwith "Cannot determine if type is data or codata for η-expansion")
  | None -> failwith "Cannot get constructors/destructors for η-expansion"

(** η-expand critical pair ⟨μα.s₁ | μ̃x.s₂⟩ *)
and normalize_critical_pair (defs: CT.definitions) 
    (alpha: Ident.t) (s1: CT.statement)
    (x: Ident.t) (s2: CT.statement)
    (ty: CTy.typ) : CutT.statement =
  match get_xtors defs ty with
  | Some xtors ->
    let norm_s1 = normalize_statement defs s1 in
    let norm_s2 = normalize_statement defs s2 in
    (match is_data_type defs ty with
    | Some true ->
      (* Data type: expand μ̃x.s₂ with case *)
      let branches = List.map (fun (xtor: CTy.ty_xtor) ->
        let vars = List.map (fun _ -> Ident.fresh ()) xtor.producers in
        let var_env = List.map (fun v -> (v, type_to_chirality defs ty)) vars in
        (xtor.symbol, var_env, norm_s2)
      ) xtors in
      CutT.New (alpha, type_to_symbol ty, [], branches, norm_s2)
    
    | Some false ->
      (* Codata type: expand μα.s₁ with cocase *)
      let branches = List.map (fun (xtor: CTy.ty_xtor) ->
        let vars = List.map (fun _ -> Ident.fresh ()) xtor.producers in
        let var_env = List.map (fun v -> (v, type_to_chirality defs ty)) vars in
        (xtor.symbol, var_env, norm_s1)
      ) xtors in
      CutT.New (x, type_to_symbol ty, [], branches, norm_s1)
    
    | None -> failwith "Cannot determine if type is data or codata for critical pair")
  | None -> failwith "Cannot get constructors/destructors for critical pair"

(** Lift non-variable arguments *)
and lift_xtor_args (defs: CT.definitions) 
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
        normalize_producer defs p (fun x ->
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
        normalize_consumer defs c (fun alpha ->
          lift_cons rest (alpha :: acc_vars)
        )
  in
  lift_prods prods []

(** Normalize case patterns *)
and normalize_case_patterns (defs: CT.definitions) (patterns: CT.pattern list) 
    : CutT.branches =
  List.map (fun (pat: CT.pattern) ->
    let norm_s = normalize_statement defs pat.statement in
    let var_env = List.map (fun v -> (v, CutT.Prd (type_to_symbol (CTy.TySym pat.xtor)))) 
      pat.variables in
    (pat.xtor, var_env, norm_s)
  ) patterns

(** Normalize cocase patterns *)
and normalize_cocase_patterns (defs: CT.definitions) (patterns: CT.pattern list)
    : CutT.branches =
  List.map (fun (pat: CT.pattern) ->
    let norm_s = normalize_statement defs pat.statement in
    let var_env = List.map (fun v -> (v, CutT.Cns (type_to_symbol (CTy.TySym pat.xtor)))) 
      pat.variables in
    (pat.xtor, var_env, norm_s)
  ) patterns

(** Helper: find matching pattern *)
and find_matching_pattern (xtor: Path.t) (patterns: CT.pattern list) 
    : (Path.t * Ident.t list * Ident.t list * CT.statement) option =
  List.find_map (fun (pat: CT.pattern) ->
    if Path.equal pat.xtor xtor then
      Some (pat.xtor, pat.variables, pat.covariables, pat.statement)
    else None
  ) patterns

(** Helper: normalize known cut by substitution *)
and normalize_known_cut (defs: CT.definitions)
    (prods: CT.producer list) (cons: CT.consumer list)
    (vars: Ident.t list) (covars: Ident.t list)
    (body: CT.statement) : CutT.statement =
  (* Lift all arguments to variables, then substitute pattern vars with actual vars *)
  lift_xtor_args defs prods cons (fun actual_vars ->
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
    normalize_statement defs subst_body
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
and k_consume_cocase (_branches: CutT.branches) (k: Ident.t -> CutT.statement)
    (v: Ident.t) : CutT.statement =
  k v

(** Main entry point: normalize a Core program to Cut *)
let normalize_program (defs: CT.definitions) : CutT.program =
  List.map (fun (path, (tdef: CT.term_def)) ->
    let label = CutT.MkLabel path in
    (* Build environment from function parameters *)
    let prod_env = List.map (fun (v, ty) -> (v, type_to_chirality defs ty)) tdef.prod_args in
    let cons_env = List.map (fun (v, ty) -> (v, type_to_chirality defs ty)) tdef.cons_args in
    let gamma = prod_env @ cons_env in
    let body = normalize_statement defs tdef.body in
    (label, gamma, body)
  ) defs.term_defs

(** Complete normalization pipeline: Core definitions to Cut program
    
    This function combines Pass A (naming, shrinking, collapsing) and Pass B (linearization)
    to produce a fully normalized Cut program with explicit substitutions.
    
    @param defs Core definitions
    @return Cut program with linearized variable usage
*)
let normalize_definitions (defs: CT.definitions) : CutT.program =
  (* Pass A: Naming, shrinking, collapsing *)
  let cut_prog = normalize_program defs in
  (* Pass B: Linearization with explicit substitutions *)
  let linearized_prog = Linearization.linearize_program cut_prog in
  linearized_prog
