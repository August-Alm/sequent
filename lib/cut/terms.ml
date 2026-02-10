(**
  Module: Cut.Cut
  Description: Minimal term syntax of the intermediate language Cut.
  
  This module defines the abstract syntax of the intermediate language Cut,
  using the generalized type system from Cut.Types that supports higher-kinded
  types, polymorphism, and GADTs.
  
  See cut/specification.txt for the full typing rules.
*)

open Common.Identifiers

(* ========================================================================= *)
(* Abstract syntax                                                           *)
(* ========================================================================= *)

type symbol = Path.t

type variable = Ident.t 

type label = MkLabel of Path.t

(* Use the rich type system from Cut.Types *)
type typ = Types.typ
type chirality_type = Types.chirality_type
type kind = Types.kind
type signature = Types.signature
type method_sig = Types.method_sig

(* type environment Γ ::= v : τ, ... *)
type typ_env = (variable * chirality_type) list

(* type variable environment Δ ::= α : κ, ... *)
type type_env = Types.type_env

(* label environment Θ ::= l : Γ, ... *)
type label_env = (label * typ_env) list

(* Signatures Σ: global collection of signature definitions *)
type signatures = Types.signature_defs

(* [v → v', ...] *)
type substitutions = (variable * variable) list

type statement =
  (* jump l[τ, ...] *)
  | Jump of label * typ list
  (* forward x to k *)
  | Forward of variable * variable
  (* substitute [v → v', ...]; s *)
  | Substitute of substitutions * statement
  (* extern m(v, ...){(Γ) ⇒ s, ...} *)
  | Extern of symbol * variable list * extern_branches
  (* let v = m[τ, ...](Γ); s - from ⟨C(Γ) | µ˜x.s⟩, v : prd T *)
  | Let of variable * symbol * typ list * typ_env * statement
  (* new v : T[τ, ...] = (Γ)b; s - from ⟨cocase {...} | µ˜x.s⟩, v : cns T *)
  | New of variable * typ * typ_env * branches * statement
  (* switch v b - from ⟨x | case {...}⟩, v : prd T *)
  | Switch of variable * branches
  (* invoke v m[τ, ...](v, ...) - from ⟨x | D(Γ)⟩, v : cns T *)
  | Invoke of variable * symbol * typ list * variable list

(* branches b ::= {m[τ, ...](Γ) ⇒ s, ...} - with type instantiation *)
and branches = (symbol * typ list * typ_env * statement) list

(* extern branches {(Γ) ⇒ s, ...} *)
and extern_branches = (typ_env * statement) list

(* programs P ::= define l : Γ = s, ... *)
type program = (label * typ_env * statement) list

(* Complete definitions including type signatures and program *)
type definitions = {
  signatures: signatures;
  program: program;
}

module Label = struct
  let to_string (MkLabel l) = Path.name l
end

module Symbol = struct
  let to_string = Path.name
end


(* ========================================================================= *)
(* Type-checking                                                             *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Type errors                                                               *)
(* ========================================================================= *)

exception VariableNotInEnv of variable * typ_env
exception LabelNotInEnv of label
exception SignatureNotFound of symbol
exception MethodNotFound of symbol * signature
exception ExternNotFound of symbol
exception EnvTooShort of int * typ_env
exception EnvSplitMismatch of typ_env * typ_env
exception VariableNotAtFront of variable * typ_env
exception ForwardTypeMismatch of variable * chirality_type * variable * chirality_type
exception ForwardNotProducer of variable * chirality_type
exception ForwardNotConsumer of variable * chirality_type
exception JumpEnvMismatch of label * typ_env * typ_env
exception ExternArgCountMismatch of symbol * int * int
exception ExternArgTypeMismatch of variable * chirality_type * chirality_type
exception ExternBranchCountMismatch of symbol * int * int
exception ExternBranchEnvMismatch of typ_env * typ_env
exception LetTypeArgCountMismatch of symbol * int * int
exception LetArgCountMismatch of symbol * int * int
exception LetArgTypeMismatch of symbol * chirality_type * chirality_type
exception NewBranchCountMismatch of symbol * int * int
exception NewBranchMethodMismatch of symbol * symbol
exception NewBranchArgCountMismatch of symbol * int * int
exception NewBranchArgTypeMismatch of symbol * chirality_type * chirality_type
exception NewExpectedSignatureType of typ
exception SwitchNotProducer of variable * chirality_type
exception SwitchVariableNotAtFront of variable * typ_env
exception SwitchBranchCountMismatch of symbol * int * int
exception SwitchBranchMethodMismatch of symbol * symbol
exception SwitchBranchArgCountMismatch of symbol * int * int
exception SwitchBranchArgTypeMismatch of symbol * chirality_type * chirality_type
exception SwitchExpectedSignatureType of typ
exception InvokeNotConsumer of variable * chirality_type
exception InvokeVariableNotAtFront of variable * typ_env
exception InvokeArgCountMismatch of symbol * int * int
exception InvokeArgTypeMismatch of symbol * chirality_type * chirality_type
exception InvokeArgNotInEnv of variable
exception InvokeExpectedSignatureType of typ

(* External symbol interface: (input types, output clauses) 
   Each output clause specifies the types of variables it binds *)
type extern_interface = chirality_type list * (typ_env list)

(* External environment: maps extern symbols to their interfaces *)
type extern_env = (symbol * extern_interface) list

module Env = struct
  (** Look up a variable in the type environment *)
  let rec lookup (v: variable) (gamma: typ_env) : chirality_type option =
    match gamma with
    | [] -> None
    | (v', ty) :: rest ->
      if Ident.equal v v' then Some ty
      else lookup v rest

  (** Look up a variable, raising an error if not found *)
  let lookup_exn (v: variable) (gamma: typ_env) : chirality_type =
    match lookup v gamma with
    | Some ty -> ty
    | None -> raise (VariableNotInEnv (v, gamma))

  (** Check if two type environments are equal *)
  let equal sigs (gamma1: typ_env) (gamma2: typ_env) : bool =
    List.length gamma1 = List.length gamma2 &&
    List.for_all2 (fun (v1, ty1) (v2, ty2) ->
      Ident.equal v1 v2 && Types.equivalent_chirality sigs ty1 ty2
    ) gamma1 gamma2

  (** Split environment: Γ, Γ0 where Γ0 has length n *)
  let split_at (n: int) (gamma: typ_env) : typ_env * typ_env =
    let rec take acc i rest =
      if i = 0 then (List.rev acc, rest)
      else match rest with
      | [] -> raise (EnvTooShort (n, gamma))
      | x :: xs -> take (x :: acc) (i - 1) xs
    in
    take [] n gamma

  (** Remove a variable from the front of the environment *)
  let remove_front (v: variable) (gamma: typ_env) : typ_env =
    match gamma with
    | (v', _) :: rest when Ident.equal v v' -> rest
    | _ -> raise (VariableNotAtFront (v, gamma))
end

(** Signature utilities - see gadt.txt for typing rules *)
module LabelEnv = struct
  (** Look up a label in the label environment *)
  let rec lookup (l: label) (theta: label_env) : typ_env option =
    match theta with
    | [] -> None
    | (l', gamma) :: rest ->
      let (MkLabel p1) = l in
      let (MkLabel p2) = l' in
      if Path.equal p1 p2 then Some gamma
      else lookup l rest
end

module Signatures = struct
  (** Look up a signature by type symbol *)
  let rec lookup (ty_sym: symbol) (sigs: signatures) : (signature * kind) option =
    match sigs with
    | [] -> None
    | (ty_sym', sk) :: rest ->
      if Path.equal ty_sym ty_sym' then Some sk
      else lookup ty_sym rest

  (** Look up a signature, raising an error if not found *)
  let lookup_exn (ty_sym: symbol) (sigs: signatures) : signature * kind =
    match lookup ty_sym sigs with
    | Some sk -> sk
    | None -> raise (SignatureNotFound ty_sym)

  (** Find a method in a signature *)
  let find_method (m: symbol) (sig_def: signature) : method_sig option =
    let rec go (methods:  method_sig list) m =
      match methods with
      | [] -> None
      | msig :: rest ->
        if Path.equal msig.Types.symbol m then Some msig
        else go rest m
    in
    go sig_def.Types.methods m

  (** Find method, raising an error if not found *)
  let find_method_exn (m: symbol) (sig_def: signature) : method_sig =
    match find_method m sig_def with
    | Some msig -> msig
    | None -> raise (MethodNotFound (m, sig_def))
end

module ExternEnv = struct
  (** Look up an extern symbol in the extern environment *)
  let rec lookup (m: symbol) (env: extern_env) : extern_interface option =
    match env with
    | [] -> None
    | (m', iface) :: rest ->
      if Path.equal m m' then Some iface
      else lookup m rest
end


(** Check a statement against a type environment
    Rule: Σ; Δ; Θ; Γ ⊢ s
    See gadt.txt for full typing rules with polymorphism and GADTs.
*)
let rec check_statement 
    (sigs: signatures) 
    (delta: type_env)
    (theta: label_env) 
    (extern_env: extern_env)
    (gamma: typ_env) 
    (s: statement) : unit =
  if false then begin
    Printf.eprintf "\n[CHECK_STATEMENT] Env size: %d\n" (List.length gamma);
    Printf.eprintf "Statement: %s\n" (match s with
      | Jump _ -> "Jump"
      | Forward _ -> "Forward"
      | Substitute _ -> "Substitute"
      | Let _ -> "Let"
      | New _ -> "New"
      | Switch _ -> "Switch"
      | Invoke _ -> "Invoke"
      | Extern _ -> "Extern");
  end;
  match s with
  | Jump (l, _type_args) ->
    (* Rule [JUMP]: Θ(l) = Γ'    θ = [β̄ ↦ τ̄]    Γ = θ(Γ')
                    ----------------------------------------
                    Γ ⊢ jump l[τ̄] *)
    let expected_gamma = 
      match LabelEnv.lookup l theta with
      | Some g -> g
      | None -> raise (LabelNotInEnv l)
    in
    (* TODO: Check type_args are well-kinded and apply type substitution θ to expected_gamma *)
    if not (Env.equal sigs gamma expected_gamma) then
      raise (JumpEnvMismatch (l, expected_gamma, gamma))
  
  | Forward (x, k) ->
    (* Rule [FORWARD]: Γ(x) = prd τ    Γ(k) = cns τ
                      ----------------------------
                      Γ ⊢ forward x k *)
    let x_ty = Env.lookup_exn x gamma in
    let k_ty = Env.lookup_exn k gamma in
    (match (x_ty, k_ty) with
    | (Types.Prd tx, Types.Cns tk) ->
      if not (Types.Type.equivalent sigs tx tk) then
        raise (ForwardTypeMismatch (x, x_ty, k, k_ty))
    | (Types.Prd _, _) ->
      raise (ForwardNotConsumer (k, k_ty))
    | _ ->
      raise (ForwardNotProducer (x, x_ty)))

  | Substitute (pairs, s') ->
    (* Rule [SUBSTITUTE]: Γ'(v′ᵢ) = τᵢ    Γ(vᵢ) = τᵢ    Γ' ⊢ s
                          -------------------------------------------
                          Γ ⊢ substitute [v′₁ → v₁, ...]; s *)
    if false then begin
      Printf.eprintf "\n[SUBSTITUTE] Input env:\n";
      List.iter (fun (v, ty) ->
        Printf.eprintf "  %s : %s\n" (Ident.name v) (Types.Pretty.chirality_to_string ty)
      ) gamma;
      Printf.eprintf "  Pairs:\n";
      List.iter (fun (v_new, v_old) ->
        Printf.eprintf "    %s → %s\n" (Ident.name v_new) (Ident.name v_old)
      ) pairs;
    end;
    let gamma' = List.map (fun (v_new, v_old) ->
      let ty = Env.lookup_exn v_old gamma in
      (v_new, ty)
    ) pairs in
    if false then begin
      Printf.eprintf "  Output env:\n";
      List.iter (fun (v, ty) ->
        Printf.eprintf "  %s : %s\n" (Ident.name v) (Types.Pretty.chirality_to_string ty)
      ) gamma';
    end;
    check_statement sigs delta theta extern_env gamma' s'

  | Extern (m, vars, branches) ->
    (* Rule [EXTERN]: extern m : (τ₁, ...) ⇒ [(Γ₁), ...]
                      Γ(vᵢ) = τᵢ    Γ, Γⱼ ⊢ sⱼ
                      ------------------------------------
                      Γ ⊢ extern m(v₁, ...){(Γ₁) ⇒ s₁, ...} *)
    let (input_types, output_clauses) = 
      match ExternEnv.lookup m extern_env with
      | Some iface -> iface
      | None -> raise (ExternNotFound m)
    in
    if List.length vars <> List.length input_types then
      raise (ExternArgCountMismatch (m, List.length input_types, List.length vars));
    List.iter2 (fun v ty ->
      let v_ty = Env.lookup_exn v gamma in
      if not (Types.equivalent_chirality sigs v_ty ty) then
        raise (ExternArgTypeMismatch (v, v_ty, ty))
    ) vars input_types;
    if List.length branches <> List.length output_clauses then
      raise (ExternBranchCountMismatch (m, List.length output_clauses, List.length branches));
    List.iter2 (fun (gamma_i, s_i) clause_gamma ->
      if not (Env.equal sigs gamma_i clause_gamma) then
        raise (ExternBranchEnvMismatch (gamma_i, clause_gamma));
      let extended_gamma = gamma_i @ gamma in
      check_statement sigs delta theta extern_env extended_gamma s_i
    ) branches output_clauses

  | Let (v, m, type_args, gamma0, s') ->
    (* Rule [LET]: Let binds a producer
       signature T : κ = {..., m : ∀β̄:κ̄'. Γ : prd τᵣ where C, ...} ∈ Σ
       θ = [ᾱ ↦ τ̄, β̄ ↦ σ̄]
       Γ' = θ(Γ)    τ_v = θ(prd τᵣ)
       Γ_ctx, v : τ_v ⊢ s
       -------------------------------------------------
       Γ_ctx, Γ' ⊢ let v = m[σ̄](Γ'); s
    *)
    (* Find which signature contains method m *)
    let (sig_def, _sig_kind) = 
      match List.find_opt (fun (_sym, (sig_def, _)) ->
        Signatures.find_method m sig_def <> None
      ) sigs with
      | Some (_, sk) -> sk
      | None -> raise (MethodNotFound (m, { Types.symbol = m; parameters = []; methods = [] }))
    in
    let msig = Signatures.find_method_exn m sig_def in
    
    (* Check type arguments match expected arity.
       In the unified environment syntax, signatures don't bind type variables -
       each method quantifies all type variables it needs, so θ = [β̄ ↦ σ̄] *)
    let expected_arity = List.length msig.Types.quantified in
    if List.length type_args <> expected_arity then
      raise (LetTypeArgCountMismatch (m, expected_arity, List.length type_args));
    
    (* Build type substitution θ = [β̄ ↦ σ̄] (method quantifiers only) *)
    let method_quants = List.map fst msig.Types.quantified in
    let subst = List.combine method_quants type_args in
    
    (* Apply substitution to environment types *)
    let expected_types = List.map (fun (_name, chi_ty) ->
      Types.substitute_chirality subst chi_ty
    ) msig.Types.environment in
    
    (* Check that gamma0 types match expected types by position *)
    if List.length gamma0 <> List.length expected_types then
      raise (LetArgCountMismatch (m, List.length expected_types, List.length gamma0));
    
    List.iter2 (fun (_var, actual_ty) expected_ty ->
      if not (Types.equivalent_chirality sigs actual_ty expected_ty) then
        raise (LetArgTypeMismatch (m, actual_ty, expected_ty))
    ) gamma0 expected_types;
    
    (* Split environment: Γ, Γ₀ *)
    let (gamma0_actual, gamma_rest) = Env.split_at (List.length gamma0) gamma in
    if not (Env.equal sigs gamma0 gamma0_actual) then
      raise (EnvSplitMismatch (gamma0, gamma0_actual));
    
    (* Result type is already polarized in the method signature *)
    let v_ty = Types.substitute_chirality subst msig.Types.result_type in
    
    (* Check continuation with Γ, v : τ_v *)
    let new_gamma = (v, v_ty) :: gamma_rest in
    check_statement sigs delta theta extern_env new_gamma s'

  | New (v, ty, gamma0, branches, s') ->
    (* Rule [NEW]: New binds a consumer
       signature T : κ = {m₁, ..., mₖ} ∈ Σ
       For each mᵢ: θᵢ = [ᾱ ↦ τ̄, β̄ᵢ ↦ σ̄ᵢ], check Γᵢ', Γ₀ ⊢ sᵢ
       τ_v = cns (T[τ̄])
       Γ_ctx, v : τ_v ⊢ s
       -------------------------------------------------
       Γ_ctx, Γ₀ ⊢ new v : T[τ̄] = (Γ₀){m₁[σ̄₁](Γ₁') ⇒ s₁, ...}; s
    *)
    (* Extract signature from type by reducing to weak head normal form *)
    let _, ty_whnf = Types.Type.whnf [] sigs ty in
    let (sig_sym, sig_def_opt) = match ty_whnf with
      | Types.TyDef sig_def ->
        (* Instantiated signature - extract parameters *)
        (sig_def.Types.symbol, Some sig_def)
      | Types.TySym sym ->
        (* Un-instantiated reference *)
        (sym, None)
      | Types.TyApp _ ->
        (* Shouldn't happen after whnf, but handle it *)
        let rec decompose = function
          | Types.TyApp (t1, _t2) -> decompose t1
          | Types.TySym sym -> (sym, None)
          | Types.TyDef sig_def ->
            (sig_def.Types.symbol, Some sig_def)
          | other -> raise (NewExpectedSignatureType other)
        in
        decompose ty_whnf
      | other -> raise (NewExpectedSignatureType other)
    in
    
    (* Look up or use the signature *)
    let sig_def = match sig_def_opt with
      | Some sd -> sd
      | None ->
        let (sd, _sig_kind) = Signatures.lookup_exn sig_sym sigs in
        sd
    in
    
    (* Check all methods are present *)
    if List.length branches <> List.length sig_def.Types.methods then
      raise (NewBranchCountMismatch (sig_sym, List.length sig_def.Types.methods, List.length branches));
    
    (* Split environment: Γ, Γ0 *)
    let (gamma0_actual, gamma_rest) = Env.split_at (List.length gamma0) gamma in
    if not (Env.equal sigs gamma0 gamma0_actual) then
      raise (EnvSplitMismatch (gamma0, gamma0_actual));
    
    (* Check each branch *)
    List.iter2 (fun (m_i, branch_type_args, branch_gamma, s_i) msig ->
      if not (Path.equal m_i msig.Types.symbol) then
        raise (NewBranchMethodMismatch (m_i, msig.Types.symbol));
      
      (* Build substitution θ = [β̄ᵢ ↦ σ̄ᵢ] (method quantifiers only) *)
      let method_quants = List.map fst msig.Types.quantified in
      let subst = List.combine method_quants branch_type_args in
      
      (* Apply substitution to environment types *)
      let expected_types = 
        List.map (fun (_name, chi_ty) -> Types.substitute_chirality subst chi_ty) 
          msig.Types.environment
      in
      
      (* Check types match by position *)
      if List.length branch_gamma <> List.length expected_types then
        raise (NewBranchArgCountMismatch (m_i, List.length expected_types, List.length branch_gamma));
      
      List.iter2 (fun (_var, actual_ty) expected_ty ->
        if not (Types.equivalent_chirality sigs actual_ty expected_ty) then
          raise (NewBranchArgTypeMismatch (m_i, actual_ty, expected_ty))
      ) branch_gamma expected_types;
      
      (* Check statement with Γᵖ, Γᶜ, Γ₀ *)
      let branch_env = branch_gamma @ gamma0 in
      check_statement sigs delta theta extern_env branch_env s_i
    ) branches sig_def.Types.methods;
    
    (* Result type: cns (T(τ̄)) *)
    let v_ty = Types.Cns ty in
    
    (* Check continuation with Γ, v : τ_v *)
    let new_gamma = (v, v_ty) :: gamma_rest in
    check_statement sigs delta theta extern_env new_gamma s'

  | Switch (v, branches) ->
    (* Rule [SWITCH]: Pattern matching on a producer
       signature T : κ = {m₁, ..., mₖ} ∈ Σ
       Γ_ctx(v) = prd (T[τ̄])
       For each mᵢ: θᵢ = [ᾱ ↦ τ̄, β̄ᵢ ↦ σ̄ᵢ], check Γ_ctx, Γᵢ' ⊢ sᵢ
       -------------------------------------------------
       Γ_ctx, v : prd (T[τ̄]) ⊢ switch v {m₁[σ̄₁](Γ₁') ⇒ s₁, ...}
    *)
    (match gamma with
    | (v', Types.Prd ty) :: gamma_rest when Ident.equal v v' ->
      (* Extract signature and type arguments from producer type using whnf *)
      let _, ty_whnf = Types.Type.whnf [] sigs ty in
      let (sig_sym, sig_def_opt) = match ty_whnf with
        | Types.TyDef sig_def ->
          (sig_def.Types.symbol, Some sig_def)
        | Types.TySym sym ->
          (sym, None)
        | Types.TyApp _ ->
          let rec decompose = function
            | Types.TyApp (t1, _t2) -> decompose t1
            | Types.TySym sym -> (sym, None)
            | Types.TyDef sig_def ->
              (sig_def.Types.symbol, Some sig_def)
            | other -> raise (SwitchExpectedSignatureType other)
          in
          decompose ty_whnf
        | other -> raise (SwitchExpectedSignatureType other)
      in
      
      let sig_def = match sig_def_opt with
        | Some sd -> sd
        | None ->
          let (sd, _sig_kind) = Signatures.lookup_exn sig_sym sigs in
          sd
      in
      
      if List.length branches <> List.length sig_def.Types.methods then
        raise (SwitchBranchCountMismatch (sig_sym, List.length sig_def.Types.methods, List.length branches));
      
      (* Check each branch *)
      List.iter2 (fun (m_i, branch_type_args, branch_gamma, s_i) msig ->
        if not (Path.equal m_i msig.Types.symbol) then
          raise (SwitchBranchMethodMismatch (m_i, msig.Types.symbol));
        
        (* Build substitution θ = [β̄ᵢ ↦ σ̄ᵢ] (method quantifiers only) *)
        let method_quants = List.map fst msig.Types.quantified in
        let subst = List.combine method_quants branch_type_args in
        
        (* Apply substitution to environment types *)
        let expected_types = 
          List.map (fun (_name, chi_ty) -> Types.substitute_chirality subst chi_ty)
            msig.Types.environment
        in
        
        (* Check types match by position *)
        if List.length branch_gamma <> List.length expected_types then
          raise (SwitchBranchArgCountMismatch (m_i, List.length expected_types, List.length branch_gamma));
        
        List.iter2 (fun (_var, actual_ty) expected_ty ->
          if not (Types.equivalent_chirality sigs actual_ty expected_ty) then
            raise (SwitchBranchArgTypeMismatch (m_i, actual_ty, expected_ty))
        ) branch_gamma expected_types;
        
        (* Check statement with Γ, Γᵖ, Γᶜ *)
        let branch_env = branch_gamma @ gamma_rest in
        check_statement sigs delta theta extern_env branch_env s_i
      ) branches sig_def.Types.methods
    | (v', ty) :: _ when Ident.equal v v' ->
      raise (SwitchNotProducer (v, ty))
    | _ ->
      raise (SwitchVariableNotAtFront (v, gamma)))

  | Invoke (v, m, type_args, args) ->
    (* Rule [INVOKE]: Invoking a method on a consumer
       signature T : κ = {..., m : ∀β̄:κ̄'. Γ : cns τᵣ where C, ...} ∈ Σ
       Γ_ctx(v) = cns (T[τ̄])
       θ = [ᾱ ↦ τ̄, β̄ ↦ σ̄]
       Γ' = θ(Γ)
       Γ_ctx = (Γ', v : cns (T[τ̄]))
       -------------------------------------------------
       Γ', v : cns (T[τ̄]) ⊢ invoke v m[σ̄](Γ')
    *)
    (match gamma with
    | (v', Types.Cns ty) :: gamma_rest when Ident.equal v v' ->
      (* Extract signature from consumer type using whnf *)
      let _, ty_whnf = Types.Type.whnf [] sigs ty in
      let (sig_sym, sig_def_opt) = match ty_whnf with
        | Types.TyDef sig_def ->
          (sig_def.Types.symbol, Some sig_def)
        | Types.TySym sym ->
          (sym, None)
        | Types.TyApp _ ->
          let rec decompose = function
            | Types.TyApp (t1, _t2) -> decompose t1
            | Types.TySym sym -> (sym, None)
            | Types.TyDef sig_def ->
              (sig_def.Types.symbol, Some sig_def)
            | other -> raise (InvokeExpectedSignatureType other)
          in
          decompose ty_whnf
        | other -> raise (InvokeExpectedSignatureType other)
      in
      
      let sig_def = match sig_def_opt with
        | Some sd -> sd
        | None ->
          let (sd, _sig_kind) = Signatures.lookup_exn sig_sym sigs in
          sd
      in
      let msig = Signatures.find_method_exn m sig_def in
      
      (* Build substitution θ = [β̄ ↦ σ̄] (method quantifiers only).
         In unified environment syntax, methods quantify all their type variables. *)
      let method_quants = List.map fst msig.Types.quantified in
      let subst = List.combine method_quants type_args in
      
      (* Apply substitution to environment types *)
      let expected_types = 
        List.map (fun (_name, chi_ty) -> Types.substitute_chirality subst chi_ty)
          msig.Types.environment
      in
      
      (* Build actual argument types from args *)
      let actual_types = List.map (fun arg ->
        match Env.lookup arg gamma_rest with
        | Some typ -> typ
        | None -> raise (InvokeArgNotInEnv arg)
      ) args in
      
      (* Check that actual types match expected types by position *)
      if List.length actual_types <> List.length expected_types then
        raise (InvokeArgCountMismatch (m, List.length expected_types, List.length actual_types));
      
      List.iter2 (fun actual_ty expected_ty ->
        if not (Types.equivalent_chirality sigs actual_ty expected_ty) then
          raise (InvokeArgTypeMismatch (m, actual_ty, expected_ty))
      ) actual_types expected_types
    | (v', ty) :: _ when Ident.equal v v' ->
      raise (InvokeNotConsumer (v, ty))
    | _ ->
      raise (InvokeVariableNotAtFront (v, gamma)))


(** Check a program
    Rule [PROGRAM]: Σ; ∅ ⊢ Θ    Θ(l) = Γ    Σ; ∅; Θ; Γ ⊢ s    ...
                    -----------------------------------------------
                    Σ Θ ⊢ define l₁ : Γ₁ = s₁, ..., lₙ : Γₙ = sₙ
    
    Programs are typed in empty type variable environment (∅).
*)
let check_program 
    (sigs: signatures) 
    (extern_env: extern_env)
    (prog: program) : unit =
  (* Build label environment from program *)
  let theta = List.map (fun (l, gamma, _) -> (l, gamma)) prog in
  (* Empty type variable environment *)
  let delta = [] in
  (* Check each definition *)
  List.iter (fun (l, gamma, s) ->
    (* Verify label is in theta with correct type *)
    let expected_gamma = 
      match LabelEnv.lookup l theta with
      | Some g -> g
      | None -> raise (LabelNotInEnv l)
    in
    if not (Env.equal sigs gamma expected_gamma) then
      raise (JumpEnvMismatch (l, expected_gamma, gamma));
    (* Check the statement in empty type variable context *)
    check_statement sigs delta theta extern_env gamma s
  ) prog

