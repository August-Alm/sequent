(**
  Module: Cut.Terms
  Description: Term syntax of the intermediate language Cut.
  
  This module defines the abstract syntax of the intermediate language Cut,
  using the generalized type system from Cut.Types that supports higher-kinded
  types, polymorphism, and GADTs.
  
  See cut/gadt.txt for the full typing rules.
*)

open Common.Identifiers

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
  (* jump l *)
  | Jump of label
  (* substitute [v → v', ...]; s *)
  | Substitute of substitutions * statement
  (* extern m(v, ...){(Γ) ⇒ s, ...} *)
  | Extern of symbol * variable list * extern_branches
  (* let v = m[τ, ...](Γ); s - with type instantiation *)
  | Let of variable * symbol * typ list * typ_env * statement
  (* new v : T[τ, ...] = (Γ)b; s - with type instantiation *)
  | New of variable * typ * typ_env * branches * statement
  (* switch v b *)
  | Switch of variable * branches
  (* invoke v m[τ, ...](v, ...) - with type instantiation *)
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

(** Pretty printing *)

let string_of_typ = Types.Pretty.typ_to_string

let string_of_chirality = Types.Pretty.chirality_to_string

let string_of_var_typ (v, ty) =
  Ident.name v ^ " : " ^ string_of_chirality ty

let string_of_typ_env gamma =
  String.concat ", " (List.map string_of_var_typ gamma)

let string_of_typ_list tys =
  if tys = [] then ""
  else "[" ^ String.concat ", " (List.map string_of_typ tys) ^ "]"

let string_of_substitution (v1, v2) =
  Ident.name v1 ^ " → " ^ Ident.name v2

let string_of_substitutions subst =
  "[" ^ String.concat ", " (List.map string_of_substitution subst) ^ "]"

let rec string_of_statement ?(indent=0) s =
  let ind = String.make (indent * 2) ' ' in
  match s with
  | Jump l -> ind ^ "jump " ^ Label.to_string l
  
  | Substitute (subst, s') ->
    ind ^ "substitute " ^ string_of_substitutions subst ^ ";\n" ^
    string_of_statement ~indent s'
  
  | Extern (f, vars, branches) ->
    let vars_str = String.concat ", " (List.map Ident.name vars) in
    ind ^ "extern " ^ Symbol.to_string f ^ "(" ^ vars_str ^ ") {\n" ^
    string_of_extern_branches ~indent:(indent + 1) branches ^ "\n" ^
    ind ^ "}"
  
  | Let (v, m, tys, gamma, s') ->
    ind ^ "let " ^ Ident.name v ^ " = " ^ Symbol.to_string m ^
    string_of_typ_list tys ^ "(" ^ string_of_typ_env gamma ^ ");\n" ^
    string_of_statement ~indent s'
  
  | New (v, ty, gamma, branches, s') ->
    ind ^ "new " ^ Ident.name v ^ " : " ^ string_of_typ ty ^
    " = (" ^ string_of_typ_env gamma ^ ") {\n" ^
    string_of_branches ~indent:(indent + 1) branches ^ "\n" ^
    ind ^ "};\n" ^
    string_of_statement ~indent s'
  
  | Switch (v, branches) ->
    ind ^ "switch " ^ Ident.name v ^ " {\n" ^
    string_of_branches ~indent:(indent + 1) branches ^ "\n" ^
    ind ^ "}"
  
  | Invoke (v, m, tys, args) ->
    let arg_str = if args = [] then "" else "(" ^ String.concat ", " (List.map Ident.name args) ^ ")" in
    ind ^ "invoke " ^ Ident.name v ^ " " ^ Symbol.to_string m ^ string_of_typ_list tys ^ arg_str

and string_of_branches ?(indent=0) branches =
  let ind = String.make (indent * 2) ' ' in
  String.concat "\n" (List.map (fun (m, tys, gamma, s) ->
    ind ^ Symbol.to_string m ^ string_of_typ_list tys ^ "(" ^ string_of_typ_env gamma ^ ") ⇒\n" ^
    string_of_statement ~indent:(indent + 1) s
  ) branches)

and string_of_extern_branches ?(indent=0) branches =
  let ind = String.make (indent * 2) ' ' in
  String.concat "\n" (List.map (fun (gamma, s) ->
    ind ^ "(" ^ string_of_typ_env gamma ^ ") ⇒\n" ^
    string_of_statement ~indent:(indent + 1) s
  ) branches)

let string_of_definition (l, gamma, s) =
  "define " ^ Label.to_string l ^ "(" ^ string_of_typ_env gamma ^ ") =\n" ^
  string_of_statement ~indent:1 s

let string_of_program prog =
  String.concat "\n\n" (List.map string_of_definition prog)

(** Type checking *)

exception TypeError of string

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
    | None -> raise (TypeError ("Variable not in environment: " ^ Ident.name v))

  (** Check if two type environments are equal *)
  let equal (gamma1: typ_env) (gamma2: typ_env) : bool =
    List.length gamma1 = List.length gamma2 &&
    List.for_all2 (fun (v1, ty1) (v2, ty2) ->
      Ident.equal v1 v2 && Types.equal_chirality ty1 ty2
    ) gamma1 gamma2

  (** Split environment: Γ, Γ0 where Γ0 has length n *)
  let split_at (n: int) (gamma: typ_env) : typ_env * typ_env =
    let rec take acc i rest =
      if i = 0 then (List.rev acc, rest)
      else match rest with
      | [] -> raise (TypeError "Environment too short for split")
      | x :: xs -> take (x :: acc) (i - 1) xs
    in
    take [] n gamma

  (** Remove a variable from the front of the environment *)
  let remove_front (v: variable) (gamma: typ_env) : typ_env =
    match gamma with
    | (v', _) :: rest when Ident.equal v v' -> rest
    | _ -> raise (TypeError ("Variable " ^ Ident.name v ^ " not at front of environment"))
end

(** Signature utilities - see gadt.txt for typing rules *)
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
    | None -> raise (TypeError ("Signature not found for type: " ^ Symbol.to_string ty_sym))

  (** Find a method in a signature *)
  let find_method (m: symbol) (sig_def: signature) : method_sig option =
    List.find_opt (fun msig -> Path.equal msig.Types.symbol m) sig_def.Types.methods

  (** Find method, raising an error if not found *)
  let find_method_exn (m: symbol) (sig_def: signature) : method_sig =
    match find_method m sig_def with
    | Some msig -> msig
    | None -> raise (TypeError ("Method not found: " ^ Symbol.to_string m ^ 
                                " in signature " ^ Path.name sig_def.Types.symbol))
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
  match s with
  | Jump l ->
    (* Rule [JUMP]: Θ(l) = Γ
                    ----------
                    Γ ⊢ jump l *)
    let expected_gamma = 
      match List.assoc_opt l theta with
      | Some g -> g
      | None -> raise (TypeError ("Label not in environment: " ^ Label.to_string l))
    in
    if not (Env.equal gamma expected_gamma) then
      raise (TypeError ("Jump: environment mismatch for label " ^ Label.to_string l))

  | Substitute (pairs, s') ->
    (* Rule [SUBSTITUTE]: Γ'(v′ᵢ) = τᵢ    Γ(vᵢ) = τᵢ    Γ' ⊢ s
                          -------------------------------------------
                          Γ ⊢ substitute [v′₁ → v₁, ...]; s *)
    let gamma' = List.map (fun (v_new, v_old) ->
      let ty = Env.lookup_exn v_old gamma in
      (v_new, ty)
    ) pairs in
    check_statement sigs delta theta extern_env gamma' s'

  | Extern (m, vars, branches) ->
    (* Rule [EXTERN]: extern m : (τ₁, ...) ⇒ [(Γ₁), ...]
                      Γ(vᵢ) = τᵢ    Γ, Γⱼ ⊢ sⱼ
                      ------------------------------------
                      Γ ⊢ extern m(v₁, ...){(Γ₁) ⇒ s₁, ...} *)
    let (input_types, output_clauses) = 
      match List.assoc_opt m extern_env with
      | Some iface -> iface
      | None -> raise (TypeError ("Extern symbol not found: " ^ Symbol.to_string m))
    in
    if List.length vars <> List.length input_types then
      raise (TypeError ("Extern: wrong number of arguments for " ^ Symbol.to_string m));
    List.iter2 (fun v ty ->
      let v_ty = Env.lookup_exn v gamma in
      if not (Types.equal_chirality v_ty ty) then
        raise (TypeError ("Extern: argument type mismatch for " ^ Ident.name v))
    ) vars input_types;
    if List.length branches <> List.length output_clauses then
      raise (TypeError ("Extern: wrong number of branches for " ^ Symbol.to_string m));
    List.iter2 (fun (gamma_i, s_i) clause_gamma ->
      if not (Env.equal gamma_i clause_gamma) then
        raise (TypeError "Extern: branch environment mismatch");
      let extended_gamma = gamma_i @ gamma in
      check_statement sigs delta theta extern_env extended_gamma s_i
    ) branches output_clauses

  | Let (v, m, type_args, gamma0, s') ->
    (* Rule [LET]: Let binds a producer
       signature T(ᾱ : κ̄) = {..., m : ∀β̄. (Γᵖ) | () : τᵣ where C, ...} ∈ Σ
       θ = [ᾱ ↦ τ̄, β̄ ↦ σ̄]
       Γ₀ = θ(Γᵖ)    τ_v = prd (θ(τᵣ))
       Γ, v : τ_v ⊢ s
       -------------------------------------------------
       Γ, Γ₀ ⊢ let v = m[τ̄, σ̄](Γ₀); s
    *)
    (* Find which signature contains method m *)
    let (sig_def, _sig_kind) = 
      match List.find_opt (fun (_sym, (sig_def, _)) ->
        Signatures.find_method m sig_def <> None
      ) sigs with
      | Some (_, sk) -> sk
      | None -> raise (TypeError ("Method not found in any signature: " ^ Symbol.to_string m))
    in
    let msig = Signatures.find_method_exn m sig_def in
    
    (* Check type arguments match expected arity *)
    let expected_arity = List.length sig_def.Types.parameters + List.length msig.Types.quantified in
    if List.length type_args <> expected_arity then
      raise (TypeError (Printf.sprintf "Let: wrong number of type arguments for %s (expected %d, got %d)"
        (Symbol.to_string m) expected_arity (List.length type_args)));
    
    (* Build type substitution θ = [ᾱ ↦ τ̄, β̄ ↦ σ̄] *)
    let sig_params = List.map fst sig_def.Types.parameters in
    let method_quants = List.map fst msig.Types.quantified in
    let subst = List.combine (sig_params @ method_quants) type_args in
    
    (* Apply substitution to producer arguments *)
    let expected_gamma0 = List.map (fun (var, chi_ty) ->
      (var, Types.substitute_chirality subst chi_ty)
    ) msig.Types.producers in
    
    (* Check that gamma0 matches expected *)
    if not (Env.equal gamma0 expected_gamma0) then
      raise (TypeError ("Let: producer arguments mismatch for " ^ Symbol.to_string m));
    
    (* Split environment: Γ, Γ₀ *)
    let (gamma0_actual, gamma_rest) = Env.split_at (List.length gamma0) gamma in
    if not (Env.equal gamma0 gamma0_actual) then
      raise (TypeError "Let: environment split mismatch");
    
    (* Result type: prd (θ(τᵣ)) *)
    let result_ty = Types.Type.substitute subst msig.Types.result_type in
    let v_ty = Types.Prd result_ty in
    
    (* Check continuation with Γ, v : τ_v *)
    let new_gamma = (v, v_ty) :: gamma_rest in
    check_statement sigs delta theta extern_env new_gamma s'

  | New (v, ty, gamma0, branches, s') ->
    (* Rule [NEW]: New binds a consumer
       signature T(ᾱ : κ̄) = {m₁, ..., mₖ} ∈ Σ
       For each mᵢ: θᵢ = [ᾱ ↦ τ̄, β̄ᵢ ↦ σ̄ᵢ], check Γᵖᵢ', Γᶜᵢ', Γ₀ ⊢ sᵢ
       τ_v = cns (T(τ̄))
       Γ, v : τ_v ⊢ s
       -------------------------------------------------
       Γ, Γ₀ ⊢ new v : T(τ̄) = (Γ₀){m₁[...] ⇒ s₁, ...}; s
    *)
    (* Extract signature from type *)
    let (sig_sym, type_args) = match ty with
      | Types.TySig sig_def -> (sig_def.Types.symbol, [])
      | Types.TyApp _ ->
        (* Decompose type application to get signature and args *)
        let rec decompose acc = function
          | Types.TyApp (t1, t2) -> decompose (t2 :: acc) t1
          | Types.TySig sig_def -> (sig_def.Types.symbol, acc)
          | _ -> raise (TypeError "New: expected signature type")
        in
        decompose [] ty
      | _ -> raise (TypeError "New: expected signature type")
    in
    
    let (sig_def, _sig_kind) = Signatures.lookup_exn sig_sym sigs in
    
    (* Check all methods are present *)
    if List.length branches <> List.length sig_def.Types.methods then
      raise (TypeError ("New: wrong number of branches for " ^ Path.name sig_sym));
    
    (* Split environment: Γ, Γ₀ *)
    let (gamma0_actual, gamma_rest) = Env.split_at (List.length gamma0) gamma in
    if not (Env.equal gamma0 gamma0_actual) then
      raise (TypeError "New: environment split mismatch");
    
    (* Check each branch *)
    List.iter2 (fun (m_i, branch_type_args, branch_gamma, s_i) msig ->
      if not (Path.equal m_i msig.Types.symbol) then
        raise (TypeError ("New: branch method mismatch"));
      
      (* Build substitution for this branch *)
      let sig_params = List.map fst sig_def.Types.parameters in
      let method_quants = List.map fst msig.Types.quantified in
      let subst = List.combine (sig_params @ method_quants) (type_args @ branch_type_args) in
      
      (* Apply substitution to producer and consumer arguments *)
      let expected_branch_gamma = 
        List.map (fun (var, chi_ty) -> (var, Types.substitute_chirality subst chi_ty)) 
          (msig.Types.producers @ msig.Types.consumers)
      in
      
      if not (Env.equal branch_gamma expected_branch_gamma) then
        (Printf.eprintf "DEBUG: Branch environment mismatch for %s\n" (Symbol.to_string m_i);
         Printf.eprintf "  branch_gamma: %s\n" (string_of_typ_env branch_gamma);
         Printf.eprintf "  expected: %s\n" (string_of_typ_env expected_branch_gamma);
         raise (TypeError ("New: branch environment mismatch for " ^ Symbol.to_string m_i)));
      
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
       signature T(ᾱ : κ̄) = {m₁, ..., mₖ} ∈ Σ
       Γ(v) = prd (T(τ̄))
       For each mᵢ: θᵢ = [ᾱ ↦ τ̄, β̄ᵢ ↦ σ̄ᵢ], check Γ, Γᵖᵢ', Γᶜᵢ' ⊢ sᵢ
       -------------------------------------------------
       Γ, v : prd (T(τ̄)) ⊢ switch v {m₁[...](Γᵖ₁', Γᶜ₁') ⇒ s₁, ...}
    *)
    (match gamma with
    | (v', Types.Prd ty) :: gamma_rest when Ident.equal v v' ->
      (* Extract signature and type arguments from producer type *)
      let (sig_sym, type_args) = match ty with
        | Types.TySig sig_def -> (sig_def.Types.symbol, [])
        | Types.TyApp _ ->
          let rec decompose acc = function
            | Types.TyApp (t1, t2) -> decompose (t2 :: acc) t1
            | Types.TySig sig_def -> (sig_def.Types.symbol, acc)
            | _ -> raise (TypeError "Switch: expected signature type")
          in
          decompose [] ty
        | _ -> raise (TypeError "Switch: expected signature type")
      in
      
      let (sig_def, _sig_kind) = Signatures.lookup_exn sig_sym sigs in
      
      if List.length branches <> List.length sig_def.Types.methods then
        raise (TypeError ("Switch: wrong number of branches for " ^ Path.name sig_sym));
      
      (* Check each branch *)
      List.iter2 (fun (m_i, branch_type_args, branch_gamma, s_i) msig ->
        if not (Path.equal m_i msig.Types.symbol) then
          raise (TypeError ("Switch: branch method mismatch"));
        
        (* Build substitution *)
        let sig_params = List.map fst sig_def.Types.parameters in
        let method_quants = List.map fst msig.Types.quantified in
        let subst = List.combine (sig_params @ method_quants) (type_args @ branch_type_args) in
        
        (* Apply substitution to arguments *)
        let expected_branch_gamma = 
          List.map (fun (var, chi_ty) -> (var, Types.substitute_chirality subst chi_ty))
            (msig.Types.producers @ msig.Types.consumers)
        in
        
        if not (Env.equal branch_gamma expected_branch_gamma) then
          raise (TypeError ("Switch: branch environment mismatch for " ^ Symbol.to_string m_i));
        
        (* Check statement with Γ, Γᵖ, Γᶜ *)
        let branch_env = branch_gamma @ gamma_rest in
        check_statement sigs delta theta extern_env branch_env s_i
      ) branches sig_def.Types.methods
    | (v', _) :: _ when Ident.equal v v' ->
      raise (TypeError ("Switch: variable " ^ Ident.name v ^ " is not a producer"))
    | _ ->
      raise (TypeError ("Switch: variable " ^ Ident.name v ^ " not at front of environment")))

  | Invoke (v, m, type_args, args) ->
    (* Rule [INVOKE]: Invoking a method on a consumer
       signature T(ᾱ : κ̄) = {..., m : ∀β̄. (Γᵖ) | (Γᶜ) : τᵣ where C, ...} ∈ Σ
       Γ(v) = cns (T(τ̄))
       θ = [ᾱ ↦ τ̄, β̄ ↦ σ̄]
       Γ = (Γᵖ', Γᶜ', v : cns (T(τ̄)))
       -------------------------------------------------
       Γᵖ', Γᶜ', v : cns (T(τ̄)) ⊢ invoke v m[τ̄, σ̄](args)
    *)
    (match gamma with
    | (v', Types.Cns ty) :: gamma_rest when Ident.equal v v' ->
      (* Extract signature from consumer type *)
      let (sig_sym, sig_type_args) = match ty with
        | Types.TySig sig_def -> (sig_def.Types.symbol, [])
        | Types.TyApp _ ->
          let rec decompose acc = function
            | Types.TyApp (t1, t2) -> decompose (t2 :: acc) t1
            | Types.TySig sig_def -> (sig_def.Types.symbol, acc)
            | _ -> raise (TypeError "Invoke: expected signature type")
          in
          decompose [] ty
        | _ -> raise (TypeError "Invoke: expected signature type")
      in
      
      let (sig_def, _sig_kind) = Signatures.lookup_exn sig_sym sigs in
      let msig = Signatures.find_method_exn m sig_def in
      
      (* Build substitution θ = [ᾱ ↦ τ̄, β̄ ↦ σ̄] *)
      let sig_params = List.map fst sig_def.Types.parameters in
      let method_quants = List.map fst msig.Types.quantified in
      let subst = List.combine (sig_params @ method_quants) (sig_type_args @ type_args) in
      
      (* Apply substitution to producer and consumer arguments *)
      let expected_args = 
        List.map (fun (var, chi_ty) -> (var, Types.substitute_chirality subst chi_ty))
          (msig.Types.producers @ msig.Types.consumers)
      in
      
      (* Build actual argument environment from args *)
      let actual_args = List.map (fun arg ->
        match List.assoc_opt arg gamma_rest with
        | Some typ -> (arg, typ)
        | None -> raise (TypeError ("Invoke: variable " ^ Ident.name arg ^ " not in environment"))
      ) args in
      
      (* Check that actual matches expected *)
      if not (Env.equal actual_args expected_args) then
        raise (TypeError ("Invoke: argument environment mismatch for " ^ Symbol.to_string m))
    | (v', _) :: _ when Ident.equal v v' ->
      raise (TypeError ("Invoke: variable " ^ Ident.name v ^ " is not a consumer"))
    | _ ->
      raise (TypeError ("Invoke: variable " ^ Ident.name v ^ " not at front of environment")))


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
      match List.assoc_opt l theta with
      | Some g -> g
      | None -> raise (TypeError ("Label not in environment: " ^ Label.to_string l))
    in
    if not (Env.equal gamma expected_gamma) then
      raise (TypeError ("Program: environment mismatch for label " ^ Label.to_string l));
    (* Check the statement in empty type variable context *)
    check_statement sigs delta theta extern_env gamma s
  ) prog
