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
  (* jump l[τ, ...] *)
  | Jump of label * typ list
  (* return x to k *)
  | Return of variable * variable
  (* substitute [v → v', ...]; s *)
  | Substitute of substitutions * statement
  (* extern m(v, ...){(Γ) ⇒ s, ...} *)
  | Extern of symbol * variable list * extern_branches
  (* let v = m[τ, ...](Γ); s - from ⟨C(Γ) | µ˜x.s⟩, v : prd T *)
  | Let of variable * symbol * typ list * typ_env * statement
  (* letcns v = m[τ, ...](Γ); s - from ⟨µα.s | D(Γ)⟩, v : cns T *)
  | LetCns of variable * symbol * typ list * typ_env * statement
  (* new v : T[τ, ...] = (Γ)b; s - from ⟨cocase {...} | µ˜x.s⟩, v : cns T *)
  | New of variable * typ * typ_env * branches * statement
  (* newprd v : T[τ, ...] = (Γ)b; s - from ⟨µα.s | case {...}⟩, v : prd T *)
  | NewPrd of variable * typ * typ_env * branches * statement
  (* switch v b - from ⟨x | case {...}⟩, v : prd T *)
  | Switch of variable * branches
  (* switchcns v b - from ⟨cocase {...} | α⟩, v : cns T *)
  | SwitchCns of variable * branches
  (* invoke v m[τ, ...](v, ...) - from ⟨x | D(Γ)⟩, v : cns T *)
  | Invoke of variable * symbol * typ list * variable list
  (* invokeprd v m[τ, ...](v, ...) - from ⟨C(Γ) | α⟩, v : prd T *)
  | InvokePrd of variable * symbol * typ list * variable list

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
  | Jump (l, tys) -> ind ^ "jump " ^ Label.to_string l ^ string_of_typ_list tys
  
  | Return (x, k) -> ind ^ "return " ^ Ident.name x ^ " to " ^ Ident.name k
  
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
  
  | LetCns (v, m, tys, gamma, s') ->
    ind ^ "letcns " ^ Ident.name v ^ " = " ^ Symbol.to_string m ^
    string_of_typ_list tys ^ "(" ^ string_of_typ_env gamma ^ ");\n" ^
    string_of_statement ~indent s'
  
  | New (v, ty, gamma, branches, s') ->
    ind ^ "new " ^ Ident.name v ^ " : " ^ string_of_typ ty ^
    " = (" ^ string_of_typ_env gamma ^ ") {\n" ^
    string_of_branches ~indent:(indent + 1) branches ^ "\n" ^
    ind ^ "};\n" ^
    string_of_statement ~indent s'
  
  | NewPrd (v, ty, gamma, branches, s') ->
    ind ^ "newprd " ^ Ident.name v ^ " : " ^ string_of_typ ty ^
    " = (" ^ string_of_typ_env gamma ^ ") {\n" ^
    string_of_branches ~indent:(indent + 1) branches ^ "\n" ^
    ind ^ "};\n" ^
    string_of_statement ~indent s'
  
  | Switch (v, branches) ->
    ind ^ "switch " ^ Ident.name v ^ " {\n" ^
    string_of_branches ~indent:(indent + 1) branches ^ "\n" ^
    ind ^ "}"
  
  | SwitchCns (v, branches) ->
    ind ^ "switchcns " ^ Ident.name v ^ " {\n" ^
    string_of_branches ~indent:(indent + 1) branches ^ "\n" ^
    ind ^ "}"
  
  | Invoke (v, m, tys, args) ->
    let arg_str = if args = [] then "" else "(" ^ String.concat ", " (List.map Ident.name args) ^ ")" in
    ind ^ "invoke " ^ Ident.name v ^ " " ^ Symbol.to_string m ^ string_of_typ_list tys ^ arg_str
  
  | InvokePrd (v, m, tys, args) ->
    let arg_str = if args = [] then "" else "(" ^ String.concat ", " (List.map Ident.name args) ^ ")" in
    ind ^ "invokeprd " ^ Ident.name v ^ " " ^ Symbol.to_string m ^ string_of_typ_list tys ^ arg_str

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
    | None -> 
      Printf.eprintf "ERROR: Variable %s not in environment\n" (Ident.name v);
      Printf.eprintf "Environment has %d variables:\n" (List.length gamma);
      List.iter (fun (v', ty) ->
        Printf.eprintf "  %s : %s\n" (Ident.name v') (Types.Pretty.chirality_to_string ty)
      ) gamma;
      raise (TypeError ("Variable not in environment: " ^ Ident.name v))

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
    | None -> raise (TypeError ("Signature not found for type: " ^ Symbol.to_string ty_sym))

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
    | None -> raise (TypeError ("Method not found: " ^ Symbol.to_string m ^ 
                                " in signature " ^ Path.name sig_def.Types.symbol))
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
      | Return _ -> "Return"
      | Substitute _ -> "Substitute"
      | Let _ -> "Let"
      | LetCns _ -> "LetCns"
      | New _ -> "New"
      | NewPrd _ -> "NewPrd"
      | Switch _ -> "Switch"
      | SwitchCns _ -> "SwitchCns"
      | Invoke _ -> "Invoke"
      | InvokePrd _ -> "InvokePrd"
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
      | None -> raise (TypeError ("Label not in environment: " ^ Label.to_string l))
    in
    (* TODO: Check type_args are well-kinded and apply type substitution θ to expected_gamma *)
    if not (Env.equal sigs gamma expected_gamma) then begin
      Printf.eprintf "\n=== Jump environment mismatch for label %s ===\n" (Label.to_string l);
      Printf.eprintf "Expected environment (from label definition): [";
      List.iter (fun (v, ty) -> 
        Printf.eprintf "%s:%s; " (Ident.name v) (string_of_chirality ty)
      ) expected_gamma;
      Printf.eprintf "]\n";
      Printf.eprintf "Actual environment (current context): [";
      List.iter (fun (v, ty) -> 
        Printf.eprintf "%s:%s; " (Ident.name v) (string_of_chirality ty)
      ) gamma;
      Printf.eprintf "]\n";
      Printf.eprintf "=============================================\n\n";
      raise (TypeError ("Jump: environment mismatch for label " ^ Label.to_string l))
    end
  
  | Return (x, k) ->
    (* Rule [RETURN]: Γ(x) = prd τ    Γ(k) = cns τ
                      ----------------------------
                      Γ ⊢ return x to k *)
    let x_ty = Env.lookup_exn x gamma in
    let k_ty = Env.lookup_exn k gamma in
    (match (x_ty, k_ty) with
    | (Types.Prd tx, Types.Cns tk) ->
      if not (Types.Type.equivalent sigs tx tk) then
        raise (TypeError (Printf.sprintf "Return: type mismatch - x has type prd %s but k expects cns %s"
          (string_of_typ tx) (string_of_typ tk)))
    | (Types.Prd _, _) ->
      raise (TypeError ("Return: second argument must be a consumer, got " ^ string_of_chirality k_ty))
    | _ ->
      raise (TypeError ("Return: first argument must be a producer, got " ^ string_of_chirality x_ty)))

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
      | None -> raise (TypeError ("Extern symbol not found: " ^ Symbol.to_string m))
    in
    if List.length vars <> List.length input_types then
      raise (TypeError ("Extern: wrong number of arguments for " ^ Symbol.to_string m));
    List.iter2 (fun v ty ->
      let v_ty = Env.lookup_exn v gamma in
      if not (Types.equivalent_chirality sigs v_ty ty) then
        raise (TypeError ("Extern: argument type mismatch for " ^ Ident.name v))
    ) vars input_types;
    if List.length branches <> List.length output_clauses then
      raise (TypeError ("Extern: wrong number of branches for " ^ Symbol.to_string m));
    List.iter2 (fun (gamma_i, s_i) clause_gamma ->
      if not (Env.equal sigs gamma_i clause_gamma) then
        raise (TypeError "Extern: branch environment mismatch");
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
      | None -> raise (TypeError ("Method not found in any signature: " ^ Symbol.to_string m))
    in
    let msig = Signatures.find_method_exn m sig_def in
    
    (* Check type arguments match expected arity.
       In the unified environment syntax, signatures don't bind type variables -
       each method quantifies all type variables it needs, so θ = [β̄ ↦ σ̄] *)
    let expected_arity = List.length msig.Types.quantified in
    if List.length type_args <> expected_arity then
      raise (TypeError (Printf.sprintf "Let: wrong number of type arguments for %s (expected %d, got %d)"
        (Symbol.to_string m) expected_arity (List.length type_args)));
    
    (* Build type substitution θ = [β̄ ↦ σ̄] (method quantifiers only) *)
    let method_quants = List.map fst msig.Types.quantified in
    let subst = List.combine method_quants type_args in
    
    (* Apply substitution to environment types *)
    let expected_types = List.map (fun (_name, chi_ty) ->
      Types.substitute_chirality subst chi_ty
    ) msig.Types.environment in
    
    (* Check that gamma0 types match expected types by position *)
    if List.length gamma0 <> List.length expected_types then
      raise (TypeError (Printf.sprintf "Let: wrong number of producer arguments for %s (expected %d, got %d)"
        (Symbol.to_string m) (List.length expected_types) (List.length gamma0)));
    
    List.iter2 (fun (_var, actual_ty) expected_ty ->
      if not (Types.equivalent_chirality sigs actual_ty expected_ty) then
        raise (TypeError ("Let: producer argument type mismatch for " ^ Symbol.to_string m))
    ) gamma0 expected_types;
    
    (* Split environment: Γ, Γ₀ *)
    let (gamma0_actual, gamma_rest) = Env.split_at (List.length gamma0) gamma in
    if not (Env.equal sigs gamma0 gamma0_actual) then begin
      Printf.eprintf "DEBUG Let environment split mismatch:\n";
      Printf.eprintf "  Checking equality for %d pairs\n" (List.length gamma0);
      List.iter2 (fun (v1, ty1) (v2, ty2) ->
        Printf.eprintf "    %s vs %s: ID equal=%b, Type equal=%b\n"
          (Ident.name v1) (Ident.name v2)
          (Ident.equal v1 v2)
          (Types.equivalent_chirality sigs ty1 ty2)
      ) gamma0 gamma0_actual;
      raise (TypeError "Let: environment split mismatch")
    end;
    
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
          | _ -> raise (TypeError "New: expected signature type")
        in
        decompose ty_whnf
      | _ -> raise (TypeError "New: expected signature type")
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
      raise (TypeError ("New: wrong number of branches for " ^ Path.name sig_sym));
    
    (* Split environment: Γ, Γ₀ *)
    let (gamma0_actual, gamma_rest) = Env.split_at (List.length gamma0) gamma in
    if not (Env.equal sigs gamma0 gamma0_actual) then
      raise (TypeError "New: environment split mismatch");
    
    (* Check each branch *)
    List.iter2 (fun (m_i, branch_type_args, branch_gamma, s_i) msig ->
      if not (Path.equal m_i msig.Types.symbol) then
        raise (TypeError ("New: branch method mismatch"));
      
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
        raise (TypeError (Printf.sprintf "New: wrong number of arguments in branch for %s (expected %d, got %d)"
          (Symbol.to_string m_i) (List.length expected_types) (List.length branch_gamma)));
      
      List.iter2 (fun (_var, actual_ty) expected_ty ->
        if not (Types.equivalent_chirality sigs actual_ty expected_ty) then
          raise (TypeError ("New: branch argument type mismatch for " ^ Symbol.to_string m_i))
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
            | _ -> raise (TypeError "Switch: expected signature type")
          in
          decompose ty_whnf
        | _ -> raise (TypeError "Switch: expected signature type")
      in
      
      let sig_def = match sig_def_opt with
        | Some sd -> sd
        | None ->
          let (sd, _sig_kind) = Signatures.lookup_exn sig_sym sigs in
          sd
      in
      
      if List.length branches <> List.length sig_def.Types.methods then
        raise (TypeError ("Switch: wrong number of branches for " ^ Path.name sig_sym));
      
      (* Check each branch *)
      List.iter2 (fun (m_i, branch_type_args, branch_gamma, s_i) msig ->
        if not (Path.equal m_i msig.Types.symbol) then
          raise (TypeError ("Switch: branch method mismatch"));
        
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
          raise (TypeError (Printf.sprintf "Switch: wrong number of arguments in branch for %s (expected %d, got %d)"
            (Symbol.to_string m_i) (List.length expected_types) (List.length branch_gamma)));
        
        List.iter2 (fun (_var, actual_ty) expected_ty ->
          if not (Types.equivalent_chirality sigs actual_ty expected_ty) then
            raise (TypeError ("Switch: branch argument type mismatch for " ^ Symbol.to_string m_i))
        ) branch_gamma expected_types;
        
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
            | _ -> raise (TypeError "Invoke: expected signature type")
          in
          decompose ty_whnf
        | _ -> raise (TypeError "Invoke: expected signature type")
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
        | None -> raise (TypeError ("Invoke: variable " ^ Ident.name arg ^ " not in environment"))
      ) args in
      
      (* Check that actual types match expected types by position *)
      if List.length actual_types <> List.length expected_types then
        raise (TypeError (Printf.sprintf "Invoke: wrong number of arguments for %s (expected %d, got %d)"
          (Symbol.to_string m) (List.length expected_types) (List.length actual_types)));
      
      List.iter2 (fun actual_ty expected_ty ->
        if not (Types.equivalent_chirality sigs actual_ty expected_ty) then
          raise (TypeError ("Invoke: argument type mismatch for " ^ Symbol.to_string m))
      ) actual_types expected_types
    | (v', _) :: _ when Ident.equal v v' ->
      raise (TypeError ("Invoke: variable " ^ Ident.name v ^ " is not a consumer"))
    | _ ->
      raise (TypeError ("Invoke: variable " ^ Ident.name v ^ " not at front of environment")))

  | LetCns (v, m, type_args, gamma0, s') ->
    (* Rule [LETCNS]: LetCns binds a consumer (dual of Let)
       Similar to Let but result is cns τᵣ *)
    let (sig_def, _sig_kind) = 
      match List.find_opt (fun (_sym, (sig_def, _)) ->
        Signatures.find_method m sig_def <> None
      ) sigs with
      | Some (_, sk) -> sk
      | None -> raise (TypeError ("Method not found in any signature: " ^ Symbol.to_string m))
    in
    let msig = Signatures.find_method_exn m sig_def in
    
    let expected_arity = List.length msig.Types.quantified in
    if List.length type_args <> expected_arity then
      raise (TypeError (Printf.sprintf "LetCns: wrong number of type arguments for %s"
        (Symbol.to_string m)));
    
    let method_quants = List.map fst msig.Types.quantified in
    let subst = List.combine method_quants type_args in
    
    let expected_types = List.map (fun (_name, chi_ty) ->
      Types.substitute_chirality subst chi_ty
    ) msig.Types.environment in
    
    if List.length gamma0 <> List.length expected_types then
      raise (TypeError (Printf.sprintf "LetCns: wrong number of arguments for %s"
        (Symbol.to_string m)));
    
    List.iter2 (fun (_var, actual_ty) expected_ty ->
      if not (Types.equivalent_chirality sigs actual_ty expected_ty) then
        raise (TypeError ("LetCns: argument type mismatch for " ^ Symbol.to_string m))
    ) gamma0 expected_types;
    
    let (gamma0_actual, gamma_rest) = Env.split_at (List.length gamma0) gamma in
    if not (Env.equal sigs gamma0 gamma0_actual) then
      raise (TypeError "LetCns: environment split mismatch");
    
    let v_ty = Types.substitute_chirality subst msig.Types.result_type in
    let new_gamma = (v, v_ty) :: gamma_rest in
    check_statement sigs delta theta extern_env new_gamma s'

  | NewPrd (v, ty, gamma0, branches, s') ->
    (* Rule [NEWPRD]: NewPrd binds a producer (dual of New)
       Similar to New but result is prd (T[τ̄]) *)
    let _, ty_whnf = Types.Type.whnf [] sigs ty in
    let (sig_sym, sig_def_opt) = match ty_whnf with
      | Types.TyDef sig_def -> (sig_def.Types.symbol, Some sig_def)
      | Types.TySym sym -> (sym, None)
      | Types.TyApp _ ->
        let rec decompose = function
          | Types.TyApp (t1, _t2) -> decompose t1
          | Types.TySym sym -> (sym, None)
          | Types.TyDef sig_def -> (sig_def.Types.symbol, Some sig_def)
          | _ -> raise (TypeError "NewPrd: expected signature type")
        in
        decompose ty_whnf
      | _ -> raise (TypeError "NewPrd: expected signature type")
    in
    
    let sig_def = match sig_def_opt with
      | Some sd -> sd
      | None ->
        let (sd, _sig_kind) = Signatures.lookup_exn sig_sym sigs in
        sd
    in
    
    if List.length branches <> List.length sig_def.Types.methods then
      raise (TypeError ("NewPrd: wrong number of branches for " ^ Path.name sig_sym));
    
    let (gamma0_actual, gamma_rest) = Env.split_at (List.length gamma0) gamma in
    if not (Env.equal sigs gamma0 gamma0_actual) then
      raise (TypeError "NewPrd: environment split mismatch");
    
    List.iter2 (fun (m_i, branch_type_args, branch_gamma, s_i) msig ->
      if not (Path.equal m_i msig.Types.symbol) then
        raise (TypeError ("NewPrd: branch method mismatch"));
      
      let method_quants = List.map fst msig.Types.quantified in
      let subst = List.combine method_quants branch_type_args in
      
      let expected_types = 
        List.map (fun (_name, chi_ty) -> Types.substitute_chirality subst chi_ty) 
          msig.Types.environment
      in
      
      if List.length branch_gamma <> List.length expected_types then
        raise (TypeError (Printf.sprintf "NewPrd: wrong number of arguments in branch for %s"
          (Symbol.to_string m_i)));
      
      List.iter2 (fun (_var, actual_ty) expected_ty ->
        if not (Types.equivalent_chirality sigs actual_ty expected_ty) then
          raise (TypeError ("NewPrd: branch argument type mismatch for " ^ Symbol.to_string m_i))
      ) branch_gamma expected_types;
      
      let branch_env = branch_gamma @ gamma0 in
      check_statement sigs delta theta extern_env branch_env s_i
    ) branches sig_def.Types.methods;
    
    let v_ty = Types.Prd ty in
    let new_gamma = (v, v_ty) :: gamma_rest in
    check_statement sigs delta theta extern_env new_gamma s'

  | SwitchCns (v, branches) ->
    (* Rule [SWITCHCNS]: Pattern matching on a consumer (dual of Switch)
       Similar to Switch but v : cns (T[τ̄]) *)
    (match gamma with
    | (v', Types.Cns ty) :: gamma_rest when Ident.equal v v' ->
      let _, ty_whnf = Types.Type.whnf [] sigs ty in
      let (sig_sym, sig_def_opt) = match ty_whnf with
        | Types.TyDef sig_def -> (sig_def.Types.symbol, Some sig_def)
        | Types.TySym sym -> (sym, None)
        | Types.TyApp _ ->
          let rec decompose = function
            | Types.TyApp (t1, _t2) -> decompose t1
            | Types.TySym sym -> (sym, None)
            | Types.TyDef sig_def -> (sig_def.Types.symbol, Some sig_def)
            | _ -> raise (TypeError "SwitchCns: expected signature type")
          in
          decompose ty_whnf
        | _ -> raise (TypeError "SwitchCns: expected signature type")
      in
      
      let sig_def = match sig_def_opt with
        | Some sd -> sd
        | None ->
          let (sd, _sig_kind) = Signatures.lookup_exn sig_sym sigs in
          sd
      in
      
      if List.length branches <> List.length sig_def.Types.methods then
        raise (TypeError ("SwitchCns: wrong number of branches for " ^ Path.name sig_sym));
      
      List.iter2 (fun (m_i, branch_type_args, branch_gamma, s_i) msig ->
        if not (Path.equal m_i msig.Types.symbol) then
          raise (TypeError ("SwitchCns: branch method mismatch"));
        
        let method_quants = List.map fst msig.Types.quantified in
        let subst = List.combine method_quants branch_type_args in
        
        let expected_types = 
          List.map (fun (_name, chi_ty) -> Types.substitute_chirality subst chi_ty)
            msig.Types.environment
        in
        
        if List.length branch_gamma <> List.length expected_types then
          raise (TypeError (Printf.sprintf "SwitchCns: wrong number of arguments in branch for %s"
            (Symbol.to_string m_i)));
        
        List.iter2 (fun (_var, actual_ty) expected_ty ->
          if not (Types.equivalent_chirality sigs actual_ty expected_ty) then
            raise (TypeError ("SwitchCns: branch argument type mismatch for " ^ Symbol.to_string m_i))
        ) branch_gamma expected_types;
        
        let branch_env = branch_gamma @ gamma_rest in
        check_statement sigs delta theta extern_env branch_env s_i
      ) branches sig_def.Types.methods
    | (v', _) :: _ when Ident.equal v v' ->
      raise (TypeError ("SwitchCns: variable " ^ Ident.name v ^ " is not a consumer"))
    | _ ->
      raise (TypeError ("SwitchCns: variable " ^ Ident.name v ^ " not at front of environment")))

  | InvokePrd (v, m, type_args, args) ->
    (* Rule [INVOKEPRD]: Invoking a method on a producer (dual of Invoke)
       Similar to Invoke but v : prd (T[τ̄]) *)
    (match gamma with
    | (v', Types.Prd ty) :: gamma_rest when Ident.equal v v' ->
      let _, ty_whnf = Types.Type.whnf [] sigs ty in
      let (sig_sym, sig_def_opt) = match ty_whnf with
        | Types.TyDef sig_def -> (sig_def.Types.symbol, Some sig_def)
        | Types.TySym sym -> (sym, None)
        | Types.TyApp _ ->
          let rec decompose = function
            | Types.TyApp (t1, _t2) -> decompose t1
            | Types.TySym sym -> (sym, None)
            | Types.TyDef sig_def -> (sig_def.Types.symbol, Some sig_def)
            | _ -> raise (TypeError "InvokePrd: expected signature type")
          in
          decompose ty_whnf
        | _ -> raise (TypeError "InvokePrd: expected signature type")
      in
      
      let sig_def = match sig_def_opt with
        | Some sd -> sd
        | None ->
          let (sd, _sig_kind) = Signatures.lookup_exn sig_sym sigs in
          sd
      in
      let msig = Signatures.find_method_exn m sig_def in
      
      let method_quants = List.map fst msig.Types.quantified in
      let subst = List.combine method_quants type_args in
      
      let expected_types = 
        List.map (fun (_name, chi_ty) -> Types.substitute_chirality subst chi_ty)
          msig.Types.environment
      in
      
      let actual_types = List.map (fun arg ->
        match Env.lookup arg gamma_rest with
        | Some typ -> typ
        | None -> raise (TypeError ("InvokePrd: variable " ^ Ident.name arg ^ " not in environment"))
      ) args in
      
      if List.length actual_types <> List.length expected_types then
        raise (TypeError (Printf.sprintf "InvokePrd: wrong number of arguments for %s"
          (Symbol.to_string m)));
      
      List.iter2 (fun actual_ty expected_ty ->
        if not (Types.equivalent_chirality sigs actual_ty expected_ty) then
          raise (TypeError ("InvokePrd: argument type mismatch for " ^ Symbol.to_string m))
      ) actual_types expected_types
    | (v', _) :: _ when Ident.equal v v' ->
      raise (TypeError ("InvokePrd: variable " ^ Ident.name v ^ " is not a producer"))
    | _ ->
      raise (TypeError ("InvokePrd: variable " ^ Ident.name v ^ " not at front of environment")))


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
      | None -> raise (TypeError ("Label not in environment: " ^ Label.to_string l))
    in
    if not (Env.equal sigs gamma expected_gamma) then
      raise (TypeError ("Program: environment mismatch for label " ^ Label.to_string l));
    (* Check the statement in empty type variable context *)
    check_statement sigs delta theta extern_env gamma s
  ) prog
