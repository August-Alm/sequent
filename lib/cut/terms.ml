(**
  Module: Cut.Terms
  Description: Term syntax of the intermediate language Cut.
  
  This module defines the abstract syntax of the
  intermediate language Cut.
*)

open Common.Identifiers

type symbol = Path.t

type variable = Ident.t 

type label = MkLabel of Path.t

type typ =
  | Prd of symbol
  | Cns of symbol
  | Ext of symbol

(* type environment Γ ::= v : τ, ... *)
type typ_env = (variable * typ) list

(* label environment Θ ::= l : Γ, ... *)
type label_env = (label * typ_env) list

(* m(Γ) *)
type pattern = symbol * typ_env

(* signatures Σ ::= signature T = {m(Γ), ...}, ... *)
type signatures = (symbol * (pattern list)) list

(* [v → v', ...] *)
type substitutions = (variable * variable) list

type statement =
  (* jump l *)
  | Jump of label
  (* substitute [v → v', ...]; s *)
  | Substitute of substitutions * statement
  (* extern m(v, ...){(Γ) ⇒ s, ...} *)
  | Extern of symbol * variable list * extern_branches
  (* let v = m(Γ); s *)
  | Let of variable * symbol * typ_env * statement
  (* new v = (Γ)b; s  -- but with symbol for type annotation *)
  | New of variable * symbol * typ_env * branches * statement
  (* switch v b *)
  | Switch of variable * branches
  (* invoke v m(Γ) *)
  | Invoke of variable * symbol * variable list

(* branches b ::= {m(Γ) ⇒ s, ...} *)
and branches = (symbol * typ_env * statement) list

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

let string_of_typ = function
  | Prd s -> "prd " ^ Path.name s
  | Cns s -> "cns " ^ Path.name s
  | Ext s -> "ext " ^ Path.name s

let string_of_var_typ (v, ty) =
  Ident.name v ^ " : " ^ string_of_typ ty

let string_of_typ_env gamma =
  String.concat ", " (List.map string_of_var_typ gamma)

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
  
  | Let (v, m, gamma, s') ->
    ind ^ "let " ^ Ident.name v ^ " = " ^ Symbol.to_string m ^
    "(" ^ string_of_typ_env gamma ^ ");\n" ^
    string_of_statement ~indent s'
  
  | New (v, ty_sym, gamma, branches, s') ->
    ind ^ "new " ^ Ident.name v ^ " : " ^ Symbol.to_string ty_sym ^
    "(" ^ string_of_typ_env gamma ^ ") {\n" ^
    string_of_branches ~indent:(indent + 1) branches ^ "\n" ^
    ind ^ "};\n" ^
    string_of_statement ~indent s'
  
  | Switch (v, branches) ->
    ind ^ "switch " ^ Ident.name v ^ " {\n" ^
    string_of_branches ~indent:(indent + 1) branches ^ "\n" ^
    ind ^ "}"
  
  | Invoke (v, m, args) ->
    let arg_str = if args = [] then "" else "(" ^ String.concat ", " (List.map Ident.name args) ^ ")" in
    ind ^ "invoke " ^ Ident.name v ^ " " ^ Symbol.to_string m ^ arg_str

and string_of_branches ?(indent=0) branches =
  let ind = String.make (indent * 2) ' ' in
  String.concat "\n" (List.map (fun (m, gamma, s) ->
    ind ^ Symbol.to_string m ^ "(" ^ string_of_typ_env gamma ^ ") ⇒\n" ^
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
type extern_interface = typ list * (typ_env list)

(* External environment: maps extern symbols to their interfaces *)
type extern_env = (symbol * extern_interface) list

module Env = struct
  (** Look up a variable in the type environment *)
  let rec lookup (v: variable) (gamma: typ_env) : typ option =
    match gamma with
    | [] -> None
    | (v', ty) :: rest ->
      if Ident.equal v v' then Some ty
      else lookup v rest

  (** Look up a variable, raising an error if not found *)
  let lookup_exn (v: variable) (gamma: typ_env) : typ =
    match lookup v gamma with
    | Some ty -> ty
    | None -> raise (TypeError ("Variable not in environment: " ^ Ident.name v))

  (** Check if two type environments are equal *)
  let equal (gamma1: typ_env) (gamma2: typ_env) : bool =
    List.length gamma1 = List.length gamma2 &&
    List.for_all2 (fun (v1, ty1) (v2, ty2) ->
      Ident.equal v1 v2 && ty1 = ty2
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

module Signatures = struct
  (** Look up a signature by type symbol *)
  let rec lookup (ty_sym: symbol) (sigs: signatures) : pattern list option =
    match sigs with
    | [] -> None
    | (ty_sym', patterns) :: rest ->
      if Path.equal ty_sym ty_sym' then Some patterns
      else lookup ty_sym rest

  (** Look up a signature, raising an error if not found *)
  let lookup_exn (ty_sym: symbol) (sigs: signatures) : pattern list =
    match lookup ty_sym sigs with
    | Some patterns -> patterns
    | None -> raise (TypeError ("Signature not found for type: " ^ Symbol.to_string ty_sym))

  (** Find the pattern for a specific constructor/destructor symbol *)
  let find_pattern (m: symbol) (patterns: pattern list) : typ_env option =
    List.find_map (fun (m', gamma) -> 
      if Path.equal m m' then Some gamma else None
    ) patterns

  (** Find pattern, raising an error if not found *)
  let find_pattern_exn (m: symbol) (patterns: pattern list) : typ_env =
    match find_pattern m patterns with
    | Some gamma -> gamma
    | None -> raise (TypeError ("Constructor/destructor not found: " ^ Symbol.to_string m))
end

(** Check a statement against a type environment
    Rule: Σ; Θ; Γ ⊢ s
*)
let rec check_statement 
    (sigs: signatures) 
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
    (* Rule [SUBSTITUTE]: v′1 : τ1, ... ⊢ s      Γ(v1) = τ1
                          ---------------------------------
                          Γ ⊢ substitute [v′1 → v1, ...]; s *)
    (* Build new environment from substitution pairs *)
    let gamma' = List.map (fun (v_new, v_old) ->
      let ty = Env.lookup_exn v_old gamma in
      (v_new, ty)
    ) pairs in
    check_statement sigs theta extern_env gamma' s'

  | Extern (m, vars, branches) ->
    (* Rule [EXTERN]: v1 : τ_1, ... ⊢ m: (Γ1), ...   Γ(v1) = τ1 ...     Γ, Γ1 ⊢ s1  ...
                      ------------------------------------------------------------------
                      Γ ⊢ extern m(v1, ...){(Γ1) ⇒ s1, ... } *)
    (* Look up the extern interface *)
    let (input_types, output_clauses) = 
      match List.assoc_opt m extern_env with
      | Some iface -> iface
      | None -> raise (TypeError ("Extern symbol not found: " ^ Symbol.to_string m))
    in
    (* Check that input variables have the correct types *)
    if List.length vars <> List.length input_types then
      raise (TypeError ("Extern: wrong number of arguments for " ^ Symbol.to_string m));
    List.iter2 (fun v ty ->
      let v_ty = Env.lookup_exn v gamma in
      if v_ty <> ty then
        raise (TypeError ("Extern: argument type mismatch for " ^ Ident.name v))
    ) vars input_types;
    (* Check that we have the right number of branches *)
    if List.length branches <> List.length output_clauses then
      raise (TypeError ("Extern: wrong number of branches for " ^ Symbol.to_string m));
    (* Check each branch *)
    List.iter2 (fun (gamma_i, s_i) clause_gamma ->
      (* Check that branch environment matches clause signature *)
      if not (Env.equal gamma_i clause_gamma) then
        raise (TypeError "Extern: branch environment mismatch");
      (* Check the statement with Γ, Γi *)
      let extended_gamma = gamma_i @ gamma in
      check_statement sigs theta extern_env extended_gamma s_i
    ) branches output_clauses

  | Let (v, m, gamma0, s') ->
    (* Rule [LET]: Σ(T) = {..., m(Γ0), ... }      Γ, v : prd T ⊢ s
                   ------------------------------------------------
                   Γ, Γ0 ⊢ let v = m(Γ0); s *)
    (* Find which type T the constructor m belongs to *)
    let ty_sym = 
      match List.find_opt (fun (_ty_sym, patterns) ->
        Signatures.find_pattern m patterns <> None
      ) sigs with
      | Some (ty_sym, _) -> ty_sym
      | None -> raise (TypeError ("Constructor not found in any signature: " ^ Symbol.to_string m))
    in
    let patterns = Signatures.lookup_exn ty_sym sigs in
    let expected_gamma0 = Signatures.find_pattern_exn m patterns in
    (* Check that gamma0 matches the constructor signature *)
    if not (Env.equal gamma0 expected_gamma0) then
      raise (TypeError ("Let: constructor argument environment mismatch for " ^ Symbol.to_string m));
    (* Split current environment: Γ, Γ0 where Γ0 is at head (rightmost in text) *)
    let (gamma0_actual, gamma_rest) = Env.split_at (List.length gamma0) gamma in
    if not (Env.equal gamma0 gamma0_actual) then
      raise (TypeError "Let: environment split mismatch");
    (* Check continuation with Γ, v : prd T where v goes at head *)
    let new_gamma = (v, Prd ty_sym) :: gamma_rest in
    check_statement sigs theta extern_env new_gamma s'

  | New (v, ty_sym, gamma0, branches, s') ->
    (* Rule [NEW]: Σ(T) = {m1(Γ1), ...}    Γ, v : cns T ⊢ s     Γ1, Γ0 ⊢ s1    ...
                   ----------------------------------------------------------------
                   Γ, Γ0 ⊢ new v = (Γ0){m1(Γ1) ⇒ s1, ... }; s *)
    let patterns = Signatures.lookup_exn ty_sym sigs in
    (* Split current environment: Γ, Γ0 where Γ0 is at head *)
    let (gamma0_actual, gamma_rest) = Env.split_at (List.length gamma0) gamma in
    if not (Env.equal gamma0 gamma0_actual) then
      raise (TypeError "New: environment split mismatch");
    (* Check that we have the right branches *)
    if List.length branches <> List.length patterns then
      raise (TypeError ("New: wrong number of branches for type " ^ Symbol.to_string ty_sym));
    (* Check each branch *)
    List.iter2 (fun (m_i, gamma_i, s_i) (m_expected, gamma_i_expected) ->
      if not (Path.equal m_i m_expected) then
        raise (TypeError ("New: branch symbol mismatch, expected " ^ Symbol.to_string m_expected));
      if not (Env.equal gamma_i gamma_i_expected) then
        raise (TypeError ("New: branch environment mismatch for " ^ Symbol.to_string m_i));
      (* Check statement with Γ1, Γ0 where Γ1 is at head *)
      let branch_env = gamma_i @ gamma0 in
      check_statement sigs theta extern_env branch_env s_i
    ) branches patterns;
    (* Check continuation with Γ, v : cns T where v goes at head *)
    let new_gamma = (v, Cns ty_sym) :: gamma_rest in
    check_statement sigs theta extern_env new_gamma s'

  | Switch (v, branches) ->
    (* Rule [SWITCH]: Σ(T) = {m1(Γ1), ...}      Γ, Γ1 ⊢ s1   ...
                      -------------------------------------------
                      Γ, v : prd T ⊢ switch v {m1(Γ1) ⇒ s1, ... } *)
    (* Check that v is at front of environment and is a producer *)
    (match gamma with
    | (v', Prd ty_sym) :: gamma_rest when Ident.equal v v' ->
      let patterns = Signatures.lookup_exn ty_sym sigs in
      (* Check that we have the right branches *)
      if List.length branches <> List.length patterns then
        raise (TypeError ("Switch: wrong number of branches for type " ^ Symbol.to_string ty_sym));
      (* Check each branch *)
      List.iter2 (fun (m_i, gamma_i, s_i) (m_expected, gamma_i_expected) ->
        if not (Path.equal m_i m_expected) then
          raise (TypeError ("Switch: branch symbol mismatch, expected " ^ Symbol.to_string m_expected));
        if not (Env.equal gamma_i gamma_i_expected) then
          raise (TypeError ("Switch: branch environment mismatch for " ^ Symbol.to_string m_i));
        (* Check statement with Γ, Γ1 *)
        let branch_env = gamma_i @ gamma_rest in
        check_statement sigs theta extern_env branch_env s_i
      ) branches patterns
    | (v', _) :: _ when Ident.equal v v' ->
      raise (TypeError ("Switch: variable " ^ Ident.name v ^ " is not a producer"))
    | _ ->
      raise (TypeError ("Switch: variable " ^ Ident.name v ^ " not at front of environment")))

  | Invoke (v, m, args) ->
    (* Rule [INVOKE]: Σ(T) = {..., m(Γ), ...}
                      -------------------------
                      Γ, v : cns T ⊢ invoke v m(Γ) *)
    (* Check that v is at front of environment and is a consumer *)
    (match gamma with
    | (v', Cns ty_sym) :: gamma_rest when Ident.equal v v' ->
      let patterns = Signatures.lookup_exn ty_sym sigs in
      let expected_gamma = Signatures.find_pattern_exn m patterns in
      (* Build actual gamma from args *)
      let actual_gamma = List.map (fun arg ->
        match List.assoc_opt arg gamma_rest with
        | Some typ -> (arg, typ)
        | None -> raise (TypeError ("Invoke: variable " ^ Ident.name arg ^ " not in environment"))
      ) args in
      (* Check that actual environment matches m's signature *)
      if not (Env.equal actual_gamma expected_gamma) then
        raise (TypeError ("Invoke: environment mismatch for method " ^ Symbol.to_string m))
    | (v', _) :: _ when Ident.equal v v' ->
      raise (TypeError ("Invoke: variable " ^ Ident.name v ^ " is not a consumer"))
    | _ ->
      raise (TypeError ("Invoke: variable " ^ Ident.name v ^ " not at front of environment")))

(** Check a program
    Rule [PROGRAM]: Θ(l) = Γ    Σ; Θ; Γ ⊢ s    ...
                    ------------------------------
                    Σ Θ ⊢ define l : Γ = s, ...
*)
let check_program 
    (sigs: signatures) 
    (extern_env: extern_env)
    (prog: program) : unit =
  (* Build label environment from program *)
  let theta = List.map (fun (l, gamma, _) -> (l, gamma)) prog in
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
    (* Check the statement *)
    check_statement sigs theta extern_env gamma s
  ) prog
