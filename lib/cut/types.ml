(**
  Module: Cut.Types
  Description: Type system for the Cut intermediate language.
  
  This module defines a higher-kinded, GADT-capable type system for Cut that
  unifies data and codata types into parametric signatures. Unlike the simple
  signature system in Cut.Terms, this type system can represent:
  
  - Higher-kinded types (e.g., List : type -> type)
  - Polymorphic methods (e.g., ∀a. nil : List a)
  - GADTs with type constraints
  - Type-level computation
  
  The key unification: both constructors and destructors become "methods" of
  a signature, each with producer arguments and consumer arguments.
*)

open Common.Identifiers

(** Kinds classify types *)
type kind = 
  | KStar                           (* kind of proper types *)
  | KArrow of kind * kind           (* kind of type constructors *)

(** Types *)
type typ =
  | TyVar of Ident.t                (* type variable *)
  | TyApp of typ * typ              (* type application T(A) *)
  | TySym of Path.t                 (* reference to signature symbol *)
  | TyDef of signature              (* instantiated signature definition *)
  | TyPrim of Path.t * kind         (* primitive external type *)

(** Signatures unify data and codata types
    
    A signature defines a collection of methods that can be invoked.
    For data types, methods correspond to constructors.
    For codata types, methods correspond to destructors.
    
    Cut collapses this duality: a signature is just a parametric collection
    of methods, each with its own type signature.
*)
and signature =
  { symbol: Path.t
    (* Type parameters with their kinds, e.g., [(None, KStar)] for List a.
      Only instantiated parameters are Some's. *)
  ; parameters: (typ option * kind) list
    (* Methods (constructors/destructors) *)
  ; methods: method_sig list
  }

(** Method signatures unify constructors and destructors
    
    Each method has a single environment Γ containing all its arguments with
    polarized types. The polarity (prd/cns/ext) indicates the role:
    - prd: producer argument (eagerly evaluated)
    - cns: consumer argument (lazily evaluated, continuation-like)
    - ext: external argument (opaque platform value)
    
    The result_type is also polarized and determines the method's role:
    - prd T: constructor-like (Let binds, Switch matches)
    - cns T: destructor-like (New binds, Invoke calls)
    
    For GADTs, the result_type can refine the type parameters with constraints.
*)
and method_sig =
  { parent: Path.t
    (* Method name *)
  ; symbol: Path.t
    (* Quantified type variables, e.g., [(a, KStar)] for polymorphic methods *)
  ; quantified: (Ident.t * kind) list
    (* Method environment: all arguments with their polarized types
       Example: [(x, Prd ty1); (k, Cns ty2)] for a method taking producer x and consumer k *)
  ; environment: (Ident.t * chirality_type) list
    (* Result type: polarized type indicating method's role
       - prd T for constructors: Let binds the result, Switch pattern matches
       - cns T for destructors: New binds the consumer, Invoke calls it *)
  ; result_type: chirality_type
    (* Type constraints for GADTs, e.g., (a, TySym Nat) means a must equal Nat *)
  ; constraints: (Ident.t * typ) list option
  }

(** Typed parameter: variable with its chirality type.
    Used in statement environments (typ_env) where variables ARE named. *)
and typed_param = Ident.t * chirality_type

(** Chirality types for Cut's operational semantics
    
    Unlike the simple prd/cns/ext in Cut.Terms, these carry full type information:
    - Prd T: producer of type T (evaluated eagerly, data-like)
    - Cns T: consumer of type T (evaluated lazily, codata-like)  
    - Ext T: external type T (platform-dependent, opaque)
*)
and chirality_type =
  | Prd of typ      (* producer *)
  | Cns of typ      (* consumer *)
  | Ext of typ      (* external *)

(** Signature definitions: global collection of signatures *)
type signature_defs = (Path.t * (signature * kind)) list

(** Type variable environment for type checking *)
type type_env = (Ident.t * kind) list

(** Kind utilities *)
module Kind = struct
  let equal = (=)
  
  let to_string = function
    | KStar -> "type"
    | KArrow (k1, k2) ->
      let rec to_string_prec needs_parens = function
        | KStar -> "type"
        | KArrow (k1, k2) ->
          let s = to_string_prec true k1 ^ " → " ^ to_string_prec false k2 in
          if needs_parens then "(" ^ s ^ ")" else s
      in
      to_string_prec false (KArrow (k1, k2))
  
  (** Get the result kind of a kind (for type application) *)
  let result_kind = function
    | KStar -> failwith "Cannot apply type of kind type"
    | KArrow (_, k) -> k
  
  (** Get the argument kind of a kind (for type application) *)
  let arg_kind = function
    | KStar -> failwith "Cannot apply type of kind type"
    | KArrow (k, _) -> k
end

(** Type utilities *)
module Type = struct
  (** Look up a type variable in a substitution list *)
  let rec lookup_subst (x: Ident.t) (subst: (Ident.t * typ) list) : typ option =
    match subst with
    | [] -> None
    | (y, ty) :: rest ->
      if Ident.equal x y then Some ty
      else lookup_subst x rest
  
  (** Get the kind of a signature from its parameters *)
  let signature_kind (params: (typ option * kind) list) : kind =
    List.fold_right (fun (_, k) acc -> KArrow (k, acc)) 
      params KStar
  
  (** Substitute into a chirality type *)
  let rec substitute_chirality (subst: (Ident.t * typ) list) (chi: chirality_type) : chirality_type =
    match chi with
    | Prd ty -> Prd (substitute subst ty)
    | Cns ty -> Cns (substitute subst ty)
    | Ext ty -> Ext (substitute subst ty)
  
  (** Substitute type variables in a type *)
  and substitute (subst: (Ident.t * typ) list) (ty: typ) : typ =
    match ty with
    | TyVar x ->
      (match lookup_subst x subst with
       | Some ty' -> ty'
       | None -> ty)
    | TyApp (t1, t2) ->
      TyApp (substitute subst t1, substitute subst t2)
    | TySym _ -> ty  (* references don't change *)
    | TyDef sig_def ->
      (* Substitute into instantiated signature parameters and methods *)
      TyDef (substitute_sig subst sig_def)
    | TyPrim _ -> ty
  
  (** Substitute into a signature definition *)
  and substitute_sig (subst: (Ident.t * typ) list) (sig_def: signature) : signature =
    { sig_def with
      parameters = List.map (fun (t_opt, k) ->
        (Option.map (substitute subst) t_opt, k)) sig_def.parameters
    ; methods = List.map (substitute_method subst) sig_def.methods
    }
  
  (** Substitute into a method signature *)
  and substitute_method (subst: (Ident.t * typ) list) (m: method_sig) : method_sig =
    (* Filter out quantified variables to avoid capture *)
    let subst' = List.filter (fun (x, _) ->
      not (List.exists (fun (y, _) -> Ident.equal x y) m.quantified)
    ) subst in
    { m with
      environment = List.map (fun (v, chi) -> (v, substitute_chirality subst' chi)) m.environment
    ; result_type = substitute_chirality subst' m.result_type
    ; constraints = Option.map (List.map (fun (x, ty) -> (x, substitute subst' ty))) m.constraints
    }
  
  (** Substitute using an Ident table (more efficient for complex substitutions) *)
  let rec subst_tbl (env: typ Ident.tbl) (ty: typ) : typ =
    match ty with
    | TyVar x ->
      (match Ident.find_opt x env with
       | Some ty' -> ty'
       | None -> ty)
    | TyApp (t1, t2) ->
      TyApp (subst_tbl env t1, subst_tbl env t2)
    | TySym _ -> ty  (* references don't change *)
    | TyDef sig_def ->
      (* Substitute into instantiated signature parameters and methods *)
      TyDef (subst_tbl_sig env sig_def)
    | TyPrim _ -> ty
  
  and subst_tbl_sig (env: typ Ident.tbl) (sig_def: signature) : signature =
    { sig_def with
      parameters = List.map (fun (t_opt, k) ->
        (Option.map (subst_tbl env) t_opt, k)) sig_def.parameters
    ; methods = List.map (subst_tbl_method env) sig_def.methods
    }
  
  and subst_tbl_method (env: typ Ident.tbl) (m: method_sig) : method_sig =
    (* Filter out quantified variables to avoid capture *)
    let env' = Ident.filter (fun x _ ->
      not (List.exists (fun (y, _) -> Ident.equal x y) m.quantified)
    ) env in
    { m with
      environment = List.map (fun (v, chi) -> (v, subst_tbl_chirality env' chi)) m.environment
    ; result_type = subst_tbl_chirality env' m.result_type
    ; constraints = Option.map (List.map (fun (x, ty) -> (x, subst_tbl env' ty))) m.constraints
    }
  
  and subst_tbl_chirality (env: typ Ident.tbl) (chi: chirality_type) : chirality_type =
    match chi with
    | Prd ty -> Prd (subst_tbl env ty)
    | Cns ty -> Cns (subst_tbl env ty)
    | Ext ty -> Ext (subst_tbl env ty)
  
  (** Apply a type constructor to an argument *)
  let apply (t1: typ) (t2: typ) : typ =
    TyApp (t1, t2)
  
  (** Check if a variable occurs in a type (for occurs check in unification) *)
  let rec occurs (x: Ident.t) (ty: typ) : bool =
    match ty with
    | TyVar y -> Ident.equal x y
    | TyApp (t1, t2) -> occurs x t1 || occurs x t2
    | TySym _ -> false  (* references contain no variables *)
    | TyDef sig_def -> occurs_sig x sig_def  (* check instantiated parameters *)
    | TyPrim _ -> false
  
  and occurs_sig (x: Ident.t) (sig_def: signature) : bool =
    List.exists (fun (t_opt, _) ->
      match t_opt with
      | None -> false
      | Some ty -> occurs x ty
    ) sig_def.parameters
  
  (** Convert chirality type to underlying type *)
  let of_chirality = function
    | Prd ty | Cns ty | Ext ty -> ty
  
  (** Instantiate a signature with one type argument, filtering methods by constraints *)
  let inst1 (_sigs: signature_defs) (sig_def: signature) (arg: typ) : signature =
    match sig_def.parameters with
    | [] -> failwith "Cannot instantiate signature with no parameters"
    | (_, k) :: rest_params ->
      (* Build substitution for the first parameter *)
      let new_params = (Some arg, k) :: rest_params in
      
      (* Filter methods whose constraints are satisfiable with this instantiation *)
      let filter_method (m: method_sig) : bool =
        match m.constraints with
        | None -> true  (* No constraints, always available *)
        | Some constraints ->
          (* Check if all constraints can unify with the instantiation *)
          (* For now, we keep all methods - proper constraint checking comes later *)
          List.for_all (fun (_var, _required_ty) ->
            (* If this constraint mentions the first parameter, check unification *)
            true  (* TODO: implement proper constraint checking *)
          ) constraints
      in
      
      { sig_def with
        parameters = new_params
      ; methods = List.filter filter_method sig_def.methods
      }
  
  (** Weak head normal form - expand type symbols to their definitions and instantiate applications *)
  let rec whnf (seen: Path.t list) (sigs: signature_defs) (ty: typ) : Path.t list * typ =
    let lookup_sig sym =
      let rec go = function
        | [] -> None
        | (s, sig_def) :: rest ->
          if Path.equal s sym then Some sig_def
          else go rest
      in
      go sigs
    in
    match ty with
    | TyApp (f, a) ->
      let seen', f' = whnf seen sigs f in
      (match f' with
      | TySym sym ->
        (* Look up signature and instantiate it *)
        (match lookup_sig sym with
        | Some (sig_def, _) ->
          if List.mem sym seen' then
            (seen', ty)  (* Cycle detected, stop *)
          else
            (sym :: seen', TyDef (inst1 sigs sig_def a))
        | None -> (seen', ty))
      | TyDef sig_def ->
        (* Further instantiation *)
        (seen', TyDef (inst1 sigs sig_def a))
      | _ ->
        if f' == f then (seen', ty)
        else (seen', TyApp (f', a)))
    | TyVar _ -> (seen, ty)
    | TySym sym ->
      (* Expand symbol reference to definition *)
      if List.mem sym seen then
        (seen, ty)  (* Cycle detected, stop *)
      else
        (match lookup_sig sym with
        | Some (sig_def, _) ->
          (sym :: seen, TyDef sig_def)
        | None -> (seen, ty))  (* Unknown symbol, leave as-is *)
    | TyDef _ -> (seen, ty)  (* Already expanded *)
    | TyPrim _ -> (seen, ty)
  
  (** Reduce a type to normal form *)
  let reduce (sigs: signature_defs) (ty: typ) : typ =
    snd (whnf [] sigs ty)
  
  (** Reduce with seen list to prevent infinite loops *)
  let reduce_seen (seen: Path.t list) (sigs: signature_defs) (ty: typ) : typ =
    snd (whnf seen sigs ty)
  
  (** Unification: returns Some substitution if types unify, None otherwise *)
  let rec unify (seen: Path.t list) (sigs: signature_defs) (t1: typ) (t2: typ) 
      : (typ Ident.tbl) option =
    let res = ref None in
    begin
      (match t1, t2 with
      | TyVar x, TyVar y when Ident.equal x y ->
        res := Some Ident.emptytbl
      | TyVar x, t | t, TyVar x ->
        (* Occurs check: don't allow x = ... x ... *)
        if not (occurs x t) then res := Some (Ident.add x t Ident.emptytbl)
      | TyApp (f1, a1), TyApp (f2, a2) ->
        (match unify seen sigs f1 f2 with
        | None -> ()
        | Some sub1 ->
          (match unify seen sigs (subst_tbl sub1 a1) (subst_tbl sub1 a2) with
          | None -> ()
          | Some sub2 -> res := Some (Ident.join sub2 sub1)))
      | TySym s1, TySym s2 when Path.equal s1 s2 ->
        res := Some Ident.emptytbl
      | TyDef s1, TyDef s2 when Path.equal s1.symbol s2.symbol ->
        (* Unify instantiated signatures - they must have same symbol and compatible parameters *)
        (* TODO: also check parameter unification *)
        res := Some Ident.emptytbl
      | TyPrim (p1, _), TyPrim (p2, _) when Path.equal p1 p2 ->
        res := Some Ident.emptytbl
      | _ -> ());
      
      (* If direct unification failed, try reducing both sides *)
      if Option.is_none !res then
        let t1' = reduce_seen seen sigs t1 in
        if not (t1' == t1) then
          res := unify seen sigs t1' t2
        else
          let t2' = reduce_seen seen sigs t2 in
          if not (t2' == t2) then
            res := unify seen sigs t1 t2'
    end;
    !res
  
  (** Check if two types are equivalent (unify with empty substitution) *)
  let equivalent (sigs: signature_defs) (t1: typ) (t2: typ) : bool =
    match unify [] sigs t1 t2 with
    | Some subs -> Ident.is_empty subs
    | None -> false
  
end

(** Chirality type operations *)
let substitute_chirality (subst: (Ident.t * typ) list) (chi: chirality_type) : chirality_type =
  match chi with
  | Prd ty -> Prd (Type.substitute subst ty)
  | Cns ty -> Cns (Type.substitute subst ty)
  | Ext ty -> Ext (Type.substitute subst ty)

let equivalent_chirality sigs (c1: chirality_type) (c2: chirality_type) : bool =
  match c1, c2 with
  | Prd t1, Prd t2 -> Type.equivalent sigs t1 t2
  | Cns t1, Cns t2 -> Type.equivalent sigs t1 t2
  | Ext t1, Ext t2 -> Type.equivalent sigs t1 t2
  | _ -> false

(** Signature utilities *)
module Sig = struct
  (** Look up a signature by symbol *)
  let rec lookup (sigs: signature_defs) (sym: Path.t) : (signature * kind) option =
    match sigs with
    | [] -> None
    | (s, sig_def) :: rest ->
      if Path.equal s sym then Some sig_def
      else lookup rest sym
  
  let lookup_exn (sigs: signature_defs) (sym: Path.t) : signature * kind =
    match lookup sigs sym with
    | Some result -> result
    | None -> failwith ("Signature not found: " ^ Path.name sym)
  
  (** Find a method in a signature *)
  let find_method (sig_def: signature) (method_sym: Path.t) : method_sig option =
    let rec go (methods:  method_sig list)method_sym =
      match methods with
      | [] -> None
      | m :: rest ->
        if Path.equal m.symbol method_sym then Some m
        else go rest method_sym
    in
    go sig_def.methods method_sym
  
  let find_method_exn (sig_def: signature) (method_sym: Path.t) : method_sig =
    match find_method sig_def method_sym with
    | Some m -> m
    | None -> failwith ("Method not found: " ^ Path.name method_sym)
  
  (** Get all method symbols from a signature *)
  let method_symbols (sig_def: signature) : Path.t list =
    List.map (fun (m: method_sig) -> m.symbol) sig_def.methods
  
  (** Instantiate a signature's parameters with concrete types *)
  let instantiate (sig_def: signature) (args: typ list) : typ =
    if List.length args <> List.length sig_def.parameters then
      failwith "Wrong number of type arguments"
    else
      (* Build the fully applied type *)
      List.fold_left Type.apply (TySym sig_def.symbol) args
end

(** Pretty printing *)
module Pretty = struct
  let rec typ_to_string ?(nested=false) (ty: typ) : string =
    match ty with
    | TyVar x -> Ident.name x
    | TyApp (t1, t2) ->
      let s = typ_to_string ~nested:true t1 ^ "(" ^ typ_to_string t2 ^ ")" in
      if nested then "(" ^ s ^ ")" else s
    | TySym sym -> Path.name sym
    | TyDef sig_def -> Path.name sig_def.symbol  (* show symbol of instantiated sig *)
    | TyPrim (sym, _) -> Path.name sym
  
  let chirality_to_string = function
    | Prd ty -> "prd " ^ typ_to_string ~nested:true ty
    | Cns ty -> "cns " ^ typ_to_string ~nested:true ty
    | Ext ty -> "ext " ^ typ_to_string ~nested:true ty
  
  let typed_param_to_string (v, chir) =
    Ident.name v ^ " : " ^ chirality_to_string chir
  
  let method_sig_to_string (m: method_sig) : string =
    let quant_str = 
      if m.quantified = [] then ""
      else "∀" ^ String.concat " " (List.map (fun (x, k) ->
        Ident.name x ^ ":" ^ Kind.to_string k) m.quantified) ^ ". "
    in
    let env_str = 
      if m.environment = [] then "()"
      else "(" ^ String.concat ", " (List.map typed_param_to_string m.environment) ^ ")"
    in
    let constr_str =
      match m.constraints with
      | None -> ""
      | Some constraints ->
        " where [" ^ String.concat ", " (List.map (fun (x, ty) ->
          Ident.name x ^ " = " ^ typ_to_string ty) constraints) ^ "]"
    in
    quant_str ^ Path.name m.symbol ^ " : " ^ env_str ^ 
    " : " ^ chirality_to_string m.result_type ^ constr_str
  
  let signature_to_string (sig_def: signature) : string =
    let params_str =
      if sig_def.parameters = [] then ""
      else "(" ^ String.concat ", " (List.map (fun (x, k) ->
        (match x with None -> "_" | Some a -> typ_to_string a) ^
        " : " ^ Kind.to_string k) sig_def.parameters) ^ ")"
    in
    let methods_str =
      String.concat "\n  " (List.map method_sig_to_string sig_def.methods)
    in
    "signature " ^ Path.name sig_def.symbol ^ params_str ^ " = {\n  " ^
    methods_str ^ "\n}"
end

(** Type checking and inference *)
module TypeCheck = struct
  type error = string
  
  (** Look up a type variable in a type environment *)
  let rec lookup_type_var (x: Ident.t) (env: type_env) : kind option =
    match env with
    | [] -> None
    | (y, k) :: rest ->
      if Ident.equal x y then Some k
      else lookup_type_var x rest
  
  (** Kind checking: ensure a type has the expected kind *)
  let rec check_kind (env: type_env) (sigs: signature_defs) (ty: typ) (expected: kind) 
      : (unit, error) result =
    match infer_kind env sigs ty with
    | Error e -> Error e
    | Ok actual ->
      if Kind.equal actual expected then Ok ()
      else Error (Printf.sprintf "Kind mismatch: expected %s but got %s"
        (Kind.to_string expected) (Kind.to_string actual))
  
  (** Kind inference: infer the kind of a type *)
  and infer_kind (env: type_env) (sigs: signature_defs) (ty: typ) 
      : (kind, error) result =
    match ty with
    | TyVar x ->
      (match lookup_type_var x env with
      | Some k -> Ok k
      | None -> Error ("Unbound type variable: " ^ Ident.name x))
    
    | TyApp (t1, t2) ->
      (match infer_kind env sigs t1 with
      | Error e -> Error e
      | Ok k1 ->
        match k1 with
        | KStar -> Error "Cannot apply type of kind type"
        | KArrow (k_arg, k_res) ->
          (match check_kind env sigs t2 k_arg with
           | Error e -> Error e
           | Ok () -> Ok k_res))
    
    | TySym sym ->
      (* Look up signature kind *)
      (match Sig.lookup sigs sym with
      | Some (_sig_def, k) -> Ok k
      | None -> Error ("Unknown signature: " ^ Path.name sym))
    
    | TyDef sig_def ->
      (* Instantiated signature - compute kind from remaining parameters *)
      Ok (Type.signature_kind sig_def.parameters)
    
    | TyPrim (_, k) -> Ok k
  
  (** Check that a method signature is well-formed *)
  let check_method (_sig_def: signature) (m: method_sig) (sigs: signature_defs)
      : (unit, error) result =
    let env = m.quantified in
    
    (* Check all environment types *)
    let check_environment =
      List.fold_left (fun acc (_, chir) ->
        match acc with
        | Error e -> Error e
        | Ok () ->
          let ty = Type.of_chirality chir in
          check_kind env sigs ty KStar
      ) (Ok ()) m.environment
    in
    
    (* Check result type *)
    match check_environment with
    | Error e -> Error e
    | Ok () ->
      let result_ty = Type.of_chirality m.result_type in
      check_kind env sigs result_ty KStar
  
  (** Check that a signature is well-formed *)
  let check_signature (sig_def: signature) (sigs: signature_defs) 
      : (unit, error) result =
    List.fold_left (fun acc m ->
      match acc with
      | Error e -> Error e
      | Ok () -> check_method sig_def m sigs
    ) (Ok ()) sig_def.methods
end
