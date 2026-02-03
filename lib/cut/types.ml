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
  | TySig of signature              (* signature type *)
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
    (* Type parameters with their kinds, e.g., [(a, KStar)] for List a *)
  ; parameters: (Ident.t * kind) list
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
  ; constraints: (Ident.t * typ) list
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

(** Primitive types *)
module Prim = struct
  let int_sym = Common.Types.Prim.int_sym
  let int_typ = TyPrim (int_sym, KStar)
  
  (** Utility: check if a type is a primitive *)
  let is_primitive (sym: Path.t) : bool =
    Path.equal sym int_sym
end

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
  (** Get the kind of a signature *)
  let signature_kind (sig_def: signature) : kind =
    List.fold_right (fun (_, k) acc -> KArrow (k, acc)) 
      sig_def.parameters KStar
  
  (** Substitute type variables in a type *)
  let rec substitute (subst: (Ident.t * typ) list) (ty: typ) : typ =
    match ty with
    | TyVar x ->
      (match List.assoc_opt x subst with
       | Some ty' -> ty'
       | None -> ty)
    | TyApp (t1, t2) ->
      TyApp (substitute subst t1, substitute subst t2)
    | TySig sig_def ->
      (* Don't substitute inside signatures - they are closed *)
      TySig sig_def
    | TyPrim _ -> ty
  
  (** Apply a type constructor to an argument *)
  let apply (t1: typ) (t2: typ) : typ =
    TyApp (t1, t2)
  
  (** Get free type variables in a type *)
  let rec free_vars (ty: typ) : Ident.t list =
    match ty with
    | TyVar x -> [x]
    | TyApp (t1, t2) -> free_vars t1 @ free_vars t2
    | TySig _ -> []
    | TyPrim _ -> []
  
  (** Convert chirality type to underlying type *)
  let of_chirality = function
    | Prd ty | Cns ty | Ext ty -> ty
  
  (** Check if two types are equal (structural equality) *)
  let rec equal (t1: typ) (t2: typ) : bool =
    let result = match t1, t2 with
    | TyVar x, TyVar y -> Ident.equal x y
    | TyApp (a, b), TyApp (c, d) -> equal a c && equal b d
    | TySig s1, TySig s2 -> Path.equal s1.symbol s2.symbol
    | TyPrim (p1, _), TyPrim (p2, _) -> Path.equal p1 p2
    | _ -> false
    in
    if not result then begin
      Printf.fprintf stderr "  Type mismatch: t1=%s, t2=%s\n%!"
        (match t1 with
         | TyVar _ -> "TyVar"
         | TyApp _ -> "TyApp"
         | TySig _ -> "TySig"
         | TyPrim (p, _) -> "TyPrim(" ^ Path.name p ^ ")")
        (match t2 with
         | TyVar _ -> "TyVar"
         | TyApp _ -> "TyApp"
         | TySig _ -> "TySig"
         | TyPrim (p, _) -> "TyPrim(" ^ Path.name p ^ ")")
    end;
    result
end

(** Chirality type operations *)
let substitute_chirality (subst: (Ident.t * typ) list) (chi: chirality_type) : chirality_type =
  match chi with
  | Prd ty -> Prd (Type.substitute subst ty)
  | Cns ty -> Cns (Type.substitute subst ty)
  | Ext ty -> Ext (Type.substitute subst ty)

let equal_chirality (c1: chirality_type) (c2: chirality_type) : bool =
  match c1, c2 with
  | Prd t1, Prd t2 -> Type.equal t1 t2
  | Cns t1, Cns t2 -> Type.equal t1 t2
  | Ext t1, Ext t2 -> Type.equal t1 t2
  | _ -> false

(** Signature utilities *)
module Sig = struct
  (** Look up a signature by symbol *)
  let lookup (sigs: signature_defs) (sym: Path.t) : (signature * kind) option =
    List.assoc_opt sym sigs
  
  let lookup_exn (sigs: signature_defs) (sym: Path.t) : signature * kind =
    match List.assoc_opt sym sigs with
    | Some result -> result
    | None -> failwith ("Signature not found: " ^ Path.name sym)
  
  (** Find a method in a signature *)
  let find_method (sig_def: signature) (method_sym: Path.t) : method_sig option =
    List.find_opt (fun (m: method_sig) -> Path.equal m.symbol method_sym) sig_def.methods
  
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
      List.fold_left Type.apply (TySig sig_def) args
end

(** Pretty printing *)
module Pretty = struct
  let rec typ_to_string ?(nested=false) (ty: typ) : string =
    match ty with
    | TyVar x -> Ident.name x
    | TyApp (t1, t2) ->
      let s = typ_to_string ~nested:true t1 ^ "(" ^ typ_to_string t2 ^ ")" in
      if nested then "(" ^ s ^ ")" else s
    | TySig sig_def -> Path.name sig_def.symbol
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
      if m.constraints = [] then ""
      else " where " ^ String.concat ", " (List.map (fun (x, ty) ->
        Ident.name x ^ " = " ^ typ_to_string ty) m.constraints)
    in
    quant_str ^ Path.name m.symbol ^ " : " ^ env_str ^ 
    " : " ^ chirality_to_string m.result_type ^ constr_str
  
  let signature_to_string (sig_def: signature) : string =
    let params_str =
      if sig_def.parameters = [] then ""
      else "(" ^ String.concat ", " (List.map (fun (x, k) ->
        Ident.name x ^ " : " ^ Kind.to_string k) sig_def.parameters) ^ ")"
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
      (match List.assoc_opt x env with
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
    
    | TySig sig_def ->
      Ok (Type.signature_kind sig_def)
    
    | TyPrim (_, k) -> Ok k
  
  (** Check that a method signature is well-formed *)
  let check_method (sig_def: signature) (m: method_sig) (sigs: signature_defs)
      : (unit, error) result =
    (* Build type environment with signature parameters and method quantified vars *)
    let env = sig_def.parameters @ m.quantified in
    
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

(**
   === Design Notes ===
   
   This type system extends Cut to support the full expressiveness of Core's
   higher-kinded and GADT features while maintaining Cut's data/codata unification.
   
   Key design decisions:
   
   1. **Signatures replace data/codata types**:
      - A signature is a parametric collection of methods
      - No distinction between data and codata at the type level
      - The operational behavior (eager/lazy) is determined by chirality (prd/cns)
   
   2. **Methods unify constructors and destructors**:
      - Each method has producers (what is given) and consumers (what is needed)
      - For data constructors: producers = arguments, consumers = empty
      - For codata destructors: producers = result, consumers = arguments
      - This mirrors Cut.Terms' operational semantics
   
   3. **Higher-kinded types via parametric signatures**:
      - Signatures can have type parameters with arbitrary kinds
      - Example: List has parameter (a : type), so List : type → type
      - Type application TyApp builds fully applied types
   
   4. **Polymorphic methods via quantification**:
      - Methods can quantify over type variables
      - Example: nil : ∀a. List(a) has quantified = [(a, KStar)]
      - Allows representing parametric polymorphism
   
   5. **GADTs via constraints and refined result types**:
      - result_type can be more specific than just applying parent parameters
      - constraints list type equalities that must hold
      - Example: for Vec(n : Nat), cons could have constraints [(n, Succ(m))]
   
   6. **Chirality types carry full type information**:
      - Unlike Cut.Terms' simple prd/cns/ext symbols
      - Prd T, Cns T, Ext T all carry the full type T
      - Enables precise type checking and inference
   
   Translation from Core types:
   
   - Core: data Nat = { Zero | Succ(Nat) }
     Cut.Types: signature Nat = {
                  zero : ∀. () : prd Nat
                  succ : ∀. (n : prd Nat) : prd Nat
                }
   
   - Core: codata Stream(A) = { head : A, tail : Stream(A) }
     Cut.Types: signature Stream(a : type) = {
                  head : ∀. (self : cns Stream(a)) : cns a
                  tail : ∀. (self : cns Stream(a)) : cns Stream(a)
                }
   
   - Core GADT: data Vec(n : Nat) = { 
                  Nil : Vec(Zero) 
                  Cons : ∀m. Vec(m) → Vec(Succ(m)) 
                }
     Cut.Types: signature Vec(n : type) = {
                  nil : ∀. () : prd Vec(Zero) where []
                  cons : ∀m. (v : prd Vec(m)) : prd Vec(Succ(m)) where []
                }
   
   This type system is currently NOT used by Cut.Terms, which uses a simpler
   first-order signature system. This module provides the foundation for a
   future extension of Cut to support full Core expressiveness.
*)
