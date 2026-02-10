(**
  Module: Kore.Types
  Description: Types for polarized sequent calculus.
  
  This module defines the type-level language of an intermediate representation
  based on a polarized sequent calculus. It includes generalized algebraic data
  and codata types and higher-kinded types.
*)

open Common.Identifiers

(* ========================================================================= *)
(*  Abstract syntax                                                          *)
(* ========================================================================= *)

type polarity = Positive | Negative

(** Kinds of types. Base kinds are polarized into positive and negative.
  External types are considered positive. *)
type kind = Pos | Neg | Ext | Arrow of kind * kind

(** Type symbols, referencing definitions or external (primitive) types*)
type symbol = Path.t

(** Type variables, used in higher kinded types *)
type variable = Ident.t

(** Type expressions *)
type tpe =
  | TyPos of signature (** Positive data definitions *)
  | TyNeg of signature (** Negative data definitions, meaning codata *)
  | TyExt of symbol (** External types have positive polarity *)
  | TySym of symbol (** Symbol reference to (co)data definition *)
  | TyVar of variable (** Type variable *)
  | TyApp of tpe * tpe (** Type application/instantiation *)

(** Chiral types are the types of Kore terms *)
and chiral_tpe =
  | Lhs of tpe (** Left hand side means 'producer' *)
  | Rhs of tpe (** Right hand side means 'consumer' *)

(** Signatures describe the structure of (co)data type definitions *)
and signature =
  { name: symbol
  ; arguments: (tpe option * kind) list
  ; xtors: xtor list
  }

(** Unified notion of constructors and destructors *)
and xtor =
  { parent: symbol
  ; name: symbol
  ; quantified: (variable * kind) list
  ; parameters: chiral_tpe list
  ; parent_arguments: tpe list
  ; constraints: (variable * tpe) list option
  }

(** Environment of defined signatures *)
type signatures = (signature * polarity * kind) Path.tbl

(* ========================================================================= *)
(* Kind inference and checking                                               *)
(* ========================================================================= *)

exception UnboundTypeVariable of variable
exception UnknownTypeSymbol of symbol
exception KindMismatch of tpe * kind * kind
exception ExpectedHigherKind of tpe * kind

let chiral_tpe_map (f: tpe -> tpe) (ct: chiral_tpe) =
  match ct with
  | Lhs t -> Lhs (f t)
  | Rhs t -> Rhs (f t)

let get_def (sgns: signatures) (s: symbol) =
  match Path.find_opt s sgns with
  | Some def -> def
  | None -> raise (UnknownTypeSymbol s)

let compute_kind base sgn =
  let rec go base ks =
    match ks with
    | [] -> base
    | k :: ks -> Arrow (k, go base ks)
  in go base (List.map snd sgn.arguments)

(** Infer the kind of a type expression *)
let rec infer_kind (sgns: signatures) (ctx: kind Ident.tbl) (t: tpe) =
  match t with
  | TySym s -> let _, _, k = get_def sgns s in k
  | TyVar x ->
    (match Ident.find_opt x ctx with
    | Some k -> k
    | None -> raise (UnboundTypeVariable x))
  | TyApp (t1, t2) ->
    (match infer_kind sgns ctx t1 with
    | Arrow (k_arg, k_res) -> check_kind sgns ctx t2 k_arg; k_res
    | k -> raise (ExpectedHigherKind (t1, k)))
  | TyExt _ -> Ext
  | TyPos sgn -> infer_signature_kind sgns ctx Pos sgn
  | TyNeg sgn -> infer_signature_kind sgns ctx Neg sgn

(** Check the kind of a type expression *)
and check_kind (sgns: signatures) (ctx: kind Ident.tbl) (t: tpe) (expected: kind) =
  let inferred = infer_kind sgns ctx t in
  if inferred <> expected then raise (KindMismatch (t, inferred, expected))

and infer_signature_kind
    (sgns: signatures) (ctx: kind Ident.tbl) (base: kind) (sgn: signature) =  
  (* Verify all constructors are well-formed *)
  let arg_kinds = List.map snd sgn.arguments in
  List.iter (fun xtor ->
    let ctx' =
      List.fold_left (fun acc (x, k) -> Ident.add x k acc) ctx xtor.quantified
    in
    List.iter2 (check_kind sgns ctx') xtor.parent_arguments arg_kinds;
    List.iter (fun ty ->
      ignore (infer_kind sgns ctx' (match ty with Lhs t | Rhs t -> t))
    ) xtor.parameters
  ) sgn.xtors;
  compute_kind base sgn

let infer_polarity (sgns: signatures) (ctx: kind Ident.tbl) (t: tpe) =
  match infer_kind sgns ctx t with
  | Pos -> Positive
  | Neg -> Negative
  | Ext -> Positive
  | Arrow _ -> failwith "Only first-order types have polarity"

(* ========================================================================= *)
(* Type-level operations                                                     *)
(* ========================================================================= *)

(** Add a signature without validating its xtors. Used for mutually recursive
  type definitions where the signature may reference types not yet added. *)
let add_def_unchecked (sgns: signatures) (polarity: polarity) (sgn: signature) =
  let base = match polarity with Positive -> Pos | Negative -> Neg in
  let k = compute_kind base sgn in
  Path.add sgn.name (sgn, polarity, k) sgns

(** Validate all xtors in a signature against the given signatures context.
  Should be called after all signatures have been added with add_def_unchecked. *)
let validate_signature (sgns: signatures) (sgn: signature) =
  let ctx = Ident.emptytbl in
  let arg_kinds = List.map snd sgn.arguments in
  List.iter (fun xtor ->
    let ctx' =
      List.fold_left (fun acc (x, k) -> Ident.add x k acc) ctx xtor.quantified
    in
    List.iter2 (check_kind sgns ctx') xtor.parent_arguments arg_kinds;
    List.iter (fun ty ->
      ignore (infer_kind sgns ctx' (match ty with Lhs t | Rhs t -> t))
    ) xtor.parameters
  ) sgn.xtors

(** Add the signature as either positive or negative polarity. Will fail if the
  signature is ill-kinded.*)
let add_def (sgns: signatures) (polarity: polarity) (sgn: signature) =
  match polarity with
  | Positive ->
    let k = infer_kind sgns Ident.emptytbl (TyPos sgn) in
    Path.add sgn.name (sgn, polarity, k) sgns
  | Negative ->
    let k = infer_kind sgns Ident.emptytbl (TyNeg sgn) in
    Path.add sgn.name (sgn, polarity, k) sgns

(* Substitution: replace type variables with their definitions *)
let rec subst (subs: tpe Ident.tbl) (t: tpe) =
  match t with
  | TySym _ -> t
  | TyVar x ->
    (match Ident.find_opt x subs with
    | Some t' -> t'
    | None -> t)
  | TyApp (t1, t2) -> TyApp (subst subs t1, subst subs t2)
  | TyExt _ -> t
  | TyPos sgn -> TyPos (subst_signature subs sgn)
  | TyNeg sgn -> TyNeg (subst_signature subs sgn)

and subst_signature (subs: tpe Ident.tbl) (sgn: signature) =
  { sgn with
    arguments =
      List.map (fun (t_opt, k) -> (Option.map (subst subs) t_opt, k)
      ) sgn.arguments
  ; xtors = List.map (subst_xtor subs) sgn.xtors
  }

and subst_xtor (subs: tpe Ident.tbl) (xtor: xtor) : xtor =
  (* Filter out quantified variables from the environment *)
  let subs' = Ident.filter (fun x _ ->
    not (List.exists (fun (y, _) -> Ident.equal x y) xtor.quantified)
  ) subs
  in
  { xtor with
    parameters = List.map (chiral_tpe_map (subst subs')) xtor.parameters
  ; parent_arguments = List.map (subst subs') xtor.parent_arguments
  ; constraints =
      Option.map (List.map (fun (x, t) -> (x, subst subs' t))) xtor.constraints
  }

(** Weak head normal form *)
let rec whnf (seen: Path.t list) (sgns: signatures) (ty: tpe) =
  let result = 
    match ty with
  | TyApp (f, a) ->
    (match whnf seen sgns f with
    | seen, TyPos sgn -> seen, TyPos (inst1 seen sgns sgn a)
    | seen, TyNeg sgn -> seen, TyNeg (inst1 seen sgns sgn a)
    | seen, f' when f' == f -> seen, ty (* Optimization *)
    | seen, f' -> seen, TyApp (f', a))
  | TySym s ->
    if List.exists (Path.equal s) seen then
      seen, ty (* Prevent infinite loops *)
    else
      let seen' = s :: seen in
      let sgn, pol, _ = get_def sgns s in
      (match pol with
      | Positive -> seen', TyPos sgn
      | Negative -> seen', TyNeg sgn)
  | _ -> seen, ty
  in
  result

and reduce (sgns: signatures) (ty: tpe) =
  snd (whnf [] sgns ty)

and reduce_seen (seen: Path.t list) (sgns: signatures) (ty: tpe) =
  snd (whnf seen sgns ty)

and inst1 (seen: Path.t list) (sgns: signatures) (sgn: signature) (arg: tpe) =
  let rec apply seen left arg =
    match left with
    | [] -> failwith "no argument to instantiate"
    | (None, k) :: rest -> seen @ (Some arg, k) :: rest
    | arg' :: rest -> apply (seen @ [arg']) rest arg
  in
  let sgn = { sgn with arguments = apply [] sgn.arguments arg } in
  let result (xtor: xtor) =
    (* Build the result type using constructor's type arguments *)
    let instantiated_args =
      List.map2 (fun result_arg (_, k) -> (Some result_arg, k)
      ) xtor.parent_arguments sgn.arguments
    in
    { sgn with arguments = instantiated_args }
  in
  let xtor_match xtor =
    match unify_signatures seen sgns sgn (result xtor) with
    | None -> None
    | Some sub ->
      (* Extract constraints for quantified variables *)
      let constraints_for_orig = 
        List.filter_map (fun (x, _k) ->
          match Ident.find_opt x sub with
          | Some ty -> Some (x, ty)
          | None -> None
        ) xtor.quantified
      in
      let combined_constraints = 
        match xtor.constraints with
        | None -> Some constraints_for_orig
        | Some prev -> Some (prev @ constraints_for_orig)
      in
      Some { xtor with constraints = combined_constraints }
  in
  { sgn with xtors = List.filter_map xtor_match sgn.xtors }

and unify_signatures
    (seen: Path.t list) (sgns: signatures) (sgn1: signature) (sgn2: signature) =
  let rec unify_args args1 args2 sub =
    match args1, args2 with
    | [], [] -> Some sub
    | (Some t1, _) :: rest1, (Some t2, _) :: rest2 ->
      let t1' = subst sub t1 in
      let t2' = subst sub t2 in
      (match unify seen sgns t1' t2' with
      | None -> None
      | Some sub' -> unify_args rest1 rest2 (Ident.join sub' sub))
    | (None, _) :: rest1, (None, _) :: rest2 ->
      unify_args rest1 rest2 sub
    (* Allow instantiated to unify with uninstantiated (for partial application) *)
    | (Some _, _) :: rest1, (None, _) :: rest2
    | (None, _) :: rest1, (Some _, _) :: rest2 ->
      unify_args rest1 rest2 sub
    | _ -> None
  in
  unify_args sgn1.arguments sgn2.arguments Ident.emptytbl

(** Unification: returns Some substitution if types unify, None otherwise *)
and unify (seen: Path.t list) (sgns: signatures) (t1: tpe) (t2: tpe) : (tpe Ident.tbl) option =
  let res = ref None in
  begin
    (* Structural match *)
    (match t1, t2 with
    | TySym s, TySym s' ->
      if Path.equal s s' then res := Some Ident.emptytbl
    | TyVar x, TyVar y when Ident.equal x y ->
      res := Some Ident.emptytbl
    | TyVar x, t | t, TyVar x ->
      (* Occurs check: don't allow x = ... x ... *)
      if not (occurs x t) then res := Some (Ident.add x t Ident.emptytbl)
    | TyApp (f1, a1), TyApp (f2, a2) ->
      (match unify seen sgns f1 f2 with
      | None -> ()
      | Some sub1 ->
        (match unify seen sgns (subst sub1 a1) (subst sub1 a2) with
        | None -> ()
        | Some sub2 -> res := Some (Ident.join sub2 sub1)))
    | TyPos sgn1, TyPos sgn2
    | TyNeg sgn1, TyNeg sgn2 when Path.equal sgn1.name sgn2.name ->
      res := unify_signatures seen sgns sgn1 sgn2
    | TyExt s1, TyExt s2 when Path.equal s1 s2 ->
      res := Some Ident.emptytbl
    | _ -> ());

    (* Try normalizing if structural match failed to detect *)
    if Option.is_none !res then
      let t1' = reduce_seen seen sgns t1 in
      if not (t1' == t1) then
        res := unify seen sgns t1' t2
      else
        let t2' = reduce_seen seen sgns t2 in
        if not (t2' == t2) then
          res := unify seen sgns t1 t2'
  end;
  !res

and occurs (x: Ident.t) (t: tpe) : bool =
  match t with
  | TySym _ -> false
  | TyVar y -> Ident.equal x y
  | TyApp (t1, t2) -> occurs x t1 || occurs x t2
  | TyExt _ -> false
  | TyPos sgn | TyNeg sgn ->
    List.exists (fun (t_opt, _) ->
      match t_opt with
      | Some t -> occurs x t
      | None -> false
    ) sgn.arguments

(** Checks for equivalence of two types *)
let equivalent (sgns: signatures) (t1: tpe) (t2: tpe) =
  match unify [] sgns t1 t2 with
  | Some subs -> Ident.is_empty subs
  | None -> false

(** Strong normal form of types *)
let norm (sgns: signatures) (ty: tpe) =
  let rec go (seen: Path.t list) (t: tpe) =
    match whnf seen sgns t with
    | _, (TyVar _ as v) -> v
    | _, (TySym _ as s) -> s
    | _, (TyExt _ as p) -> p
    | seen, TyApp (t1, t2) -> TyApp (go seen t1, go seen t2)
    | seen, TyPos sgn -> TyPos (go_sig seen sgn)
    | seen, TyNeg sgn -> TyNeg (go_sig seen sgn)
  and go_sig (seen: Path.t list) (sgn: signature) =
    let seen' = sgn.name :: seen in
    let normalized_xtors = List.map (fun xtor ->
      { xtor with
        parameters = List.map (chiral_tpe_map (go seen')) xtor.parameters
      ; parent_arguments = List.map (go seen') xtor.parent_arguments
      }) sgn.xtors
    in
    let normalized_arguments =
      List.map (fun (t_opt, k) -> (Option.map (go seen') t_opt, k)
      ) sgn.arguments
    in
    { sgn with
      arguments = normalized_arguments
    ; xtors = normalized_xtors
    }
  in
  go [] ty
