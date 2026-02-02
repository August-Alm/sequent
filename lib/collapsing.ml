(**
  Module: Collapsing
  Pass 2: Collapsing (Core -> Cut)
  
  Applies the 4 symmetric transformation rules from normalization.txt:
  
  ⟨C(Γ) | µ˜x.s ⟩                & ⟨µα.s |D(Γ)⟩                      → let v = m(Γ); s
  ⟨x | case {C(Γ) ⇒ s, ... }⟩    & ⟨cocase {D(Γ) ⇒ s, ... } | α⟩     → switch v {m(Γ) ⇒ s, ...}
  ⟨µα.s | case {C(Γ) ⇒ s, ... }⟩ & ⟨cocase {D(Γ) ⇒ s, ... } | µ˜x.s⟩ → new v = {m(Γ) ⇒ s, ...}; s
  ⟨C(Γ) | α⟩                     & ⟨x | D(Γ)⟩                        → invoke v m(Γ)
  
  Key insight: Variables change chirality during collapse:
  - let v = ... → v is Prd (producer)
  - switch v ... → v is Prd (producer)  
  - new v = ... → v is Cns (consumer)
  - invoke v ... → v is Cns (consumer)
*)

open Common.Identifiers
open Common.Types
module CT = Core.Terms
module CutT = Cut.Terms
module CutTypes = Cut.Types

type collapse_context = {
  defs: CT.definitions;
  chirality_reqs: Shrinking.chirality_context;
}

(** Simple dummy type for now - avoids infinite recursion in type conversion *)
let dummy_type = CutTypes.TyPrim (Path.of_primitive 0 "_", CutTypes.KStar)

(** Dummy chirality - just use Prd for everything *)
let dummy_chirality = CutTypes.Prd dummy_type

(** Infer chirality from context - use simple heuristic for now *)
let infer_chirality (_ctx: collapse_context) (_var: Ident.t) (_ty: typ) : CutTypes.chirality_type =
  (* Default: producers are eager (Prd) *)
  dummy_chirality

(** Main collapsing transformation *)
let rec collapse_statement (ctx: collapse_context) (s: CT.statement) : CutT.statement =
  match s with
  | CT.Cut (p, ty, c) -> collapse_cut ctx p ty c
  | CT.Call (f, _ty_args, prods, cons) ->
    let args = (List.map (function 
      | CT.Var x -> x 
      | _ -> failwith "Expected variable after shrinking") prods) @
      (List.map (function 
      | CT.Covar a -> a 
      | _ -> failwith "Expected covariable after shrinking") cons) in
    (* Call needs to be converted to invoke on first arg *)
    if args = [] then failwith "Empty call"
    else CutT.Invoke (List.hd args, f, [], List.tl args)

(** Collapse a cut into one of the 4 symmetric forms *)
and collapse_cut (ctx: collapse_context) (p: CT.producer) (_ty: Common.Types.typ) (c: CT.consumer) : CutT.statement =
  match (p, c) with
  
  (* FORM 1: ⟨C(Γ) | µ˜x.s⟩ → let x = C(Γ); s 
     x becomes a PRODUCER *)
  | (CT.Constructor (ctor, (_ty_args, prods, cons)), CT.MuTilde (x, s)) ->
    let args_env = 
      (List.map (fun p -> match p with 
        | CT.Var v -> (v, CutTypes.Prd (CutTypes.TyPrim (Path.of_primitive 0 "_", CutTypes.KStar)))
        | _ -> failwith "Expected variable") prods) @
      (List.map (fun c -> match c with
        | CT.Covar a -> (a, CutTypes.Cns (CutTypes.TyPrim (Path.of_primitive 0 "_", CutTypes.KStar)))
        | _ -> failwith "Expected covariable") cons) in
    CutT.Let (x, ctor, [], args_env, collapse_statement ctx s)
  
  (* FORM 1: ⟨µα.s | D(Γ)⟩ → let α = D(Γ); s 
     α becomes a PRODUCER *)
  | (CT.Mu (alpha, s), CT.Destructor (dtor, (_ty_args, prods, cons))) ->
    let args_env =
      (List.map (fun p -> match p with
        | CT.Var v -> (v, CutTypes.Prd (CutTypes.TyPrim (Path.of_primitive 0 "_", CutTypes.KStar)))
        | _ -> failwith "Expected variable") prods) @
      (List.map (fun c -> match c with
        | CT.Covar a -> (a, CutTypes.Cns (CutTypes.TyPrim (Path.of_primitive 0 "_", CutTypes.KStar)))
        | _ -> failwith "Expected covariable") cons) in
    CutT.Let (alpha, dtor, [], args_env, collapse_statement ctx s)
  
  (* FORM 2: ⟨x | case {C(Γ) ⇒ s, ...}⟩ → switch x {C(Γ) ⇒ s, ...} 
     x is a PRODUCER *)
  | (CT.Var x, CT.Case patterns) ->
    let branches = List.map (fun (pat: CT.pattern) ->
      let args_env =
        (List.map (fun v -> (v, CutTypes.Prd (CutTypes.TyPrim (Path.of_primitive 0 "_", CutTypes.KStar)))) pat.CT.variables) @
        (List.map (fun a -> (a, CutTypes.Cns (CutTypes.TyPrim (Path.of_primitive 0 "_", CutTypes.KStar)))) pat.CT.covariables) in
      (pat.CT.xtor, [], args_env, collapse_statement ctx pat.CT.statement)
    ) patterns in
    CutT.Switch (x, branches)
  
  (* FORM 2: ⟨cocase {D(Γ) ⇒ s, ...} | α⟩ → switch α {D(Γ) ⇒ s, ...} 
     α (covariable) becomes variable and is a PRODUCER *)
  | (CT.Cocase patterns, CT.Covar alpha) ->
    let branches = List.map (fun (pat: CT.pattern) ->
      let args_env =
        (List.map (fun v -> (v, CutTypes.Prd (CutTypes.TyPrim (Path.of_primitive 0 "_", CutTypes.KStar)))) pat.CT.variables) @
        (List.map (fun a -> (a, CutTypes.Cns (CutTypes.TyPrim (Path.of_primitive 0 "_", CutTypes.KStar)))) pat.CT.covariables) in
      (pat.CT.xtor, [], args_env, collapse_statement ctx pat.CT.statement)
    ) patterns in
    CutT.Switch (alpha, branches)
  
  (* FORM 3: ⟨µα.s1 | case {C(Γ) ⇒ s2, ...}⟩ → new α = {C(Γ) ⇒ s2, ...}; s1 
     α is a CONSUMER *)
  | (CT.Mu (alpha, s1), CT.Case patterns) ->
    let branches = List.map (fun (pat: CT.pattern) ->
      let args_env =
        (List.map (fun v -> (v, CutTypes.Prd dummy_type)) pat.CT.variables) @
        (List.map (fun a -> (a, CutTypes.Cns dummy_type)) pat.CT.covariables) in
      (pat.CT.xtor, [], args_env, collapse_statement ctx pat.CT.statement)
    ) patterns in
    CutT.New (alpha, dummy_type, [], branches, collapse_statement ctx s1)
  
  (* FORM 3: ⟨cocase {D(Γ) ⇒ s2, ...} | µ˜x.s1⟩ → new x = {D(Γ) ⇒ s2, ...}; s1 
     x is a CONSUMER *)
  | (CT.Cocase patterns, CT.MuTilde (x, s1)) ->
    let branches = List.map (fun (pat: CT.pattern) ->
      let args_env =
        (List.map (fun v -> (v, CutTypes.Prd dummy_type)) pat.CT.variables) @
        (List.map (fun a -> (a, CutTypes.Cns dummy_type)) pat.CT.covariables) in
      (pat.CT.xtor, [], args_env, collapse_statement ctx pat.CT.statement)
    ) patterns in
    CutT.New (x, dummy_type, [], branches, collapse_statement ctx s1)
  
  (* FORM 4: ⟨C(Γ) | α⟩ → invoke α C(Γ) 
     α (covariable) becomes variable and is a CONSUMER *)
  | (CT.Constructor (ctor, (_ty_args, prods, cons)), CT.Covar alpha) ->
    let args = 
      (List.map (function CT.Var v -> v | _ -> failwith "Expected variable") prods) @
      (List.map (function CT.Covar a -> a | _ -> failwith "Expected covariable") cons) in
    CutT.Invoke (alpha, ctor, [], args)
  
  (* FORM 4: ⟨x | D(Γ)⟩ → invoke x D(Γ) 
     x is a CONSUMER *)
  | (CT.Var x, CT.Destructor (dtor, (_ty_args, prods, cons))) ->
    let args =
      (List.map (function CT.Var v -> v | _ -> failwith "Expected variable") prods) @
      (List.map (function CT.Covar a -> a | _ -> failwith "Expected covariable") cons) in
    CutT.Invoke (x, dtor, [], args)
  
  | _ -> failwith "Unexpected cut form after shrinking"

(** Collapse a term definition into a Cut label definition *)
let collapse_term_def (ctx: collapse_context) (name: Path.t) (def: CT.term_def) : CutT.label * CutT.typ_env * CutT.statement =
  let label = CutT.MkLabel name in
  
  (* Build environment with chirality information *)
  let typ_env = 
    (List.map (fun (v, ty) -> (v, infer_chirality ctx v ty)) def.prod_args) @
    (List.map (fun (v, ty) -> (v, infer_chirality ctx v ty)) def.cons_args) in
  
  let body = collapse_statement ctx def.body in
  
  (label, typ_env, body)

(** Extract signatures from Core type definitions *)
let extract_signatures_from_defs (_defs: CT.definitions) : CutTypes.signature_defs =
  (* TODO: Proper signature extraction - for now return empty *)
  []

(** Entry point *)
let collapse_definitions (defs: CT.definitions) (chirality_reqs: Shrinking.chirality_context) 
  : CutT.definitions =
  let ctx = { defs; chirality_reqs } in
  
  let signatures = extract_signatures_from_defs defs in
  let program = List.map (fun (name, def) -> collapse_term_def ctx name def) defs.term_defs in
  
  { CutT.signatures; program }
