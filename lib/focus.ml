(**
  Module: Focus
  Description: Translates positive Kore to nonlinear Cut.

  The translation generalizes the simplified version in simple.ml to work
  handle also higher-kinded types and external import statements, while also
  specializing the translation so as to only map the positive fragment of
  Kore to Cut. The transformation is essentially defined by:

  ⟨C(Γ) | µ˜x.s⟩                  → let x = C(Γ); s
  ⟨x | case {C(Γ) ⇒ s, ... }⟩     → switch x {C(Γ) ⇒ s, ...}
  ⟨µα.s | case {C(Γ) ⇒ s, ... }⟩  → new α = {C(Γ) ⇒ s, ...}; s
  ⟨C(Γ) | α⟩                      → invoke α C(Γ)

  The dual statements

  ⟨µα.s | D(Γ)⟩
  ⟨cocase {D(Γ) ⇒ s, ... } | α⟩
  ⟨cocase {D(Γ) ⇒ s, ... } | µ˜x.s⟩
  ⟨x | D(Γ)⟩

  are negatively polarized and trigger exceptions.

*)

module Sym = Kore.Builtins.Sym
module Ext = Kore.Builtins.Ext
module Prim = Kore.Builtins.Prim
module KTy = Kore.Types
module KTm = Kore.Terms
module CTy = Cut.Types
module CTm = Cut.Terms
open Common.Identifiers

(* ========================================================================= *)
(* Exceptions                                                                *)
(* ========================================================================= *)

exception NegativePolarityNotSupported of string
exception IllTypedCut of string
exception UnexpectedTermForm of string

(* ========================================================================= *)
(* Type translation: Kore.Types → Cut.Types                                  *)
(* ========================================================================= *)

(** Translate Kore kind to Cut kind *)
let rec map_kind (k: KTy.kind) : CTy.kind =
  match k with
  | KTy.Pos -> CTy.KStar
  | KTy.Neg -> CTy.KStar  (* Negative types also map to * in Cut *)
  | KTy.Ext -> CTy.KStar  (* External types are proper types *)
  | KTy.Arrow (k1, k2) -> CTy.KArrow (map_kind k1, map_kind k2)

(** Translate Kore type to Cut type *)
let rec map_type (ty: KTy.tpe) : CTy.typ =
  match ty with
  | KTy.TyVar x -> CTy.TyVar x
  | KTy.TySym s -> CTy.TySym s
  | KTy.TyApp (t1, t2) -> CTy.TyApp (map_type t1, map_type t2)
  | KTy.TyExt s -> CTy.TyPrim (s, CTy.KStar)
  | KTy.TyPos sgn -> CTy.TyDef (map_signature sgn)
  | KTy.TyNeg sgn -> CTy.TyDef (map_signature sgn)

(** Translate Kore chiral type to Cut chirality type *)
and map_chiral (ct: KTy.chiral_tpe) : CTy.chirality_type =
  match ct with
  | KTy.Lhs ty -> CTy.Prd (map_type ty)
  | KTy.Rhs ty -> CTy.Cns (map_type ty)

(** Translate Kore signature to Cut signature *)
and map_signature (sgn: KTy.signature) : CTy.signature =
  { CTy.symbol = sgn.KTy.name
  ; parameters = List.map (fun (t_opt, k) ->
      (Option.map map_type t_opt, map_kind k)
    ) sgn.KTy.arguments
  ; methods = List.map map_xtor sgn.KTy.xtors
  }

(** Translate Kore xtor to Cut method_sig *)
and map_xtor (xtor: KTy.xtor) : CTy.method_sig =
  (* Build environment from parameters *)
  let env = List.map (fun ct ->
    let v = Ident.fresh () in  (* Generate fresh names for method params *)
    (v, map_chiral ct)
  ) xtor.KTy.parameters in
  (* The result type is determined by parent_arguments *)
  let result_ty = 
    let base = CTy.TySym xtor.KTy.parent in
    List.fold_left (fun acc arg -> CTy.TyApp (acc, map_type arg)
    ) base xtor.KTy.parent_arguments
  in
  { CTy.parent = xtor.KTy.parent
  ; symbol = xtor.KTy.name
  ; quantified = List.map (fun (v, k) -> (v, map_kind k)) xtor.KTy.quantified
  ; environment = env
  ; result_type = CTy.Prd result_ty  (* Constructors produce *)
  ; constraints = Option.map (List.map (fun (v, t) -> (v, map_type t))) xtor.KTy.constraints
  }

(* ========================================================================= *)
(* Substitutions                                                             *)
(* ========================================================================= *)

module Sub = struct
  type t = Ident.t Ident.tbl
  
  let empty : t = Ident.emptytbl
  
  let add (x: Ident.t) (y: Ident.t) (s: t) : t =
    Ident.add x y s
  
  let apply (s: t) (x: Ident.t) : Ident.t =
    match Ident.find_opt x s with
    | Some y -> y
    | None -> x
end

(* ========================================================================= *)
(* Term translation: Kore.Terms → Cut.Terms                                  *)
(* ========================================================================= *)

(** Get the signature from a positive type for η-expansion *)
let get_pos_signature (sgns: KTy.signatures) (ty: KTy.tpe) : KTy.signature =
  match KTy.reduce sgns ty with
  | KTy.TyPos sgn -> sgn
  | KTy.TySym s ->
    let sgn, _, _ = KTy.get_def sgns s in sgn
  | _ -> failwith "get_pos_signature: expected positive type"

(** Build a typ_env from Kore branch variables and xtor parameters *)
let build_env (vars: Ident.t list) (params: KTy.chiral_tpe list) : CTm.typ_env =
  List.map2 (fun v ct -> (v, map_chiral ct)) vars params

(** Generate fresh variables for xtor parameters *)
let fresh_params (params: KTy.chiral_tpe list) : Ident.t list =
  List.map (fun _ -> Ident.fresh ()) params

(** Build branches from a signature for η-expansion *)
let build_eta_branches (_sgns: KTy.signatures) (sgn: KTy.signature) (_h: Sub.t)
    (build_body: KTy.xtor -> Ident.t list -> CTm.statement) : CTm.branches =
  List.map (fun xtor ->
    let params = fresh_params xtor.KTy.parameters in
    let tys = List.map (fun (_, _k) -> CTy.TyVar (Ident.fresh ())) xtor.KTy.quantified in
    let env = build_env params xtor.KTy.parameters in
    (xtor.KTy.name, tys, env, build_body xtor params)
  ) sgn.KTy.xtors

(** Translate Kore branch to Cut branch entry *)
let rec map_branch (sgns: KTy.signatures) (h: Sub.t) (br: KTm.branch) 
    : CTm.symbol * CTm.typ list * CTm.typ_env * CTm.statement =
  let tys = List.map (fun (_, _k) -> 
    CTy.TyVar (Ident.fresh ())
  ) br.KTm.type_vars in
  let env = build_env br.KTm.term_vars br.KTm.xtor.KTy.parameters in
  let h' = List.fold_left2 (fun acc old new_ -> Sub.add old new_ acc) 
           h br.KTm.term_vars (List.map fst env) in
  (br.KTm.xtor.KTy.name, tys, env, map_command sgns h' br.KTm.command)

(** Translate multiple Kore branches to Cut branches *)
and map_branches (sgns: KTy.signatures) (h: Sub.t) (brs: KTm.branch list) : CTm.branches =
  List.map (map_branch sgns h) brs

(** Translate Kore clause to Cut extern branch *)
and map_clause (sgns: KTy.signatures) (h: Sub.t) (cl: KTm.clause) : CTm.typ_env * CTm.statement =
  let env = List.map (fun v -> (v, CTy.Ext (CTy.TyVar (Ident.fresh ())))) cl.KTm.parameters in
  let h' = List.fold_left2 (fun acc old new_ -> Sub.add old new_ acc)
           h cl.KTm.parameters (List.map fst env) in
  (env, map_command sgns h' cl.KTm.body)

(**
  Bind a producer term to a variable, calling continuation with the variable.
  
  If the term is already a variable, just call the continuation.
  Otherwise, normalize by creating a binding:
    N[⟨...p...⟩] = N[⟨p | µ̃x. N[⟨...x...⟩]⟩]
  
  This corresponds to the rule:
    N[⟨C(..., p, ...) | c0⟩] = N[⟨p | µ̃x.N[⟨C(..., x, ...) | c0⟩]⟩]
*)
and bind_producer (sgns: KTy.signatures) (h: Sub.t) (term: KTm.term) (ty: KTy.tpe)
    (k: Ident.t -> CTm.statement) : CTm.statement =
  match term with
  | KTm.Variable x -> 
    k (Sub.apply h x)
  
  | KTm.Constructor (xtor, ty_args, args) ->
    (* Bind all arguments first, then create Let for the constructor *)
    bind_producers sgns h args xtor.KTy.parameters (fun arg_vars ->
      let x = Ident.fresh () in
      let tys' = List.map map_type ty_args in
      let env = build_env arg_vars xtor.KTy.parameters in
      CTm.Let (x, xtor.KTy.name, tys', env, k x))
  
  | KTm.MuLhsPos (ty', alpha, s) ->
    (* µα.s is a producer - η-expand to create a New with switch branches *)
    let sgn = get_pos_signature sgns ty' in
    let branches = build_eta_branches sgns sgn h (fun xtor params ->
      (* Each branch: C(Γ) ⇒ ⟨C(Γ) | α⟩ after binding *)
      let tys' = List.map map_type xtor.KTy.parent_arguments in
      CTm.Invoke (alpha, xtor.KTy.name, tys', params)
    ) in
    let _x = Ident.fresh () in  (* Unused but kept for documentation *)
    CTm.New (alpha, map_type ty', [], branches, 
      map_command sgns (Sub.add alpha alpha h) s)
    (* Then continue with the bound value... but MuLhsPos produces a consumer not producer *)
    (* Actually this case shouldn't happen for producers *)
  
  | KTm.Match (_sgn, _branches) ->
    (* Match produces a consumer, not a producer - this shouldn't be called *)
    failwith "bind_producer: Match is a consumer, not a producer"
  
  | KTm.New (_sgn, branches) ->
    (* New produces a (co)value - bind it *)
    let x = Ident.fresh () in
    let branches' = map_branches sgns h branches in
    let ty' = map_type ty in
    CTm.New (x, ty', [], branches', k x)
  
  | KTm.Destructor _ ->
    failwith "bind_producer: Destructor is a consumer"
  
  | KTm.MuRhsPos _ | KTm.MuLhsNeg _ | KTm.MuRhsNeg _ ->
    failwith "bind_producer: unexpected term form"

(** Bind multiple producer terms sequentially *)
and bind_producers (sgns: KTy.signatures) (h: Sub.t) 
    (terms: KTm.term list) (tys: KTy.chiral_tpe list)
    (k: Ident.t list -> CTm.statement) : CTm.statement =
  match terms, tys with
  | [], [] -> k []
  | t :: rest_terms, KTy.Lhs ty :: rest_tys ->
    bind_producer sgns h t ty (fun v ->
      bind_producers sgns h rest_terms rest_tys (fun vs -> k (v :: vs)))
  | t :: rest_terms, KTy.Rhs ty :: rest_tys ->
    (* Consumer argument - bind it differently *)
    bind_consumer sgns h t ty (fun v ->
      bind_producers sgns h rest_terms rest_tys (fun vs -> k (v :: vs)))
  | _ -> failwith "bind_producers: mismatched lengths"

(**
  Bind a consumer term to a covariable, calling continuation with the covariable.
  
  If the term is already a variable, just call the continuation.
  Otherwise, normalize by creating a binding:
    N[⟨...c...⟩] = N[⟨µα. N[⟨...α...⟩] | c⟩]
*)
and bind_consumer (sgns: KTy.signatures) (h: Sub.t) (term: KTm.term) (ty: KTy.tpe)
    (k: Ident.t -> CTm.statement) : CTm.statement =
  match term with
  | KTm.Variable alpha ->
    k (Sub.apply h alpha)
  
  | KTm.Match (_sgn, branches) ->
    (* case {...} is a consumer - η-expand by creating New *)
    let alpha = Ident.fresh () in
    let branches' = map_branches sgns h branches in
    let ty' = map_type ty in
    CTm.New (alpha, ty', [], branches', k alpha)
  
  | KTm.MuRhsPos (ty', x, s) ->
    (* µ̃x.s is a consumer - inline by substitution when cut with a producer *)
    (* But here we need to bind it... create a switch *)
    let sgn = get_pos_signature sgns ty' in
    let alpha = Ident.fresh () in
    let branches = build_eta_branches sgns sgn h (fun xtor params ->
      (* Each branch: C(Γ) ⇒ ⟨C(Γ) | µ̃x.s⟩ which becomes let x = C(Γ); s *)
      let tys' = List.map map_type xtor.KTy.parent_arguments in
      let env = build_env params xtor.KTy.parameters in
      CTm.Let (x, xtor.KTy.name, tys', env, 
        map_command sgns (Sub.add x x h) s)
    ) in
    CTm.New (alpha, map_type ty', [], branches, k alpha)
  
  | KTm.Destructor (xtor, ty_args, args) ->
    (* Destructor is a consumer *)
    bind_producers sgns h args xtor.KTy.parameters (fun _arg_vars ->
      let _alpha = Ident.fresh () in
      let _tys' = List.map map_type ty_args in
      (* Need to create something that consumes... *)
      failwith "bind_consumer: Destructor binding not yet implemented")
  
  | _ ->
    failwith "bind_consumer: unexpected term form"

(** Lookup branch by constructor name and inline it *)
and lookup_and_inline (sgns: KTy.signatures) (h: Sub.t) 
    (branches: KTm.branch list) (xtor: KTy.xtor) (arg_vars: Ident.t list) 
    : CTm.statement =
  match List.find_opt (fun br -> Path.equal br.KTm.xtor.KTy.name xtor.KTy.name) branches with
  | Some br ->
    let h' = List.fold_left2 (fun acc v a -> Sub.add v a acc) h br.KTm.term_vars arg_vars in
    map_command sgns h' br.KTm.command
  | None ->
    failwith "lookup_and_inline: constructor not found in branches"

(** Main command translation with normalization *)
and map_command (sgns: KTy.signatures) (h: Sub.t) (cmd: KTm.command) : CTm.statement =
  match cmd with
  | KTm.End -> 
    let halt = Ident.fresh () in
    CTm.Forward (halt, halt)

  | KTm.Call (sym, tys, _args) ->
    (* Bind all arguments, then jump *)
    (* TODO: proper binding - args should be bound and passed *)
    let tys' = List.map map_type tys in
    CTm.Jump (CTm.MkLabel sym, tys')

  | KTm.Extern (sym, args, clauses) ->
    bind_extern_args sgns h args (fun arg_vars ->
      let branches = List.map (map_clause sgns h) clauses in
      CTm.Extern (sym, arg_vars, branches))

  | KTm.CutPos (ty, lhs, rhs) ->
    map_cut_pos sgns h ty lhs rhs

  | KTm.CutNeg (_, _, _) ->
    raise (NegativePolarityNotSupported "CutNeg in positive fragment")

(** Bind extern arguments (all should be producers of external type) *)
and bind_extern_args (sgns: KTy.signatures) (h: Sub.t) (args: KTm.term list)
    (k: Ident.t list -> CTm.statement) : CTm.statement =
  match args with
  | [] -> k []
  | t :: rest ->
    (match t with
    | KTm.Variable x -> 
      bind_extern_args sgns h rest (fun vs -> k (Sub.apply h x :: vs))
    | _ ->
      (* Need to bind non-variable - but extern args don't have Kore types *)
      failwith "bind_extern_args: non-variable extern argument")

(**
  Map a positive cut based on the forms of lhs and rhs.
  
  Implements the focusing/normalization rules:
  - Known cuts: ⟨C(Γ) | case {...}⟩ → inline branch
  - Unknown cuts: ⟨x | α⟩ → η-expand 
  - Critical pairs: ⟨µα.s | µ̃x.s'⟩ → η-expand
  - Standard forms: ⟨C(Γ)|µ̃x.s⟩, ⟨x|case{...}⟩, ⟨µα.s|case{...}⟩, ⟨C(Γ)|α⟩
*)
and map_cut_pos (sgns: KTy.signatures) (h: Sub.t) (ty: KTy.tpe) 
    (lhs: KTm.term) (rhs: KTm.term) : CTm.statement =
  match lhs, rhs with
  
  (* ========== Standard focused forms ========== *)
  
  (* ⟨C(Γ) | µ̃x.s⟩ → let x = C(Γ); s *)
  | KTm.Constructor (xtor, ty_args, args), KTm.MuRhsPos (_, x, s) ->
    bind_producers sgns h args xtor.KTy.parameters (fun arg_vars ->
      let tys' = List.map map_type ty_args in
      let env = build_env arg_vars xtor.KTy.parameters in
      CTm.Let (x, xtor.KTy.name, tys', env, 
        map_command sgns (Sub.add x x h) s))

  (* ⟨x | case {C(Γ) ⇒ s, ...}⟩ → switch x {...} *)
  | KTm.Variable x, KTm.Match (_, branches) ->
    let x' = Sub.apply h x in
    CTm.Switch (x', map_branches sgns h branches)

  (* ⟨µα.s | case {C(Γ) ⇒ s', ...}⟩ → new α = {...}; s *)
  | KTm.MuLhsPos (_, alpha, s), KTm.Match (_, branches) ->
    let ty' = map_type ty in
    let branches' = map_branches sgns h branches in
    CTm.New (alpha, ty', [], branches', 
      map_command sgns (Sub.add alpha alpha h) s)

  (* ⟨C(Γ) | α⟩ → invoke α C(Γ) *)
  | KTm.Constructor (xtor, ty_args, args), KTm.Variable alpha ->
    bind_producers sgns h args xtor.KTy.parameters (fun arg_vars ->
      let alpha' = Sub.apply h alpha in
      let tys' = List.map map_type ty_args in
      CTm.Invoke (alpha', xtor.KTy.name, tys', arg_vars))

  (* ========== Completely known cuts - inline ========== *)
  
  (* ⟨C(Γ0) | case {..., C(Γ) ⇒ s, ...}⟩ → s{Γ → Γ0} *)
  | KTm.Constructor (xtor, _ty_args, args), KTm.Match (_, branches) ->
    bind_producers sgns h args xtor.KTy.parameters (fun arg_vars ->
      lookup_and_inline sgns h branches xtor arg_vars)

  (* ========== Variable-variable substitution ========== *)
  
  (* ⟨x | µ̃y.s⟩ → s{y → x} *)
  | KTm.Variable x, KTm.MuRhsPos (_, y, s) ->
    let x' = Sub.apply h x in
    map_command sgns (Sub.add y x' h) s

  (* ⟨µα.s | α'⟩ → s{α → α'} *)
  | KTm.MuLhsPos (_, alpha, s), KTm.Variable alpha' ->
    let alpha'' = Sub.apply h alpha' in
    map_command sgns (Sub.add alpha alpha'' h) s

  (* ========== Completely unknown cuts - η-expand ========== *)
  
  (* ⟨x | α⟩_T → ⟨x | case {C1(Γ1) ⇒ ⟨C1(Γ1) | α⟩, ...}⟩ for data T *)
  | KTm.Variable x, KTm.Variable alpha ->
    let x' = Sub.apply h x in
    let alpha' = Sub.apply h alpha in
    let sgn = get_pos_signature sgns ty in
    let branches = build_eta_branches sgns sgn h (fun xtor params ->
      let tys' = List.map map_type xtor.KTy.parent_arguments in
      CTm.Invoke (alpha', xtor.KTy.name, tys', params)
    ) in
    CTm.Switch (x', branches)

  (* ========== Critical pairs - η-expand ========== *)
  
  (* ⟨µα.s1 | µ̃x.s2⟩_T → ⟨µα.s1 | case {C1(Γ1) ⇒ ⟨C1(Γ1) | µ̃x.s2⟩, ...}⟩ for data T *)
  | KTm.MuLhsPos (_, alpha, s1), KTm.MuRhsPos (_, x, s2) ->
    let sgn = get_pos_signature sgns ty in
    (* Build branches: each C(Γ) ⇒ let x = C(Γ); s2 *)
    let branches = build_eta_branches sgns sgn h (fun xtor params ->
      let tys' = List.map map_type xtor.KTy.parent_arguments in
      let env = build_env params xtor.KTy.parameters in
      CTm.Let (x, xtor.KTy.name, tys', env,
        map_command sgns (Sub.add x x h) s2)
    ) in
    let ty' = map_type ty in
    CTm.New (alpha, ty', [], branches,
      map_command sgns (Sub.add alpha alpha h) s1)

  (* ========== Normalization: non-variable arguments ========== *)
  
  (* If lhs is not a value form, bind it first *)
  | lhs, rhs when not (is_lhs_value lhs) ->
    bind_producer sgns h lhs ty (fun x ->
      map_cut_pos sgns h ty (KTm.Variable x) rhs)
  
  (* If rhs is not a continuation form, bind it first *)  
  | lhs, rhs when not (is_rhs_continuation rhs) ->
    bind_consumer sgns h rhs ty (fun alpha ->
      map_cut_pos sgns h ty lhs (KTm.Variable alpha))

  | _, _ ->
    raise (IllTypedCut "Unexpected positive cut combination")

(** Check if lhs is a value form (Variable or Constructor) *)
and is_lhs_value (t: KTm.term) : bool =
  match t with
  | KTm.Variable _ | KTm.Constructor _ | KTm.MuLhsPos _ -> true
  | _ -> false

(** Check if rhs is a continuation form (Variable, Match, or MuRhsPos) *)
and is_rhs_continuation (t: KTm.term) : bool =
  match t with
  | KTm.Variable _ | KTm.Match _ | KTm.MuRhsPos _ -> true
  | _ -> false

(* ========================================================================= *)
(* Top-level translation                                                     *)
(* ========================================================================= *)

(** Translate a Kore definition to a Cut program entry (before linearization) *)
let map_definition_raw (sgns: KTy.signatures) (def: KTm.definition) 
    : CTm.label * CTm.typ_env * CTm.statement =
  let label = CTm.MkLabel def.KTm.name in
  let env = List.map (fun (v, ct) -> (v, map_chiral ct)) def.KTm.term_params in
  let stmt = map_command sgns Sub.empty def.KTm.body in
  (label, env, stmt)

(** Translate a Kore definition to a Cut program entry (with linearization) *)
let map_definition (sgns: KTy.signatures) (def: KTm.definition) 
    : CTm.label * CTm.typ_env * CTm.statement =
  map_definition_raw sgns def

(** Translate a Kore environment to Cut definitions (before linearization) *)
let map_env_raw (env: KTm.Env.t) : CTm.definitions =
  let sgns = env.KTm.Env.signatures in
  let program = 
    List.fold_left (fun acc (_, def) -> map_definition_raw sgns def :: acc) 
      [] (Path.to_list env.KTm.Env.terms)
  in
  { CTm.signatures = []  (* TODO: translate signatures *)
  ; program = program
  }

(** Translate a Kore environment to Cut definitions (with linearization) *)
let map_env (env: KTm.Env.t) : CTm.definitions =
  let defs = map_env_raw env in
  Cut.Linearize.linearize_definitions defs