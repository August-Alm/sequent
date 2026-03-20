(**
  module: Axil.Terms
  description: AST and type checking for AXIL.
*)

open Common.Identifiers
open Common.External
open Types.AxilBase
open Types.AxilTypes

let ( let* ) o f = Utility.( let* ) o f

type var = Ident.t
type sym = Path.t

(* ========================================================================= *)
(* Commands                                                                  *)
(* ========================================================================= *)
   
(*
  Programs are typed with signatures Σ and with labels Θ. The statement for
  each label must be well-typed in the annotated type environment Γ. The only
  typing rule that refers to the label environment is JUMP. It ensures that
  the current type environment exactly matches the one assumed by the label.
  We omit the signatures Σ and the label environment Θ from the rules, since
  they do not change.
  
  Rule SUBSTITUTE for explicit substitutions makes the structural rules of
  weakening, contraction, and exchange explicit.  It is the only place where
  sharing and erasing of variables can occur and also the only way to reorder
  variables in the environment for the subsequent statement s. All the other
  typing rules, except for primitives of external types, follow the rules of
  ordered (aka, linear) logic.  Primitives for external types, such as add, do
  not consume the variables they use and it does not matter at which positions
  in the environment these variables occur.
   
   Types are ambidextrous: the same signature can be read as data or codata.
   - Data reading: Let (constructor), Switch (pattern match)
   - Codata reading: New (copattern), Invoke (destructor)
   
   Type instantiation is already reflected in sgn_typ/xtor.
*)

type command =
    (* let v = m(x1, ...); s
       
      Σ(T) = {..., m(Γ0), ...}    Γ, v : prd T ⊢ s
      --------------------------------------------- [LET]
      Γ, Γ0 ⊢ let v = m(x1, ...); s
      
      Constructs a producer of T using constructor m. *)
    (* v, instantiated dec, m, xi's, s *)
    Let of var * dec * sym * (var list) * command

    (* switch v {m1(y1, ...) ⇒ s1, ...}
       
      Σ(T) = {m1(Γ1), ...}     Γ, Γ1 ⊢ s1    ...
      ------------------------------------------ [SWITCH]
      Γ, v : prd T ⊢ switch v {m1(Γ1) ⇒ s1, ...}
      
      Pattern matches on producer v of signature T. *)
    (* v, instantiated dec, branches *)
  | Switch of var * dec * branch list

    (* new v = {m1(y1, ...) ⇒ s1, ...}; s
       
      Σ(T) = {m1(Γ1), ...}    Γ, v : cns T ⊢ s     Γ1, Γ0 ⊢ s1    ...
      ---------------------------------------------------------------- [NEW]
      Γ, Γ0 ⊢ new v = (Γ0){m1(Γ1) ⇒ s1, ...}; s
      
      Creates a consumer of T via copattern matching. *)
    (* v, instantiated dec, branches, s *)
  | New of var * dec * branch list * command

    (* invoke v m(x1, ...)
       
      Σ(T) = {..., m(Γ), ...}
      ------------------------- [INVOKE]
      Γ, v : cns T ⊢ invoke v m
      
      Invokes destructor m on consumer v. *)
    (* v, instantiated dec, m, xi's *)
  | Invoke of var * dec * sym * (var list)

    (* jump s  

      Θ(l) = Γ
      ---------- [JUMP]
      Γ ⊢ jump l 
    
    Jump: Go to top-level definition/label *)
  | Jump of sym * (var list)

    (* substitute [v'₁ → v₁, ..., v'ₙ → vₙ]; s

      Γ'(v'ᵢ) = τᵢ    Γ(vᵢ) = τᵢ    (for each i)    Γ' ⊢ s
      -------------------------------------------------------[SUBSTITUTE]
      Γ ⊢ substitute [v'₁ ← v₁, ..., v'ₙ ← vₙ]; s

      Each substitution pair must preserve types, and the body must type check in the
      reordered environment. *)
    (* [(v'₁, v₁), ..., (v'ₙ, vₙ)], s *)
  | Substitute of (var * var) list * command

  (* Primitives for external types ==========================================*)

    (* ⟨v | k⟩
       
      Γ(v) = prd τ    Γ(k) = cns τ
      ----------------------------- [AXIOM]
      Γ ⊢ ⟨v | k⟩
      
      Cut: pass producer v to consumer k at primitive type τ. *)
  | Axiom of ext_type * var * var

  | Lit of int64 * var * command       (* lit n { v ⇒ s } *)
  | NewInt of var * var * command * command  (* new k = { v ⇒ s1 }; s2 - Int consumer binding, k : Cns Int *)
  | Add of var * var * var * command (* add(x, y) { v ⇒ s } *)
  | Sub of var * var * var * command (* sub(x, y) { v ⇒ s } *)
  | Mul of var * var * var * command (* mul(x, y) { v ⇒ s } *)
  | Div of var * var * var * command (* div(x, y) { v ⇒ s } *)
  | Rem of var * var * var * command (* rem(x, y) { v ⇒ s } *)
  | Ifz of var * command * command   (* ifz(v) { sThen; sElse } *)

  (* Destination primitives *)

    (* let (v, d) = alloc{T}; s

      Γ, v: prd[ω] τ, x: prd[1] dest(τ) ⊢ s
      ------------------------------------- [ALLOC]
      Γ ⊢ let (v, d) = alloc{T}; s

    Alloc: Create fresh (unitialized) v and destination x (writing to v). *)
  | Alloc of var * var * typ * command

    (* fill{T} d v; s
    
      Γ ⊢ s
      ----------------------------------------------- [FILL]
      Γ, v: prd[ω] τ, x: prd[1] dest(τ) ⊢ fill x v; s

    Fill: Fill a destination x with a value v. *)
  | Fill of var * var * typ * command

    (* let (xi) = unfold d m; s
    
      m(prd[1] τ_i) constructor of τ
      Γ, (xi: prd[1] dest(τi)) ⊢ s
      ------------------------------------------- [UNFOLD]
      Γ, (d: prd[1] τ) ⊢ let (xi) = unfold d m; s 

    Unfold: Extracts the subdestinations with respect to a data constructor.  *)
    (* xi's, x, instantiated dec, m, s *)
  | Unfold of (var list) * var * dec * sym * command

  (* Terminals *)
  | Ret of typ * var  (* ret τ v *)
  | End

and branch = sym * (var list) * (var list) * command

(* ========================================================================= *)
(* Type Checking Errors                                                      *)
(* ========================================================================= *)

type check_error =
    UnboundVariable of var
  | UnboundDeclaration of Path.t
  | UnboundDefinition of Path.t
  | UnboundXtor of Path.t * Path.t
  | UnificationFailed of typ * typ
  | ChiralityMismatch of { expected_chirality: [`Prd | `Cns]; actual: chiral_typ }
  | XtorArityMismatch of { xtor: Path.t; expected: int; got: int }
  | TypeVarArityMismatch of { xtor: Path.t; expected: int; got: int }
  | NonExhaustiveMatch of { dec_name: Path.t; missing: Path.t list }
  | ArityMismatch of { expected: int; got: int }
  | ExpectedSignature of typ
  | LinearOrderViolation of { expected: var; got: var }
  | ContextNotEmpty of (var * chiral_typ) list

type 'a check_result = ('a, check_error) result

(* ========================================================================= *)
(* Type Checking Context and Helpers                                         *)
(* ========================================================================= *)

type definition =
  { path: sym
  ; term_params: (var * chiral_typ) list
  ; body: command
  }

type context =
  { types: Types.AxilTypes.context
  ; defs: definition Path.tbl
  ; term_vars: chiral_typ Ident.tbl
  }

(** Create an initial context from type declarations and term definitions *)
let make_tc_context (type_defs: dec Path.tbl) (defs: definition Path.tbl) : context =
  let tyctx = List.fold_left (fun ctx ((p, dec): (Path.t * dec)) ->
    { ctx with decs = Path.add p dec ctx.decs }
  ) empty_context (Path.to_list type_defs) in
  { types = tyctx; term_vars = Ident.emptytbl; defs = defs }

(** Lookup a declaration (data/codata type) by path *)
let lookup_dec (ctx: context) (p: Path.t) : (dec, check_error) result =
  match Path.find_opt p ctx.types.decs with
    Some d -> Ok d | None -> Error (UnboundDeclaration p)

(** Lookup a definition (top-level label) by path *)
let lookup_def (ctx: context) (p: Path.t) : (definition, check_error) result =
  match Path.find_opt p ctx.defs with
    Some d -> Ok d | None -> Error (UnboundDefinition p)

(** Find an xtor in a declaration *)
let find_xtor (dec: dec) (xtor_name: Path.t) : xtor option =
  List.find_opt (fun (x: xtor) -> Path.equal x.name xtor_name) dec.xtors

(* ========================================================================= *)
(* Ordered Context Operations                                                *)
(* ========================================================================= *)
(* The context is an ordered list where:
   - Head (prefix) = first elements of the list
   - Tail (suffix) = remaining elements
   
   Context ordering: [x1:τ1, x2:τ2, ..., xn:τn]
   Written in rules as: Γ = xn:τn, ..., x2:τ2, x1:τ1 (head on right)
   
   In our list representation:
   - List head = context head (rightmost in rule notation)
   - List tail = context tail (leftmost in rule notation)
*)

(** Lookup a variable in context (non-consuming, for primitives) *)
let lookup_var (ctx: context) (v: var) : chiral_typ check_result =
  match Ident.find_opt v ctx.term_vars with
    Some ct -> Ok ct
  | None -> Error (UnboundVariable v)

(** Prepend a binding at the head of context (front of list) *)
let prepend (ctx: context) (v: var) (ct: chiral_typ) : context =
  let vars_list = Ident.to_list ctx.term_vars in
  { ctx with term_vars = Ident.of_list ((v, ct) :: vars_list) }

(** Prepend multiple bindings at the head of context.
    prepend_many ctx [(x1,τ1), (x2,τ2)] results in x1:τ1, x2:τ2, Γ
    i.e., the first binding ends up at the head *)
let prepend_many (ctx: context) (bindings: (var * chiral_typ) list) : context =
  let vars_list = Ident.to_list ctx.term_vars in
  { ctx with term_vars = Ident.of_list (bindings @ vars_list) }

(** Append multiple bindings at the tail of context.
    append_many ctx [(x1,τ1), (x2,τ2)] results in Γ, x1:τ1, x2:τ2
    i.e., the bindings are added at the end *)
let append_many (ctx: context) (bindings: (var * chiral_typ) list) : context =
  let vars_list = Ident.to_list ctx.term_vars in
  { ctx with term_vars = Ident.of_list (vars_list @ bindings) }

(** Extend context with a type variable binding *)
let extend_tyvar (ctx: context) (v: var) (k: typ) : context =
  { ctx with types = { ctx.types with typ_vars = Ident.add v k ctx.types.typ_vars } }

(** Consume head variable from context.
    For Γ, v:τ (v at head), returns (τ, Γ). *)
let consume_head (ctx: context) : ((var * chiral_typ) * context) check_result =
  match Ident.to_list ctx.term_vars with
    [] -> Error (UnboundVariable (Ident.mk "_empty_"))
  | (v, ct) :: rest ->
      Ok ((v, ct), { ctx with term_vars = Ident.of_list rest })

(** Consume a specific variable from head position.
    Checks that the expected variable is actually at the head. *)
let consume_head_var (ctx: context) (expected: var) 
    : (chiral_typ * context) check_result =
  match Ident.to_list ctx.term_vars with
    [] -> Error (UnboundVariable expected)
  | (v, ct) :: rest ->
      if Ident.equal v expected then
        Ok (ct, { ctx with term_vars = Ident.of_list rest })
      else
        Error (LinearOrderViolation { expected; got = v })

(** Consume n variables from the head (prefix) of context.
    Returns (prefix_bindings, tail_context).
    
    For context Γ0, Γ where |Γ0| = n:
    consume_prefix ctx n = (Γ0, ctx_with_only_Γ) *)
let consume_prefix (ctx: context) (n: int) 
    : ((var * chiral_typ) list * context) check_result =
  let vars_list = Ident.to_list ctx.term_vars in
  let rec take_n acc n lst =
    if n = 0 then Ok (List.rev acc, lst)
    else match lst with
      [] -> Error (UnboundVariable (Ident.mk "_insufficient_"))
    | x :: xs -> take_n (x :: acc) (n - 1) xs
  in
  let* (prefix, tail) = take_n [] n vars_list in
  Ok (prefix, { ctx with term_vars = Ident.of_list tail })

(** Consume specific variables from prefix in order.
    Verifies that the given vars match the prefix exactly. *)
let consume_prefix_vars (ctx: context) (expected_vars: var list)
    : ((var * chiral_typ) list * context) check_result =
  let* (prefix, tail_ctx) = consume_prefix ctx (List.length expected_vars) in
  (* Verify the variables match in order *)
  let* () = List.fold_left2 (fun acc (got_v, _) exp_v ->
    let* () = acc in
    if Ident.equal got_v exp_v then Ok ()
    else Error (LinearOrderViolation { expected = exp_v; got = got_v })
  ) (Ok ()) prefix expected_vars in
  Ok (prefix, tail_ctx)

(** Check that context is empty (all variables consumed) *)
let expect_empty (ctx: context) : unit check_result =
  match Ident.to_list ctx.term_vars with
    [] -> Ok ()
  | remaining -> Error (ContextNotEmpty remaining)

(** Check that a chiral type is Prd and extract the type *)
let expect_prd (ct: chiral_typ) : (typ, check_error) result =
  match ct with
    Prd (_, t) -> Ok t
  | Cns _ -> Error (ChiralityMismatch { expected_chirality = `Prd; actual = ct })

(** Check that a chiral type is Cns and extract the type *)
let expect_cns (ct: chiral_typ) : (typ, check_error) result =
  match ct with
    Cns (_, t) -> Ok t
  | Prd _ -> Error (ChiralityMismatch { expected_chirality = `Cns; actual = ct })

(** Expect a type to be a signature *)
let expect_sgn (t: typ) (subs: subst) : (Path.t * typ list, check_error) result =
  match apply_subst subs t with
    Sgn (name, args) -> Ok (name, args)
  | t' -> Error (ExpectedSignature t')

(** Apply a type substitution to all variable types in a context.
    Used for GADT refinement. Preserves ordering. *)
let refine_context (subst: typ Ident.tbl) (ctx: context) : context =
  let refine_chiral ct = chiral_map (apply_fresh_subst subst) ct in
  let vars_list = Ident.to_list ctx.term_vars in
  let refined = List.map (fun (v, ct) -> (v, refine_chiral ct)) vars_list in
  { ctx with term_vars = Ident.of_list refined }

(* ========================================================================= *)
(* Xtor Instantiation                                                        *)
(* ========================================================================= *)

(** Freshen an xtor's type parameters for pattern matching.
    Both quantified and existential parameters become existentially bound when matching.
    Returns: (fresh_metas, inst_args, inst_main) where fresh_metas maps original params to fresh TMetas *)
let freshen_xtor_type_params (xtor: xtor)
    : (Ident.t list * chiral_typ list * typ) =
  let all_params = xtor.quantified @ xtor.existentials in
  let fresh_metas_with_kinds, subst = freshen_meta all_params in
  let fresh_metas = List.map fst fresh_metas_with_kinds in
  let inst_args =
    List.map (chiral_map (apply_fresh_subst subst))
      xtor.argument_types in
  let inst_main = apply_fresh_subst subst xtor.main in
  (fresh_metas, inst_args, inst_main)

(* ========================================================================= *)
(* Branch Checking                                                           *)
(* ========================================================================= *)

(** Common branch checking logic with GADT refinement.
    The `build_ctx` function determines context ordering:
    - For clauses (Switch): args @ tail (xtor_bindings prepended)
    - For methods (New): captured @ args (xtor_bindings appended) *)
let check_branch_common
    (ctx: context) (dec: dec)
    (xtor_name: Path.t) (type_vars: var list) (term_vars: var list) (cmd: command)
    (check_cmd: context -> subst -> command -> unit check_result)
    (subs: subst)
    (build_ctx: context -> (var * chiral_typ) list -> context)
    : unit check_result =
  match find_xtor dec xtor_name with
    None -> Error (UnboundXtor (dec.name, xtor_name))
  | Some xtor ->
      let all_type_params = xtor.quantified @ xtor.existentials in
      let num_type_vars = List.length all_type_params in
      if List.length type_vars <> num_type_vars then
        Error (TypeVarArityMismatch {
          xtor = xtor_name; expected = num_type_vars; got = List.length type_vars })
      else if List.length term_vars <> List.length xtor.argument_types then
        Error (XtorArityMismatch {
          xtor = xtor_name
        ; expected = List.length xtor.argument_types
        ; got = List.length term_vars })
      else
        (* GADT Refinement: For types in dec.type_args that are TMetas or TVars,
           we'll include them in scrutinee_ty for unification with xtor.main. *)
        let (tvar_to_meta, scrutinee_meta_args) =
          List.fold_right (fun ty (mapping, args) ->
            match ty with
              TMeta _ -> mapping, ty :: args
            | TVar v ->
                let m = Ident.mk (Ident.name v) in
                ((v, m) :: mapping, TMeta m :: args)
            | other -> (mapping, other :: args)
          ) dec.type_args ([], [])
        in
        let scrutinee_ty = Sgn (dec.name, scrutinee_meta_args) in
        
        (* Unify xtor's result type with scrutinee type to learn GADT constraints *)
        let branch_subs = match unify xtor.main scrutinee_ty Ident.emptytbl with
            Some gadt_subs ->
              List.fold_left (fun acc (k, v) ->
                Ident.add k v acc
              ) subs (Ident.to_list gadt_subs)
          | None -> subs
        in
        
        (* Convert TVars in context to TMetas for GADT resolution *)
        let refined_ctx = if tvar_to_meta = [] then ctx else begin
          let tvar_subst = List.fold_left (fun s (orig_var, meta_var) ->
            Ident.add orig_var (TMeta meta_var) s
          ) Ident.emptytbl tvar_to_meta in
          refine_context tvar_subst ctx
        end in
        
        (* Freshen quantified params and reuse existing existentials *)
        let fresh_quant_metas, quant_subst = freshen_meta xtor.quantified in
        let fresh_quant_ids = List.map fst fresh_quant_metas in
        let existing_exist_ids = List.map fst xtor.existentials in
        let all_fresh_metas = fresh_quant_ids @ existing_exist_ids in
        
        let inst_args = List.map (chiral_map (apply_fresh_subst quant_subst)) xtor.argument_types in
        
        (* Add user_var -> fresh_meta mappings to substitution *)
        let branch_subs_with_tyvars =
          List.fold_left2 (fun s meta user_var ->
            if Ident.equal meta user_var then s
            else Ident.add user_var (TMeta meta) s
          ) branch_subs all_fresh_metas type_vars
        in
        
        (* Extend context with type vars *)
        let ctx' =
          List.fold_left2 (fun c new_v (_, k) -> extend_tyvar c new_v k)
            refined_ctx type_vars all_type_params
        in
        let xtor_bindings = List.map2 (fun v ct -> (v, ct)) term_vars inst_args in
        (* Use build_ctx to determine ordering *)
        let ctx'' = build_ctx ctx' xtor_bindings in
        check_cmd ctx'' branch_subs_with_tyvars cmd

(** Check a clause branch (for Switch).
    ORDERED: xtor args Γi prepended to tail context Γ.
    Result context: Γi, Γ (args @ tail) *)
let check_clause
    (ctx: context) (dec: dec)
    (xtor_name: Path.t) (type_vars: var list) (term_vars: var list) (cmd: command)
    (check_cmd: context -> subst -> command -> unit check_result)
    (subs: subst)
    : unit check_result =
  check_branch_common ctx dec xtor_name type_vars term_vars cmd check_cmd subs
    (fun ctx' xtor_bindings -> prepend_many ctx' xtor_bindings)

(** Check a method branch (for New).
    ORDERED: captured context Γ at head, xtor args Γi appended at tail.
    Result context: Γ, Γi (captured @ args) *)
let check_method
    (ctx: context) (dec: dec)
    (xtor_name: Path.t) (type_vars: var list) (term_vars: var list) (cmd: command)
    (check_cmd: context -> subst -> command -> unit check_result)
    (subs: subst)
    : unit check_result =
  check_branch_common ctx dec xtor_name type_vars term_vars cmd check_cmd subs
    (fun ctx' xtor_bindings -> append_many ctx' xtor_bindings)

(** Check all clauses (for Switch) and verify exhaustiveness *)
let check_clauses
    (ctx: context) (dec: dec) (branches: branch list)
    (check_cmd: context -> subst -> command -> unit check_result)
    (subs: subst)
    : unit check_result =
  let* () =
    List.fold_left (fun acc (xtor_name, type_vars, term_vars, cmd) ->
      let* _ = acc in
      check_clause ctx dec xtor_name
        type_vars term_vars cmd check_cmd subs
    ) (Ok ()) branches
  in
  let covered = List.map (fun (xtor_name, _, _, _) -> xtor_name) branches in
  let missing = List.filter_map (fun (x: xtor) ->
    if List.exists (Path.equal x.name) covered then None
    else Some x.name
  ) dec.xtors in
  if missing = [] then Ok ()
  else Error (NonExhaustiveMatch { dec_name = dec.name; missing })

(** Check all methods (for New) and verify exhaustiveness *)
let check_methods
    (ctx: context) (dec: dec) (branches: branch list)
    (check_cmd: context -> subst -> command -> unit check_result)
    (subs: subst)
    : unit check_result =
  let* () =
    List.fold_left (fun acc (xtor_name, type_vars, term_vars, cmd) ->
      let* _ = acc in
      check_method ctx dec xtor_name
        type_vars term_vars cmd check_cmd subs
    ) (Ok ()) branches
  in
  let covered = List.map (fun (xtor_name, _, _, _) -> xtor_name) branches in
  let missing = List.filter_map (fun (x: xtor) ->
    if List.exists (Path.equal x.name) covered then None
    else Some x.name
  ) dec.xtors in
  if missing = [] then Ok ()
  else Error (NonExhaustiveMatch { dec_name = dec.name; missing })

(* ========================================================================= *)
(* Command Type Checking                                                     *)
(* ========================================================================= *)

(** Check a command under a context, threading substitution.
    The linear/ordered typing discipline is enforced:
    - Variables are consumed in order from the head (prefix)
    - SUBSTITUTE is the only place for weakening, contraction, exchange
    - Primitives (Axiom, Add, Sub) don't consume their operands *)
let rec check_command (ctx: context) (subs: subst) (cmd: command)
    : unit check_result =
  match cmd with
  (* let v = m(xi's); s
    
    Γ, Γ0 ⊢ let v = m(Γ0); s  where Γ, v : prd T ⊢ s
    
    ORDERED: Γ0 is the prefix (head) of context.
    Consume Γ0 from prefix, check body with v prepended to remaining Γ. *)
    Let (v, dec, xtor_name, term_vars, body) ->
      (match find_xtor dec xtor_name with
        None -> Error (UnboundXtor (dec.name, xtor_name))
      | Some xtor ->
          let _, inst_args, inst_main = freshen_xtor_type_params xtor in
          if List.length term_vars <> List.length inst_args then
            Error (XtorArityMismatch
              { xtor = xtor_name
              ; expected = List.length inst_args
              ; got = List.length term_vars
              })
          else
            (* ORDERED: Consume Γ0 from prefix (head) of context *)
            let* (prefix_bindings, tail_ctx) = consume_prefix_vars ctx term_vars in
            (* Verify types match *)
            let* subs' = check_bindings_against_types prefix_bindings inst_args subs in
            let v_typ = Prd (Lin, inst_main) in
            (* ORDERED: Prepend v at head of tail Γ *)
            check_command (prepend tail_ctx v v_typ) subs' body)

  (* switch v {...}
     
    Γ, v : prd T ⊢ switch v {m1(Γ1) ⇒ s1, ...}
    where each branch: Γ, Γi ⊢ si
    
    ORDERED: v is at head of context.
    Consume v, each branch gets Γi prepended to Γ. *)
  | Switch (v, dec, branches) ->
      (* ORDERED: Consume v from head *)
      let* (v_ct, tail_ctx) = consume_head_var ctx v in
      let* v_ty = expect_prd v_ct in
      let resolved_v_ty = apply_subst subs v_ty in
      let actual_type_args = match resolved_v_ty with
          Sgn (_, args) -> args
        | _ -> dec.type_args
      in
      let unified_dec = { dec with type_args = actual_type_args } in
      let expected_ty = Sgn (dec.name, dec.type_args) in
      (match unify v_ty expected_ty subs with
        None -> Error (UnificationFailed (v_ty, expected_ty))
      | Some subs' ->
          (* ORDERED: Clauses get Γi prepended to Γ (args @ tail) *)
          check_clauses tail_ctx unified_dec branches check_command subs')

  (* new v = (Γ0){...}; s
     
    Γ, Γ0 ⊢ new v = (Γ0){m1(Γ1) ⇒ s1, ...}; s
    where each branch: Γ0, Γ1 ⊢ si  (captured @ args)
    and continuation: Γ, v : cns T ⊢ s
    
    ORDERED: Methods get Γ0 (captured) at head, Γi (args) at tail. *)
  | New (v, dec, branches, body) ->
      (* Check methods with captured context at head, args at tail *)
      let* _ =
        check_methods ctx dec branches check_command subs
      in
      let v_typ = Cns (Lin, Sgn (dec.name, dec.type_args)) in
      (* ORDERED: Prepend v at head *)
      check_command (prepend ctx v v_typ) subs body

  (* invoke v m(xi's)
    
    v : cns T, Γ ⊢ invoke v m(Γ)
    
    ORDERED: v is at head, Γ (method args) follows.
    Consume v from head, then consume args Γ. *)
  | Invoke (v, dec, xtor_name, term_vars) ->
      (match find_xtor dec xtor_name with
        None -> Error (UnboundXtor (dec.name, xtor_name))
      | Some xtor ->
          let _, inst_args, _ = freshen_xtor_type_params xtor in
          (* ORDERED: Consume v from head first *)
          let* (v_ct, tail_ctx) = consume_head_var ctx v in
          (match expect_cns v_ct with
            Error e -> Error e
          | Ok v_ty ->
              let expected_ty = Sgn (dec.name, dec.type_args) in
              let* subs' = (match unify v_ty expected_ty subs with
                None -> Error (UnificationFailed (v_ty, expected_ty))
              | Some s -> Ok s) in
              (* ORDERED: Then consume method args Γ *)
              let* (arg_bindings, _final_ctx) = consume_prefix_vars tail_ctx term_vars in
              let* _ = check_bindings_against_types arg_bindings inst_args subs' in
              Ok ()))

  (* substitute [v'₁ → v₁, ...]; s
    The only place where weakening, contraction, and exchange can occur.
    Creates a new ordered context Γ' with the substituted bindings for s. *)
  | Substitute (mapping, body) ->
      (* Build new ordered context from the substitution mapping.
        Each (v', v) means: take type of v from current ctx, bind as v' in new ctx.
        The order of mapping determines the order of the new context. *)
      let* new_bindings = List.fold_left (fun acc (v', v) ->
        let* bindings = acc in
        let* ct = lookup_var ctx v in
        Ok (bindings @ [(v', ct)])  (* Append to preserve order *)
      ) (Ok []) mapping in
      let ctx' = { ctx with term_vars = Ident.of_list new_bindings } in
      check_command ctx' subs body

    (* jump l(args)
       
      Θ(l) = Γ means the current context must exactly match the label's expected context.
      ORDERED: args must match def.term_params in order. *)
  | Jump (label, args) ->
      let* def = lookup_def ctx label in
      if List.length args <> List.length def.term_params then
        Error (ArityMismatch {
          expected = List.length def.term_params;
          got = List.length args
        })
      else
        (* ORDERED: Consume args from prefix in order and verify types *)
        let* (prefix_bindings, tail_ctx) = consume_prefix_vars ctx args in
        let* _ = check_bindings_against_types prefix_bindings 
                   (List.map snd def.term_params) subs in
        (* ORDERED: Context should be empty after consuming all args *)
        expect_empty tail_ctx

  (* Primitives for external types - these do NOT consume their operands *)

  (* ⟨v | k⟩ at ty - cut between producer and consumer *)
  | Axiom (ty, v, k) ->
      let* v_ct = lookup_var ctx v in
      let* k_ct = lookup_var ctx k in
      let* v_ty = expect_prd v_ct in
      (match expect_cns k_ct with
        Error e -> Error e
      | Ok k_ty ->
      (match unify v_ty (Ext ty) subs with
        None -> Error (UnificationFailed (v_ty, Ext ty))
      | Some subs' ->
          (match unify k_ty (Ext ty) subs' with
            None -> Error (UnificationFailed (k_ty, Ext ty))
          | Some _ -> Ok ())))

  (* lit n { v => s } - introduces v : Prd Int at head *)
  | Lit (_, v, body) ->
      let v_typ = Prd (Unr, Ext Int) in
      check_command (prepend ctx v v_typ) subs body

  (* add(x, y) { v => s } - doesn't consume x, y; introduces v : Prd Int at head *)
  | Add (x, y, v, body) ->
      let* x_ct = lookup_var ctx x in
      let* y_ct = lookup_var ctx y in
      let* x_ty = expect_prd x_ct in
      let* y_ty = expect_prd y_ct in
      let int_ty = Ext Int in
      (match unify x_ty int_ty subs with
        None -> Error (UnificationFailed (x_ty, int_ty))
      | Some subs' ->
          (match unify y_ty int_ty subs' with
            None -> Error (UnificationFailed (y_ty, int_ty))
          | Some subs'' ->
              let v_typ = Prd (Unr, int_ty) in
              check_command (prepend ctx v v_typ) subs'' body))

  (* sub(x, y) { v => s } - doesn't consume x, y; introduces v : Prd Int at head *)
  | Sub (x, y, v, body) ->
      let* x_ct = lookup_var ctx x in
      let* y_ct = lookup_var ctx y in
      let* x_ty = expect_prd x_ct in
      let* y_ty = expect_prd y_ct in
      let int_ty = Ext Int in
      (match unify x_ty int_ty subs with
        None -> Error (UnificationFailed (x_ty, int_ty))
      | Some subs' ->
          (match unify y_ty int_ty subs' with
            None -> Error (UnificationFailed (y_ty, int_ty))
          | Some subs'' ->
              let v_typ = Prd (Unr, int_ty) in
              check_command (prepend ctx v v_typ) subs'' body))

  (* mul(x, y) { v => s } - doesn't consume x, y; introduces v : Prd Int at head *)
  | Mul (x, y, v, body) ->
      let* x_ct = lookup_var ctx x in
      let* y_ct = lookup_var ctx y in
      let* x_ty = expect_prd x_ct in
      let* y_ty = expect_prd y_ct in
      let int_ty = Ext Int in
      (match unify x_ty int_ty subs with
        None -> Error (UnificationFailed (x_ty, int_ty))
      | Some subs' ->
          (match unify y_ty int_ty subs' with
            None -> Error (UnificationFailed (y_ty, int_ty))
          | Some subs'' ->
              let v_typ = Prd (Unr, int_ty) in
              check_command (prepend ctx v v_typ) subs'' body))

  (* div(x, y) { v => s } - doesn't consume x, y; introduces v : Prd Int at head *)
  | Div (x, y, v, body) ->
      let* x_ct = lookup_var ctx x in
      let* y_ct = lookup_var ctx y in
      let* x_ty = expect_prd x_ct in
      let* y_ty = expect_prd y_ct in
      let int_ty = Ext Int in
      (match unify x_ty int_ty subs with
        None -> Error (UnificationFailed (x_ty, int_ty))
      | Some subs' ->
          (match unify y_ty int_ty subs' with
            None -> Error (UnificationFailed (y_ty, int_ty))
          | Some subs'' ->
              let v_typ = Prd (Unr, int_ty) in
              check_command (prepend ctx v v_typ) subs'' body))

  (* rem(x, y) { v => s } - doesn't consume x, y; introduces v : Prd Int at head *)
  | Rem (x, y, v, body) ->
      let* x_ct = lookup_var ctx x in
      let* y_ct = lookup_var ctx y in
      let* x_ty = expect_prd x_ct in
      let* y_ty = expect_prd y_ct in
      let int_ty = Ext Int in
      (match unify x_ty int_ty subs with
        None -> Error (UnificationFailed (x_ty, int_ty))
      | Some subs' ->
          (match unify y_ty int_ty subs' with
            None -> Error (UnificationFailed (y_ty, int_ty))
          | Some subs'' ->
              let v_typ = Prd (Unr, int_ty) in
              check_command (prepend ctx v v_typ) subs'' body))

  (* new k = { v => s1 }; s2 - Int consumer binding *)
  | NewInt (k, v, branch_body, cont) ->
      let int_ty = Ext Int in
      (* Branch: v prepended at head *)
      let* _ = check_command (prepend ctx v (Prd (Unr, int_ty))) subs branch_body in
      (* Continuation: k prepended at head *)
      check_command (prepend ctx k (Cns (Lin, int_ty))) subs cont

  (* ifz(v) { then; else } - doesn't consume v *)
  | Ifz (v, then_cmd, else_cmd) ->
      let* v_ct = lookup_var ctx v in
      let* v_ty = expect_prd v_ct in
      let int_ty = Ext Int in
      (match unify v_ty int_ty subs with
        None -> Error (UnificationFailed (v_ty, int_ty))
      | Some subs' ->
          let* _ = check_command ctx subs' then_cmd in
          check_command ctx subs' else_cmd)

  (* ret τ v - returns the value v *)
  | Ret (ty, v) ->
      let* v_ct = lookup_var ctx v in
      let v_ty = strip_chirality v_ct in
      (match unify v_ty ty subs with
        None -> Error (UnificationFailed (v_ty, ty))
      | Some _ -> Ok ())

  | End -> Ok ()

  (* Destination primitives *)

  (* let (v, d) = alloc{T}; s

    Γ, v: prd[ω] τ, d: prd[1] dest(τ) ⊢ s
    ------------------------------------- [ALLOC]
    Γ ⊢ let (v, d) = alloc{T}; s

    Creates uninitialized v and destination d. d is at head, v next. *)
  | Alloc (v, d, ty, body) ->
      let v_typ = Prd (Unr, ty) in
      let d_typ = Prd (Lin, Dest ty) in
      (* d at head, v second *)
      let ctx1 = prepend ctx v v_typ in
      let ctx2 = prepend ctx1 d d_typ in
      check_command ctx2 subs body

  (* fill d v; s

    Γ ⊢ s
    ----------------------------------------------- [FILL]
    Γ, v: prd[ω] τ, d: prd[1] dest(τ) ⊢ fill d v; s

    Consumes d and v, filling destination d with value v. *)
  | Fill (d, v, _ty, body) ->
      (* d is at head, v is second *)
      let* (d_ct, ctx1) = consume_head_var ctx d in
      let* d_ty = expect_prd d_ct in
      let* (v_ct, ctx2) = consume_head_var ctx1 v in
      let* v_ty = expect_prd v_ct in
      (* d_ty should be Dest(inner_ty) where inner_ty = v_ty *)
      (match d_ty with
        Dest inner_ty ->
          (match unify inner_ty v_ty subs with
            None -> Error (UnificationFailed (inner_ty, v_ty))
          | Some subs' -> check_command ctx2 subs' body)
      | _ -> Error (UnificationFailed (d_ty, Dest v_ty)))

  (* let (xi) = unfold d m; s

    m(prd[1] τ_i) constructor of τ
    Γ, (xi: prd[1] dest(τi)) ⊢ s
    ------------------------------------------- [UNFOLD]
    Γ, d: prd[1] dest(τ) ⊢ let (xi) = unfold d m; s

    Consumes d, introduces subdestinations xi for constructor m's arguments. *)
  | Unfold (xi_vars, d, dec, xtor_name, body) ->
      (* d is at head *)
      let* (d_ct, tail_ctx) = consume_head_var ctx d in
      let* d_ty = expect_prd d_ct in
      (* d_ty should be Dest(Sgn(...)) *)
      let* _sgn_ty = (match d_ty with
          Dest (Sgn (_, _) as s) -> Ok s
        | _ -> Error (ExpectedSignature d_ty)) in
      (* Find xtor m in dec *)
      (match find_xtor dec xtor_name with
        None -> Error (UnboundXtor (dec.name, xtor_name))
      | Some xtor ->
          if List.length xi_vars <> List.length xtor.argument_types then
            Error (XtorArityMismatch
              { xtor = xtor_name
              ; expected = List.length xtor.argument_types
              ; got = List.length xi_vars })
          else
            (* Each xi gets type prd[1] dest(τi) where τi is the arg type *)
            let xi_bindings = List.map2 (fun xi arg_ct ->
              let arg_ty = strip_chirality arg_ct in
              (xi, Prd (Lin, Dest arg_ty))
            ) xi_vars xtor.argument_types in
            (* xi's are prepended at head of tail context *)
            let new_ctx = prepend_many tail_ctx xi_bindings in
            check_command new_ctx subs body)

(** Helper: check that consumed bindings match expected xtor argument types *)
and check_bindings_against_types 
    (bindings: (var * chiral_typ) list) 
    (expected: chiral_typ list) 
    (subs: subst)
    : subst check_result =
  let rec check subs bindings expected =
    match bindings, expected with
      [], [] -> Ok subs
    | (_, got_ct) :: bs, exp_ct :: es ->
        let got_ty = strip_chirality got_ct in
        let exp_ty = strip_chirality exp_ct in
        (match unify got_ty exp_ty subs with
          None -> Error (UnificationFailed (got_ty, exp_ty))
        | Some subs' ->
            (* Also check chirality matches *)
            (match exp_ct, got_ct with
              Prd _, Prd _ | Cns _, Cns _ -> check subs' bs es
            | _ ->
                Error (ChiralityMismatch
                { expected_chirality =
                    (match exp_ct with Prd _ -> `Prd | Cns _ -> `Cns)
                ; actual = got_ct
                })))
    | _ ->
      Error (ArityMismatch { expected = List.length expected; got = List.length bindings })
  in
  check subs bindings expected

(** Type check a definition.
    The definition's term_params become the initial ordered context. *)
let check_def (ctx: context) (def: definition) : definition check_result =
  let ctx' = prepend_many ctx def.term_params in
  let* _ = check_command ctx' Ident.emptytbl def.body in
  Ok def
