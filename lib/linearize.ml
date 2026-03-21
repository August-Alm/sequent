(**
  module: Linearize
  description: Translates from Focused to AXIL.

  Consider the following program in Focused. It receives an integer and
  a list and returns the same list with the integer prepended twice.

  def cons_twice(v: prd int, l0: prd list(int), k: cns list(int)) =
    let l1 = cons(v, l0);
    invoke k cons(v, l1)

  We insert an explicit substitution before each statement, where for every
  free variable in the statement we substitute this variable for itself in
  an order dictated by what variables the statement consumes. This will
  exchange and weaken variables appropriately. When a variable occurs free
  more than once, such as v here, we have to contract and rename it.

  def cons_twice(v: prd int, l0: prd list(int), k: cns list(int)) =
    substitute [v ← v, k ← k, v0 ← v, l0 ← l0];
    let l1 = cons(v0, l0);
    substitute [v ← v, l1 ← l1, k ← k];
    invoke k cons
*)

module FB = Focused.Types.FocusedBase
module FTy = Focused.Types.FocusedTypes
module FTm = Focused.Terms
module AB = Axil.Types.AxilBase
module ATy = Axil.Types.AxilTypes
module ATm = Axil.Terms

(* ========================================================================= *)
(* Type/Dec Conversion                                                       *)
(* ========================================================================= *)
(* Focused and Axil types are structurally identical, just in different modules *)

let rec convert_typ (t: FTy.typ) : ATy.typ =
  match t with
    FTy.Base _ -> ATy.Base AB.Typ
  | FTy.Arrow (t1, t2) -> ATy.Arrow (convert_typ t1, convert_typ t2)
  | FTy.Ext e -> ATy.Ext e
  | FTy.TVar v -> ATy.TVar v
  | FTy.TMeta m -> ATy.TMeta m
  | FTy.Sgn (p, args) -> ATy.Sgn (p, List.map convert_typ args)
  | FTy.PromotedCtor (d, c, args) -> 
      ATy.PromotedCtor (d, c, List.map convert_typ args)
  | FTy.Forall (v, k, body) -> 
      ATy.Forall (v, convert_typ k, convert_typ body)
  | FTy.Dest t ->
      ATy.Dest (convert_typ t)

let convert_chiral (ct: FTy.chiral_typ) : ATy.chiral_typ =
  match ct with
    FB.Prd (u, t) -> AB.Prd (u, convert_typ t) | FB.Cns (u, t) -> AB.Cns (u, convert_typ t)

let convert_xtor (x: FTy.xtor) : ATy.xtor =
  { ATy.name = x.FTy.name
  ; quantified = List.map (fun (v, k) -> (v, convert_typ k)) x.quantified
  ; existentials = List.map (fun (v, k) -> (v, convert_typ k)) x.existentials
  ; argument_types = List.map convert_chiral x.argument_types
  ; main = convert_typ x.main
  ; original_index = x.original_index
  }

let convert_dec (d: FTy.dec) : ATy.dec =
  { ATy.name = d.FTy.name
  ; data_sort = d.data_sort
  ; param_kinds = List.map convert_typ d.param_kinds
  ; type_args = List.map convert_typ d.type_args
  ; xtors = List.map convert_xtor d.xtors
  }

(* ========================================================================= *)
(* Variable Sets with Multiplicity                                           *)
(* ========================================================================= *)
(* We need to track how many times each variable is used to handle contraction *)

module VarSet = Set.Make(struct
  type t = Common.Identifiers.Ident.t
  let compare = Common.Identifiers.Ident.compare
end)

module VarMap = Map.Make(struct
  type t = Common.Identifiers.Ident.t
  let compare = Common.Identifiers.Ident.compare
end)

(* Count occurrences of each variable *)
let add_var (v: Common.Identifiers.Ident.t) (counts: int VarMap.t) : int VarMap.t =
  let n = try VarMap.find v counts with Not_found -> 0 in
  VarMap.add v (n + 1) counts

let add_vars (vs: Common.Identifiers.Ident.t list) (counts: int VarMap.t) : int VarMap.t =
  List.fold_left (fun acc v -> add_var v acc) counts vs

let merge_counts (c1: int VarMap.t) (c2: int VarMap.t) : int VarMap.t =
  VarMap.merge (fun _ a b ->
    match a, b with
      Some x, Some y -> Some (max x y)  (* For branches, take max *)
    | Some x, None -> Some x
    | None, Some y -> Some y
    | None, None -> None
  ) c1 c2

(* ========================================================================= *)
(* Free Variables                                                            *)
(* ========================================================================= *)
(* Compute free variables with multiplicities *)

let rec free_vars_cmd (cmd: FTm.command) : int VarMap.t =
  match cmd with
    FTm.Let (v, _dec, _xtor, args, body) ->
      let body_fv = free_vars_cmd body in
      let body_fv' = VarMap.remove v body_fv in
      add_vars args body_fv'
  | FTm.Switch (v, _dec, branches) ->
      let branch_fvs = List.map free_vars_branch branches in
      let merged = List.fold_left merge_counts VarMap.empty branch_fvs in
      add_var v merged
  | FTm.New (v, _dec, branches, body) ->
      let body_fv = free_vars_cmd body in
      let body_fv' = VarMap.remove v body_fv in
      let branch_fvs = List.map free_vars_branch branches in
      let merged = List.fold_left merge_counts body_fv' branch_fvs in
      merged
  | FTm.Invoke (v, _dec, _xtor, args) ->
      add_var v (add_vars args VarMap.empty)
  | FTm.Jump (_label, args) ->
      add_vars args VarMap.empty
  | FTm.Axiom (_ty, v, k) ->
      add_vars [v; k] VarMap.empty
  | FTm.Lit (_n, v, body) ->
      let body_fv = free_vars_cmd body in
      VarMap.remove v body_fv
  | FTm.NewInt (k, v, branch, cont) ->
      let branch_fv = free_vars_cmd branch in
      let branch_fv' = VarMap.remove v branch_fv in
      let cont_fv = free_vars_cmd cont in
      let cont_fv' = VarMap.remove k cont_fv in
      merge_counts branch_fv' cont_fv'
  | FTm.Add (x, y, r, body) ->
      let body_fv = free_vars_cmd body in
      let body_fv' = VarMap.remove r body_fv in
      add_vars [x; y] body_fv'
  | FTm.Sub (x, y, r, body) ->
      let body_fv = free_vars_cmd body in
      let body_fv' = VarMap.remove r body_fv in
      add_vars [x; y] body_fv'
  | FTm.Mul (x, y, r, body) ->
      let body_fv = free_vars_cmd body in
      let body_fv' = VarMap.remove r body_fv in
      add_vars [x; y] body_fv'
  | FTm.Div (x, y, r, body) ->
      let body_fv = free_vars_cmd body in
      let body_fv' = VarMap.remove r body_fv in
      add_vars [x; y] body_fv'
  | FTm.Rem (x, y, r, body) ->
      let body_fv = free_vars_cmd body in
      let body_fv' = VarMap.remove r body_fv in
      add_vars [x; y] body_fv'
  | FTm.Ifz (v, then_cmd, else_cmd) ->
      let then_fv = free_vars_cmd then_cmd in
      let else_fv = free_vars_cmd else_cmd in
      add_var v (merge_counts then_fv else_fv)
  | FTm.Ret (_ty, v) ->
      add_var v VarMap.empty
  | FTm.End ->
      VarMap.empty

  (* Destination primitives *)
  | FTm.Alloc (v, d, _ty, body) ->
      let body_fv = free_vars_cmd body in
      let body_fv' = VarMap.remove v body_fv in
      VarMap.remove d body_fv'
  | FTm.Fill (d, v, _ty, body) ->
      let body_fv = free_vars_cmd body in
      add_vars [d; v] body_fv
  | FTm.Unfold (xi_vars, d, _dec, _xtor, body) ->
      let body_fv = free_vars_cmd body in
      let body_fv' = List.fold_left (fun acc x -> VarMap.remove x acc) body_fv xi_vars in
      add_var d body_fv'

and free_vars_branch ((_, ty_vars, term_vars, body): FTm.branch) : int VarMap.t =
  let body_fv = free_vars_cmd body in
  (* Remove bound type and term variables *)
  let fv = List.fold_left (fun acc v -> VarMap.remove v acc) body_fv ty_vars in
  List.fold_left (fun acc v -> VarMap.remove v acc) fv term_vars

(* ========================================================================= *)
(* Linearization State                                                       *)
(* ========================================================================= *)

type state = 
  { fresh_counter: int ref
  ; var_types: FTy.chiral_typ Common.Identifiers.Ident.tbl
  }

let mk_state (var_types: FTy.chiral_typ Common.Identifiers.Ident.tbl) : state =
  { fresh_counter = ref 0
  ; var_types
  }

let fresh_var (st: state) (base: Common.Identifiers.Ident.t) : Common.Identifiers.Ident.t =
  let n = !(st.fresh_counter) in
  st.fresh_counter := n + 1;
  Common.Identifiers.Ident.mk (Common.Identifiers.Ident.name base ^ "_" ^ string_of_int n)

(* ========================================================================= *)
(* Substitution Generation                                                   *)
(* ========================================================================= *)
(* 
  Build a substitution that reorders the current context to put consumed
  variables at the head in the required order, followed by remaining vars.
  
  The substitution expresses: for each position in new context, which 
  variable from old context goes there.
  
  For ordered linear logic, even if names stay the same, order matters!
  We also handle contraction: if a variable is consumed but also needed
  in the continuation, we make a copy.
*)
(*
  Build reordering substitution with contraction support.
  current_ctx: the actual ordered context (list of vars in current order)
  consumed: variables that need to be at head (in required order) - will be removed after
  fv: free variables with multiplicities (for the whole command including continuations)
  continuation_fv: free variables needed AFTER the consumed vars are used
  
  Returns: (substitution, new_ctx after substitution but before consumption, copy_map)
  where copy_map maps original var -> copy var for vars that were contracted
*)
let build_reordering_with_contraction
    (st: state)
    (current_ctx: Common.Identifiers.Ident.t list)
    (consumed: Common.Identifiers.Ident.t list)
    (continuation_fv: int VarMap.t)
    : (Common.Identifiers.Ident.t * Common.Identifiers.Ident.t) list 
      * Common.Identifiers.Ident.t list
      * Common.Identifiers.Ident.t VarMap.t =
  (* Figure out which consumed vars are also needed in continuation (require contraction) *)
  let consumed_set = VarSet.of_list consumed in
  let needs_copy = VarSet.filter (fun v -> VarMap.mem v continuation_fv) consumed_set in
  
  (* For vars that need contraction, we'll create copies that go into the tail *)
  let copy_names = ref VarMap.empty in
  let get_copy_name v =
    match VarMap.find_opt v !copy_names with
      Some name -> name
    | None ->
        let name = fresh_var st v in
        copy_names := VarMap.add v name !copy_names;
        name
  in
  
  (* Build consumed part - these go at head and will be consumed *)
  let consumed_pairs = List.map (fun v -> (v, v)) consumed in
  
  (* Build tail part:
    1. First, copies of consumed vars that are also needed in continuation
    2. Then, remaining vars from context that weren't consumed *)
  let copy_pairs = VarSet.fold (fun v acc ->
    (get_copy_name v, v) :: acc
  ) needs_copy [] in
  
  let tail_pairs = List.filter_map (fun v ->
    if VarSet.mem v consumed_set then None  (* Already consumed, handled by copy_pairs if needed *)
    else if VarMap.mem v continuation_fv then Some (v, v)  (* Still needed *)
    else None  (* Weakening - drop unused *)
  ) current_ctx in
  
  let subst = consumed_pairs @ (List.rev copy_pairs) @ tail_pairs in
  let new_ctx = List.map fst subst in
  (subst, new_ctx, !copy_names)

(* Simple build_reordering without contraction - for commands where consumed vars
  don't need to survive (like Let args, Invoke args, etc.) *)
let build_reordering 
    (_st: state)
    (current_ctx: Common.Identifiers.Ident.t list)
    (consumed: Common.Identifiers.Ident.t list)
    (fv: int VarMap.t)
    : (Common.Identifiers.Ident.t * Common.Identifiers.Ident.t) list * Common.Identifiers.Ident.t list =
  let consumed_set = VarSet.of_list consumed in
  
  (* Build consumed part *)
  let consumed_pairs = List.map (fun v -> (v, v)) consumed in
  
  (* Build tail part *)
  let tail_pairs = List.filter_map (fun v ->
    if VarSet.mem v consumed_set then None
    else if VarMap.mem v fv then Some (v, v)
    else None
  ) current_ctx in
  
  let subst = consumed_pairs @ tail_pairs in
  let new_ctx = List.map fst subst in
  (subst, new_ctx)

(* Check if substitution is a no-op (identity permutation with no weakening) *)
let is_identity_reordering 
    (current_ctx: Common.Identifiers.Ident.t list)
    (subst: (Common.Identifiers.Ident.t * Common.Identifiers.Ident.t) list) : bool =
  (* Identity requires:
    1. Same length (no weakening)
    2. Same order (no exchange)
    3. Same names (no renaming for contraction) *)
  if List.length subst <> List.length current_ctx then
    false  (* Different length means weakening occurred *)
  else
    let subst_order = List.map snd subst in  (* Original var names in new order *)
    (* Check order matches and names are unchanged *)
    List.for_all2 Common.Identifiers.Ident.equal subst_order current_ctx &&
    List.for_all (fun (new_v, old_v) -> Common.Identifiers.Ident.equal new_v old_v) subst

(* Wrap command with substitution if reordering is needed *)
let wrap_with_reordering 
    (current_ctx: Common.Identifiers.Ident.t list)
    (subst: (Common.Identifiers.Ident.t * Common.Identifiers.Ident.t) list)
    (cmd: ATm.command) : ATm.command =
  if subst = [] || is_identity_reordering current_ctx subst then cmd
  else ATm.Substitute (subst, cmd)

(* Apply rename_map to a variable reference: if v is renamed, return its actual context name *)
let apply_rename (rename_map: Common.Identifiers.Ident.t VarMap.t) (v: Common.Identifiers.Ident.t) =
  match VarMap.find_opt v rename_map with
  | Some actual -> actual
  | None -> v

(* Apply rename_map to a list of variables *)
let apply_rename_list (rename_map: Common.Identifiers.Ident.t VarMap.t) (vs: Common.Identifiers.Ident.t list) =
  List.map (apply_rename rename_map) vs

(* ========================================================================= *)
(* Command Translation                                                       *)
(* ========================================================================= *)

(* rename_map: maps FTm variable names -> actual context names (for contracted copies) *)
let rec linearize_cmd (st: state) (ctx: Common.Identifiers.Ident.t list) 
    (rename_map: Common.Identifiers.Ident.t VarMap.t)
    (cmd: FTm.command) : ATm.command =
  (* Compute free vars with FTm names, then map to actual ctx names *)
  let fv_ftm = free_vars_cmd cmd in
  let fv = VarMap.fold (fun v count acc ->
    VarMap.add (apply_rename rename_map v) count acc
  ) fv_ftm VarMap.empty in
  match cmd with
  (* let v = m(args); s
    Consumes: args (in order as prefix)
    Continues with: v prepended to remaining context
    
    Important: args may be used multiple times if they have unrestricted types.
    If an arg is also free in body, we need contraction to make a copy.
    The copy stays in context but body still references original name,
    so we extend rename_map with orig -> copy for the body. *)
    FTm.Let (v, dec, xtor, args, body) ->
      (* Map FTm arg names to actual context names *)
      let actual_args = apply_rename_list rename_map args in
      let body_fv_ftm = free_vars_cmd body in
      let continuation_fv = VarMap.fold (fun v count acc ->
        if Common.Identifiers.Ident.equal v (fst (v, ())) then 
          VarMap.add (apply_rename rename_map v) count acc
        else
          VarMap.add (apply_rename rename_map v) count acc
      ) (VarMap.remove v body_fv_ftm) VarMap.empty in
      (* Use contraction if any arg is also needed in continuation *)
      let (subst, new_ctx, copy_map) = build_reordering_with_contraction st ctx actual_args continuation_fv in
      (* Extend rename_map with copy_map for body (maps FTm orig -> actual copy) *)
      let body_rename_map = VarMap.fold (fun orig copy acc ->
        VarMap.add orig copy acc
      ) copy_map rename_map in
      (* After consuming args, filter them out *)
      let args_set = VarSet.of_list actual_args in
      let body_ctx = v :: (List.filter (fun x -> not (VarSet.mem x args_set)) new_ctx) in
      let body' = linearize_cmd st body_ctx body_rename_map body in
      wrap_with_reordering ctx subst (ATm.Let (v, convert_dec dec, xtor, actual_args, body'))

  (* switch v { branches }
    Consumes: v (at head)
    Each branch gets its bound vars prepended to remaining context *)
  | FTm.Switch (v, dec, branches) ->
      let actual_v = apply_rename rename_map v in
      let (subst, new_ctx) = build_reordering st ctx [actual_v] fv in
      (* After consuming v, branches get term_vars prepended to remaining *)
      let remaining_ctx = List.filter (fun x ->
        not (Common.Identifiers.Ident.equal x actual_v)
      ) new_ctx in
      let branches' = List.map (linearize_branch st remaining_ctx rename_map) branches in
      wrap_with_reordering ctx subst (ATm.Switch (actual_v, convert_dec dec, branches'))

  (* new v = { branches }; s
    Doesn't consume from head; v prepended for continuation 
    Methods run in captured_ctx @ args *)
  | FTm.New (v, dec, branches, body) ->
      let (subst, new_ctx) = build_reordering st ctx [] fv in
      let branches' = List.map (linearize_method st new_ctx rename_map) branches in
      let body' = linearize_cmd st (v :: new_ctx) rename_map body in
      wrap_with_reordering ctx subst (ATm.New (v, convert_dec dec, branches', body'))

  (* invoke v m(args)
    Consumes: v at head, then args
    args stay at tail positions and captured env is at head *)
  | FTm.Invoke (v, dec, xtor, args) ->
      let actual_v = apply_rename rename_map v in
      let actual_args = apply_rename_list rename_map args in
      let consumed = [actual_v] @ actual_args in
      let (subst, _) = build_reordering st ctx consumed fv in
      wrap_with_reordering ctx subst (ATm.Invoke (actual_v, convert_dec dec, xtor, actual_args))

  (* jump l(args) - terminal, consumes args *)
  | FTm.Jump (label, args) ->
      let actual_args = apply_rename_list rename_map args in
      let (subst, _) = build_reordering st ctx actual_args fv in
      wrap_with_reordering ctx subst (ATm.Jump (label, actual_args))

  | FTm.Axiom (ty, v, k) ->
      let actual_v = apply_rename rename_map v in
      let actual_k = apply_rename rename_map k in
      (* Order [k; v] so that after substitute:
        - k at position 1 → r1 = X5 (this), r2 = X6 (code)  
        - v at position 0 → r2 = X4 (arg)
        This matches the calling convention for methods with 1 arg,
        so CAxiom only needs to save code ptr and branch. *)
      let (subst, _) = build_reordering st ctx [actual_k; actual_v] fv in
      wrap_with_reordering ctx subst (ATm.Axiom (ty, actual_v, actual_k))

  | FTm.Lit (n, v, body) ->
      let (subst, new_ctx) = build_reordering st ctx [] fv in
      let body' = linearize_cmd st (v :: new_ctx) rename_map body in
      wrap_with_reordering ctx subst (ATm.Lit (n, v, body'))

  | FTm.Add (x, y, r, body) ->
      let actual_x = apply_rename rename_map x in
      let actual_y = apply_rename rename_map y in
      (* Add does NOT consume x and y - unrestricted discipline for primitives.
        Just need x, y present in context; r is prepended for body *)
      let (subst, new_ctx) = build_reordering st ctx [] fv in
      let body' = linearize_cmd st (r :: new_ctx) rename_map body in
      wrap_with_reordering ctx subst (ATm.Add (actual_x, actual_y, r, body'))

  | FTm.Sub (x, y, r, body) ->
      let actual_x = apply_rename rename_map x in
      let actual_y = apply_rename rename_map y in
      (* Sub does NOT consume x and y - unrestricted discipline for primitives *)
      let (subst, new_ctx) = build_reordering st ctx [] fv in
      let body' = linearize_cmd st (r :: new_ctx) rename_map body in
      wrap_with_reordering ctx subst (ATm.Sub (actual_x, actual_y, r, body'))

  | FTm.Mul (x, y, r, body) ->
      let actual_x = apply_rename rename_map x in
      let actual_y = apply_rename rename_map y in
      (* Mul does NOT consume x and y - unrestricted discipline for primitives *)
      let (subst, new_ctx) = build_reordering st ctx [] fv in
      let body' = linearize_cmd st (r :: new_ctx) rename_map body in
      wrap_with_reordering ctx subst (ATm.Mul (actual_x, actual_y, r, body'))

  | FTm.Div (x, y, r, body) ->
      let actual_x = apply_rename rename_map x in
      let actual_y = apply_rename rename_map y in
      (* Div does NOT consume x and y - unrestricted discipline for primitives *)
      let (subst, new_ctx) = build_reordering st ctx [] fv in
      let body' = linearize_cmd st (r :: new_ctx) rename_map body in
      wrap_with_reordering ctx subst (ATm.Div (actual_x, actual_y, r, body'))

  | FTm.Rem (x, y, r, body) ->
      let actual_x = apply_rename rename_map x in
      let actual_y = apply_rename rename_map y in
      (* Rem does NOT consume x and y - unrestricted discipline for primitives *)
      let (subst, new_ctx) = build_reordering st ctx [] fv in
      let body' = linearize_cmd st (r :: new_ctx) rename_map body in
      wrap_with_reordering ctx subst (ATm.Rem (actual_x, actual_y, r, body'))

  | FTm.NewInt (k, v, branch, cont) ->
      let (subst, new_ctx) = build_reordering st ctx [] fv in
      let branch' = linearize_cmd st (v :: new_ctx) rename_map branch in
      let cont' = linearize_cmd st (k :: new_ctx) rename_map cont in
      wrap_with_reordering ctx subst (ATm.NewInt (k, v, branch', cont'))

  | FTm.Ifz (v, then_cmd, else_cmd) ->
      let actual_v = apply_rename rename_map v in
      (* Ifz does NOT consume v - unrestricted discipline for primitives.
        Both branches get the same context with v still present *)
      let (subst, new_ctx) = build_reordering st ctx [] fv in
      let then' = linearize_cmd st new_ctx rename_map then_cmd in
      let else' = linearize_cmd st new_ctx rename_map else_cmd in
      wrap_with_reordering ctx subst (ATm.Ifz (actual_v, then', else'))

  (* Destination primitives *)
  | FTm.Alloc (v, d, ty, body) ->
      (* Nothing consumed; d and v are bound for body (d at head, v second) *)
      let (subst, new_ctx) = build_reordering st ctx [] fv in
      let body' = linearize_cmd st (d :: v :: new_ctx) rename_map body in
      wrap_with_reordering ctx subst (ATm.Alloc (v, d, convert_typ ty, body'))

  | FTm.Fill (d, v, ty, body) ->
      let actual_d = apply_rename rename_map d in
      let actual_v = apply_rename rename_map v in
      (* d is linear (consumed), v is also consumed (value is stored) *)
      let consumed = [actual_d; actual_v] in
      let (subst, new_ctx) = build_reordering st ctx consumed fv in
      let consumed_set = VarSet.of_list consumed in
      let remaining_ctx = List.filter (fun x ->
        not (VarSet.mem x consumed_set)
      ) new_ctx in
      let body' = linearize_cmd st remaining_ctx rename_map body in
      wrap_with_reordering ctx subst (ATm.Fill (actual_d, actual_v, convert_typ ty, body'))

  | FTm.Unfold (xi_vars, d, dec, xtor, body) ->
      let actual_d = apply_rename rename_map d in
      (* d is linear (consumed); xi_vars are bound for body *)
      let (subst, new_ctx) = build_reordering st ctx [actual_d] fv in
      let remaining_ctx = List.filter (fun x ->
        not (Common.Identifiers.Ident.equal x actual_d)
      ) new_ctx in
      let body' = linearize_cmd st (xi_vars @ remaining_ctx) rename_map body in
      wrap_with_reordering ctx subst (ATm.Unfold (xi_vars, actual_d, convert_dec dec, xtor, body'))

  | FTm.Ret (ty, v) ->
      let actual_v = apply_rename rename_map v in
      let (subst, _) = build_reordering st ctx [actual_v] fv in
      wrap_with_reordering ctx subst (ATm.Ret (convert_typ ty, actual_v))

  | FTm.End ->
      ATm.End

and linearize_branch (st: state) (ctx: Common.Identifiers.Ident.t list) 
    (rename_map: Common.Identifiers.Ident.t VarMap.t)
    ((xtor, ty_vars, term_vars, body): FTm.branch) : ATm.branch =
  (* Branch context for clauses: term_vars prepended to ctx (args @ tail) *)
  let branch_ctx = term_vars @ ctx in
  let body' = linearize_cmd st branch_ctx rename_map body in
  (xtor, ty_vars, term_vars, body')

(** Linearize a method branch for New (codata).
    Method body runs in captured @ args.
    This is ctx @ term_vars where ctx is the captured context. *)
and linearize_method (st: state) (captured_ctx: Common.Identifiers.Ident.t list) 
    (rename_map: Common.Identifiers.Ident.t VarMap.t)
    ((xtor, ty_vars, term_vars, body): FTm.branch) : ATm.branch =
  (* Method context: captured_ctx @ term_vars (as ++ cs) *)
  let branch_ctx = captured_ctx @ term_vars in
  let body' = linearize_cmd st branch_ctx rename_map body in
  (xtor, ty_vars, term_vars, body')

(* ========================================================================= *)
(* Definition Translation                                                    *)
(* ========================================================================= *)

let linearize_def (fdef: FTm.definition) : ATm.definition =
  let var_types = List.fold_left (fun tbl (v, ct) ->
    Common.Identifiers.Ident.add v ct tbl
  ) Common.Identifiers.Ident.emptytbl fdef.term_params in
  let st = mk_state var_types in
  let ctx_vars = List.map fst fdef.term_params in
  let body' = linearize_cmd st ctx_vars VarMap.empty fdef.body in
  { ATm.path = fdef.path
  ; term_params = List.map (fun (v, ct) -> (v, convert_chiral ct)) fdef.term_params
  ; body = body'
  }