(** 
  This file contains a focusing normalization algorithm mapping a
  polarized Source sequent calculus with user-defined type, down to
  a Target language with eight statement form and no relations:
   
  ⟨C(Γ) | µ˜x.s⟩                 & ⟨µα.s |D(Γ)⟩
  ⟨x | case {C(Γ) ⇒ s, ... }⟩    & ⟨cocase {D(Γ) ⇒ s, ... } | α⟩
  ⟨µα.s | case {C(Γ) ⇒ s, ... }⟩ & ⟨cocase {D(Γ) ⇒ s, ... } | µ˜x.s⟩
  ⟨C(Γ) | α⟩                     & ⟨x | D(Γ)⟩
*)

open Common.Identifiers

(* ========================================================================= *)
(* Types (Object Language)                                                   *)
(* ========================================================================= *)

type signature = chiral_tpe list list

and tpe =
  | Pos of signature
  | Neg of signature

and chiral_tpe =
  | Lhs of tpe
  | Rhs of tpe

(* ========================================================================= *)
(* Substitutions (Renamings)                                                 *)
(* ========================================================================= *)

module Sub = struct
  (** A substitution is a finite map from identifiers to identifiers *)
  type t = Ident.t Ident.tbl

  let empty : t = Ident.emptytbl

  let add (x : Ident.t) (y : Ident.t) (s : t) : t = 
    Ident.add x y s

  let apply (s : t) (x : Ident.t) : Ident.t =
    match Ident.find_opt x s with
    | Some y -> y
    | None -> x
end

(* ========================================================================= *)
(* Source Language                                                           *)
(* ========================================================================= *)

module Source = struct

  type command =
    | CutPos of signature * term * term
    | CutNeg of signature * term * term
    | End

  and term =
    | Variable of Ident.t
    | Constructor of signature * int * term list
    | Match of signature * branch list
    | Comatch of signature * branch list
    | Destructor of signature * int * term list
    | MuLhsPos of signature * Ident.t * command
    | MuRhsPos of signature * Ident.t * command
    | MuLhsNeg of signature * Ident.t * command
    | MuRhsNeg of signature * Ident.t * command

  and branch = Clause of Ident.t list * command

  (** Apply renaming to a command *)
  let rec rename_command (h : Sub.t) : command -> command = function
    | CutPos (sig_, lhs, rhs) -> 
        CutPos (sig_, rename_term h lhs, rename_term h rhs)
    | CutNeg (sig_, lhs, rhs) -> 
        CutNeg (sig_, rename_term h lhs, rename_term h rhs)
    | End -> End

  and rename_term (h : Sub.t) : term -> term = function
    | Variable x -> Variable (Sub.apply h x)
    | Constructor (sig_, n, args) -> 
        Constructor (sig_, n, List.map (rename_term h) args)
    | Match (sig_, branches) -> 
        Match (sig_, List.map (rename_branch h) branches)
    | Comatch (sig_, branches) -> 
        Comatch (sig_, List.map (rename_branch h) branches)
    | Destructor (sig_, n, args) -> 
        Destructor (sig_, n, List.map (rename_term h) args)
    | MuLhsPos (sig_, x, cmd) ->
        let x' = Ident.fresh () in
        MuLhsPos (sig_, x', rename_command (Sub.add x x' h) cmd)
    | MuRhsPos (sig_, x, cmd) ->
        let x' = Ident.fresh () in
        MuRhsPos (sig_, x', rename_command (Sub.add x x' h) cmd)
    | MuLhsNeg (sig_, a, cmd) ->
        let a' = Ident.fresh () in
        MuLhsNeg (sig_, a', rename_command (Sub.add a a' h) cmd)
    | MuRhsNeg (sig_, a, cmd) ->
        let a' = Ident.fresh () in
        MuRhsNeg (sig_, a', rename_command (Sub.add a a' h) cmd)

  and rename_branch (h : Sub.t) (Clause (params, body)) : branch =
    let params' = List.map (fun _ -> Ident.fresh ()) params in
    let h' = List.fold_left2 (fun acc p p' -> Sub.add p p' acc) h params params' in
    Clause (params', rename_command h' body)
end

(* ========================================================================= *)
(* Target Language                                                           *)
(* ========================================================================= *)

module Target = struct

  type command =
    | LetConstructor of signature * int * Ident.t list * Ident.t * command  (** [⟨Cₙ(Γ) | μ̃x.s⟩] *)
    | LetMatch of signature * branch list * Ident.t * command  (** [⟨μα.s | case \{C₁(Γ₁) ⇒ s₁; …\}⟩] *)
    | LetComatch of signature * branch list * Ident.t * command  (** [⟨cocase \{D₁(Γ₁) ⇒ s₁; …\} | μ̃x.s⟩] *)
    | LetDestructor of signature * int * Ident.t list * Ident.t * command  (** [⟨μα.s | Dₙ(Γ)⟩] *)
    | CutConstructor of signature * int * Ident.t list * Ident.t  (** [⟨Cₙ(Γ) | α⟩] *)
    | CutMatch of signature * Ident.t * branch list  (** [⟨x | case \{C₁(Γ₁) ⇒ s₁; …\}⟩] *)
    | CutComatch of signature * branch list * Ident.t  (** [⟨cocase \{D₁(Γ₁) ⇒ s₁; …\} | α⟩] *)
    | CutDestructor of signature * Ident.t * int * Ident.t list  (** [⟨x | Dₙ(Γ)⟩] *)
    | End  (** Terminal / halt *)

  and branch = Clause of Ident.t list * command

  (** Apply renaming to a command *)
  let rec rename_command (h : Sub.t) : command -> command = function
    | LetConstructor (sig_, n, args, x, cont) ->
        let x' = Ident.fresh () in
        LetConstructor (sig_, n, List.map (Sub.apply h) args, x',
          rename_command (Sub.add x x' h) cont)
    | LetMatch (sig_, branches, x, cont) ->
        let x' = Ident.fresh () in
        LetMatch (sig_, List.map (rename_branch h) branches, x',
          rename_command (Sub.add x x' h) cont)
    | LetComatch (sig_, branches, a, cont) ->
        let a' = Ident.fresh () in
        LetComatch (sig_, List.map (rename_branch h) branches, a',
          rename_command (Sub.add a a' h) cont)
    | LetDestructor (sig_, n, args, a, cont) ->
        let a' = Ident.fresh () in
        LetDestructor (sig_, n, List.map (Sub.apply h) args, a',
          rename_command (Sub.add a a' h) cont)
    | CutConstructor (sig_, n, args, a) ->
        CutConstructor (sig_, n, List.map (Sub.apply h) args, Sub.apply h a)
    | CutMatch (sig_, x, branches) ->
        CutMatch (sig_, Sub.apply h x, List.map (rename_branch h) branches)
    | CutComatch (sig_, branches, a) ->
        CutComatch (sig_, List.map (rename_branch h) branches, Sub.apply h a)
    | CutDestructor (sig_, x, n, args) ->
        CutDestructor (sig_, Sub.apply h x, n, List.map (Sub.apply h) args)
    | End -> End

  and rename_branch (h : Sub.t) (Clause (params, body)) : branch =
    let params' = List.map (fun _ -> Ident.fresh ()) params in
    let h' = List.fold_left2 (fun acc p p' -> Sub.add p p' acc) h params params' in
    Clause (params', rename_command h' body)
end

(* ========================================================================= *)
(* Transformation                                                            *)
(* ========================================================================= *)

module Transform = struct
  open Source

  (** Generate fresh parameter names from a parameter spec *)
  let fresh_params (ps : 'a list) : Ident.t list =
    List.map (fun _ -> Ident.fresh ()) ps

  (** Lookup and inline the n-th branch body, substituting arg_vars for params *)
  let lookup_branch_body (branches : Target.branch list) (n : int) 
      (arg_vars : Ident.t list) : Target.command =
    match List.nth_opt branches n with
    | Some (Target.Clause (params, body)) ->
        let sub = List.fold_left2 (fun acc p v -> Sub.add p v acc) 
                    Sub.empty params arg_vars in
        Target.rename_command sub body
    | None -> Target.End

  (** Build target branches from a signature using a builder function *)
  let build_branches_from_sig (sig_ : signature) 
      (build : Ident.t list -> int -> Target.command) : Target.branch list =
    List.mapi (fun idx ps ->
      let params = fresh_params ps in
      Target.Clause (params, build params idx)
    ) sig_

  (** Transform source branches to target branches *)
  let rec transform_source_branches (branches : Source.branch list) 
      (h : Sub.t) : Target.branch list =
    List.map (fun (Clause (params, body)) ->
      let params' = fresh_params params in
      let h' = List.fold_left2 (fun acc p p' -> Sub.add p p' acc) h params params' in
      Target.Clause (params', transform_command body h')
    ) branches

  (** Bind a single term, calling continuation with the resulting variable *)
  and bind_term (term : Source.term) (h : Sub.t) 
      (k : Ident.t -> Target.command) : Target.command =
    match term with
    | Variable x -> 
        k (Sub.apply h x)

    | Constructor (sig_, n, args) ->
        bind_terms args h (fun arg_vars ->
          let x = Ident.fresh () in
          Target.LetConstructor (sig_, n, arg_vars, x, k x))

    | Match (sig_, bs) ->
        let x = Ident.fresh () in
        Target.LetMatch (sig_, transform_source_branches bs h, x, k x)

    | Comatch (sig_, bs) ->
        let a = Ident.fresh () in
        Target.LetComatch (sig_, transform_source_branches bs h, a, k a)

    | Destructor (sig_, n, args) ->
        bind_terms args h (fun arg_vars ->
          let a = Ident.fresh () in
          Target.LetDestructor (sig_, n, arg_vars, a, k a))

    | MuLhsPos (sig_, x, s) ->
        let bound = Ident.fresh () in
        Target.LetMatch (sig_,
          build_branches_from_sig sig_ (fun params n ->
            Target.LetConstructor (sig_, n, params, bound, k bound)),
          x,
          transform_command s (Sub.add x x h))

    | MuRhsPos (sig_, a, s) ->
        let bound = Ident.fresh () in
        Target.LetMatch (sig_,
          build_branches_from_sig sig_ (fun params n ->
            let a' = Ident.fresh () in
            Target.LetConstructor (sig_, n, params, a',
              transform_command s (Sub.add a a' h))),
          bound,
          k bound)

    | MuLhsNeg (sig_, a, s) ->
        let bound = Ident.fresh () in
        Target.LetComatch (sig_,
          build_branches_from_sig sig_ (fun params n ->
            let a' = Ident.fresh () in
            Target.LetDestructor (sig_, n, params, a',
              transform_command s (Sub.add a a' h))),
          bound,
          k bound)

    | MuRhsNeg (sig_, x, s) ->
        let bound = Ident.fresh () in
        Target.LetComatch (sig_,
          build_branches_from_sig sig_ (fun params n ->
            Target.LetDestructor (sig_, n, params, bound, k bound)),
          x,
          transform_command s (Sub.add x x h))

  (** Bind multiple terms, calling continuation with the resulting variables *)
  and bind_terms (terms : Source.term list) (h : Sub.t)
      (k : Ident.t list -> Target.command) : Target.command =
    match terms with
    | [] -> k []
    | t :: rest ->
        bind_term t h (fun v ->
          bind_terms rest h (fun vs -> k (v :: vs)))

  (** Main transformation function *)
  and transform_command (cmd : Source.command) (h : Sub.t) : Target.command =
    match cmd with
    | CutPos (sig_, Variable x, Variable y) ->
        Target.CutMatch (sig_, Sub.apply h x,
          build_branches_from_sig sig_ (fun params n ->
            Target.CutConstructor (sig_, n, params, Sub.apply h y)))

    | CutPos (sig_, Variable x, Match (_, bs)) ->
        Target.CutMatch (sig_, Sub.apply h x, transform_source_branches bs h)

    | CutPos (_, Variable x, MuRhsPos (_, a, r)) ->
        transform_command r (Sub.add a (Sub.apply h x) h)

    | CutPos (sig_, Constructor (_, n, args), Variable y) ->
        bind_terms args h (fun arg_vars ->
          Target.CutConstructor (sig_, n, arg_vars, Sub.apply h y))

    | CutPos (_, Constructor (_, n, args), Match (_, bs)) ->
        bind_terms args h (fun arg_vars ->
          let branches = transform_source_branches bs h in
          lookup_branch_body branches n arg_vars)

    | CutPos (sig_, Constructor (_, n, args), MuRhsPos (_, a, r)) ->
        bind_terms args h (fun arg_vars ->
          let a' = Ident.fresh () in
          Target.LetConstructor (sig_, n, arg_vars, a',
            transform_command r (Sub.add a a' h)))

    | CutPos (_, MuLhsPos (_, x, s), Variable y) ->
        transform_command s (Sub.add x (Sub.apply h y) h)

    | CutPos (sig_, MuLhsPos (_, x, s), Match (_, bs)) ->
        let x' = Ident.fresh () in
        Target.LetMatch (sig_, transform_source_branches bs h, x',
          transform_command s (Sub.add x x' h))

    | CutPos (sig_, MuLhsPos (_, x, s), MuRhsPos (_, a, r)) ->
        let x' = Ident.fresh () in
        Target.LetMatch (sig_,
          build_branches_from_sig sig_ (fun params n ->
            let a' = Ident.fresh () in
            Target.LetConstructor (sig_, n, params, a',
              transform_command r (Sub.add a a' h))),
          x',
          transform_command s (Sub.add x x' h))

    | CutNeg (sig_, Variable x, Variable y) ->
        Target.CutComatch (sig_,
          build_branches_from_sig sig_ (fun params n ->
            Target.CutDestructor (sig_, Sub.apply h x, n, params)),
          Sub.apply h y)

    | CutNeg (sig_, Variable x, Destructor (_, n, args)) ->
        bind_terms args h (fun arg_vars ->
          Target.CutDestructor (sig_, Sub.apply h x, n, arg_vars))

    | CutNeg (_, Variable x, MuRhsNeg (_, a, r)) ->
        transform_command r (Sub.add a (Sub.apply h x) h)

    | CutNeg (sig_, Comatch (_, bs), Variable y) ->
        Target.CutComatch (sig_, transform_source_branches bs h, Sub.apply h y)

    | CutNeg (_, Comatch (_, bs), Destructor (_, n, args)) ->
        bind_terms args h (fun arg_vars ->
          let branches = transform_source_branches bs h in
          lookup_branch_body branches n arg_vars)

    | CutNeg (sig_, Comatch (_, bs), MuRhsNeg (_, a, r)) ->
        let a' = Ident.fresh () in
        Target.LetComatch (sig_, transform_source_branches bs h, a',
          transform_command r (Sub.add a a' h))

    | CutNeg (_, MuLhsNeg (_, x, s), Variable y) ->
        transform_command s (Sub.add x (Sub.apply h y) h)

    | CutNeg (sig_, MuLhsNeg (_, x, s), Destructor (_, n, args)) ->
        bind_terms args h (fun arg_vars ->
          let x' = Ident.fresh () in
          Target.LetDestructor (sig_, n, arg_vars, x',
            transform_command s (Sub.add x x' h)))

    | CutNeg (sig_, MuLhsNeg (_, x, s), MuRhsNeg (_, a, r)) ->
        let a' = Ident.fresh () in
        Target.LetComatch (sig_,
          build_branches_from_sig sig_ (fun params n ->
            let x' = Ident.fresh () in
            Target.LetDestructor (sig_, n, params, x',
              transform_command s (Sub.add x x' h))),
          a',
          transform_command r (Sub.add a a' h))

    | End -> Target.End

    | CutPos (_, _, _) -> 
        failwith "ill-typed: CutPos requires (Variable|Constructor|MuLhsPos) on LHS and (Variable|Match|MuRhsPos) on RHS"
    | CutNeg (_, _, _) -> 
        failwith "ill-typed: CutNeg requires (Variable|Comatch|MuLhsNeg) on LHS and (Variable|Destructor|MuRhsNeg) on RHS"
end

(* ========================================================================= *)
(* Collapsed Language                                                           *)
(* ========================================================================= *)

module Collapsed = struct

  (* Collapsed language makes no distinction between positive (data) and negative (codata) types *)
  type signature = chiral_tpe list list

  and chiral_tpe =
    | Lhs of signature (* prd *)
    | Rhs of signature (* cns *)

  type command =
    | Let of signature * int * Ident.t list * Ident.t * command  (** [⟨Cₙ(Γ) | μ̃x.s⟩] or [⟨μα.s | Dₙ(Γ)⟩] *)
    | Switch of signature * Ident.t * branch list  (** [⟨x | case \{C₁(Γ₁) ⇒ s₁; …\}⟩] or [⟨cocase \{D₁(Γ₁) ⇒ s₁; …\} | α⟩] *)
    | New of signature * branch list * Ident.t * command (* [⟨cocase \{D₁(Γ₁) ⇒ s₁; …\} | μ̃x.s⟩] or [⟨μα.s | case \{C₁(Γ₁) ⇒ s₁; …\}⟩] *)
    | Invoke of signature * int * Ident.t list * Ident.t  (** [⟨Cₙ(Γ) | α⟩] or [⟨x | Dₙ(Γ)⟩] *)
    | End  (** Terminal / halt *)

  and branch = Clause of Ident.t list * command

end

(* ========================================================================= *)
(* Collapse Transformation (Target → Collapsed)                              *)
(* ========================================================================= *)

module Collapse = struct
  (** 
    Collapse the 8-form Target language to the 4-form Collapsed language.
    
    Key insight: chirality flips for negative types.
    - Positive type T: Lhs T → Lhs, Rhs T → Rhs  (preserved)
    - Negative type T: Lhs T → Rhs, Rhs T → Lhs  (flipped)
    
    This ensures consistent variable typing:
    - Let/Switch operate on producers (Lhs in Collapsed)
    - New/Invoke operate on consumers (Rhs in Collapsed)
  *)

  (** Collapse a chiral type, flipping chirality for negative types *)
  let rec collapse_chiral : chiral_tpe -> Collapsed.chiral_tpe = function
    | Lhs (Pos sig_) -> Collapsed.Lhs (collapse_sig sig_)
    | Rhs (Pos sig_) -> Collapsed.Rhs (collapse_sig sig_)
    | Lhs (Neg sig_) -> Collapsed.Rhs (collapse_sig sig_)  (* flip! *)
    | Rhs (Neg sig_) -> Collapsed.Lhs (collapse_sig sig_)  (* flip! *)

  (** Collapse a signature (list of constructor/destructor parameter lists) *)
  and collapse_sig (sig_ : signature) : Collapsed.signature =
    List.map (List.map collapse_chiral) sig_

  (** Collapse a branch *)
  let rec collapse_branch (Target.Clause (params, body)) : Collapsed.branch =
    Collapsed.Clause (params, collapse_command body)

  (** Main collapse transformation *)
  and collapse_command : Target.command -> Collapsed.command = function
    (* Let: ⟨C(Γ)|μ̃x.s⟩ and ⟨μα.s|D(Γ)⟩ both become Let *)
    | Target.LetConstructor (sig_, n, args, x, cont) ->
        Collapsed.Let (collapse_sig sig_, n, args, x, collapse_command cont)
    | Target.LetDestructor (sig_, n, args, a, cont) ->
        Collapsed.Let (collapse_sig sig_, n, args, a, collapse_command cont)

    (* Switch: ⟨x|case{…}⟩ and ⟨cocase{…}|α⟩ both become Switch *)
    | Target.CutMatch (sig_, x, branches) ->
        Collapsed.Switch (collapse_sig sig_, x, List.map collapse_branch branches)
    | Target.CutComatch (sig_, branches, a) ->
        Collapsed.Switch (collapse_sig sig_, a, List.map collapse_branch branches)

    (* New: ⟨cocase{…}|μ̃x.s⟩ and ⟨μα.s|case{…}⟩ both become New *)
    | Target.LetComatch (sig_, branches, x, cont) ->
        Collapsed.New (collapse_sig sig_, List.map collapse_branch branches, x, collapse_command cont)
    | Target.LetMatch (sig_, branches, a, cont) ->
        Collapsed.New (collapse_sig sig_, List.map collapse_branch branches, a, collapse_command cont)

    (* Invoke: ⟨C(Γ)|α⟩ and ⟨x|D(Γ)⟩ both become Invoke *)
    | Target.CutConstructor (sig_, n, args, a) ->
        Collapsed.Invoke (collapse_sig sig_, n, args, a)
    | Target.CutDestructor (sig_, x, n, args) ->
        Collapsed.Invoke (collapse_sig sig_, n, args, x)

    | Target.End -> Collapsed.End

  (** Full pipeline: Source → Target → Collapsed *)
  let from_source (cmd : Source.command) : Collapsed.command =
    collapse_command (Transform.transform_command cmd Sub.empty)
end