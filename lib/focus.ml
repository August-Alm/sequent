(**
  Module: Focus
  Description: Translates Core to Focused.
  
  This transformation canonicalizes Core sequent calculus terms into a focused
  form where all cuts are between variables (axiom cuts), constructors are
  bound via Let, and pattern matches become Switch/New.
  
  The key insight: every cut ⟨producer | consumer⟩ is analyzed based on the
  shapes of both sides to determine the focused form:
  
  - Var | Var → Axiom (eta-expand if needed)
  - Ctor | Match → inline the branch (beta reduction)
  - Ctor | MuRhs → Let binding
  - MuLhs | Match → New binding
  - etc.
*)

module Core = Core.Terms
module Focused = Focused.Terms

open Common.Identifiers
open Common.Types

(* ========================================================================= *)
(* Helper Functions                                                          *)
(* ========================================================================= *)

(** Generate fresh variable names for an xtor's arguments *)
let fresh_params (xtor: xtor) : Ident.t list =
  List.map (fun _ -> Ident.fresh ()) xtor.arguments

(** Find an xtor in a signature by name *)
let find_xtor (sgn: sgn_typ) (name: Path.t) : xtor option =
  List.find_opt (fun x -> Path.equal x.name name) sgn.xtors

(* ========================================================================= *)
(* Variable Renaming in Core Terms                                           *)
(* ========================================================================= *)

(** Rename a variable in a Core term *)
let rec rename_term (from_v: Ident.t) (to_v: Ident.t) (t: Core.term) : Core.term =
  let rename = rename_term from_v to_v in
  let rename_cmd = rename_command from_v to_v in
  let rename_var v = if Ident.equal v from_v then to_v else v in
  match t with
    Core.Var v -> Core.Var (rename_var v)
  | Core.Lit n -> Core.Lit n
  | Core.Ctor (sgn, xtor, args) -> Core.Ctor (sgn, xtor, List.map rename args)
  | Core.Dtor (sgn, xtor, args) -> Core.Dtor (sgn, xtor, List.map rename args)
  | Core.Match (sgn, branches) ->
      Core.Match (sgn, List.map (rename_branch from_v to_v) branches)
  | Core.Comatch (sgn, branches) ->
      Core.Comatch (sgn, List.map (rename_branch from_v to_v) branches)
  | Core.MuLhs (ty, x, cmd) ->
      if Ident.equal x from_v then t  (* shadowed *)
      else Core.MuLhs (ty, x, rename_cmd cmd)
  | Core.MuRhs (ty, x, cmd) ->
      if Ident.equal x from_v then t  (* shadowed *)
      else Core.MuRhs (ty, x, rename_cmd cmd)

and rename_command (from_v: Ident.t) (to_v: Ident.t) (cmd: Core.command) : Core.command =
  let rename = rename_term from_v to_v in
  let rename_cmd = rename_command from_v to_v in
  match cmd with
    Core.Cut (ty, lhs, rhs) -> Core.Cut (ty, rename lhs, rename rhs)
  | Core.Call (path, ty_args, tm_args) -> 
      Core.Call (path, ty_args, List.map rename tm_args)
  | Core.Add (t1, t2, t3) -> Core.Add (rename t1, rename t2, rename t3)
  | Core.Ifz (cond, then_cmd, else_cmd) ->
      Core.Ifz (rename cond, rename_cmd then_cmd, rename_cmd else_cmd)
  | Core.End -> Core.End

and rename_branch (from_v: Ident.t) (to_v: Ident.t) 
    ((xtor, vars, cmd): Core.branch) : Core.branch =
  if List.exists (Ident.equal from_v) vars then
    (xtor, vars, cmd)  (* shadowed *)
  else
    (xtor, vars, rename_command from_v to_v cmd)

(* ========================================================================= *)
(* Term Binding: Convert Core.term to variable + Focused prefix              *)
(* ========================================================================= *)

(** Bind a Core term to a fresh variable, building Focused commands.
    Returns: a function that takes a continuation and produces a command
    where the bound variable is available. *)
let rec bind_term (t: Core.term) (k: Ident.t -> Focused.command) : Focused.command =
  match t with
    Core.Var x -> k x
  | Core.Lit n ->
      let v = Ident.fresh () in
      Focused.Lit (n, v, k v)
  | Core.Ctor (_sgn, xtor, args) ->
      bind_terms args (fun arg_vars ->
        let v = Ident.fresh () in
        Focused.Let (v, xtor, arg_vars, k v))
  | Core.Dtor (_sgn, xtor, args) ->
      (* Destructors also become Let bindings in focused form *)
      bind_terms args (fun arg_vars ->
        let v = Ident.fresh () in
        Focused.Let (v, xtor, arg_vars, k v))
  | Core.Match (sgn, branches) ->
      (* Match becomes New: creates a consumer *)
      let v = Ident.fresh () in
      let focused_branches = List.map (fun (xtor, vars, cmd) ->
        (xtor, vars, transform_command cmd)
      ) branches in
      Focused.New (sgn, v, focused_branches, k v)
  | Core.Comatch (sgn, branches) ->
      (* Comatch also becomes New in focused form *)
      let v = Ident.fresh () in
      let focused_branches = List.map (fun (xtor, vars, cmd) ->
        (xtor, vars, transform_command cmd)
      ) branches in
      Focused.New (sgn, v, focused_branches, k v)
  | Core.MuLhs (ty, x, cmd) ->
      (* MuLhs binds a continuation x and produces a value.
         We transform the body and the result becomes available. *)
      bind_mu ty x cmd k
  | Core.MuRhs (ty, x, cmd) ->
      (* MuRhs binds a producer x and produces a consumer. *)
      bind_mu ty x cmd k

(** Bind multiple terms in sequence *)
and bind_terms (ts: Core.term list) (k: Ident.t list -> Focused.command) : Focused.command =
  match ts with
    [] -> k []
  | t :: rest ->
      bind_term t (fun v ->
        bind_terms rest (fun vs -> k (v :: vs)))

(** Handle Mu bindings *)
and bind_mu (ty: typ) (x: Ident.t) (cmd: Core.command) (k: Ident.t -> Focused.command) : Focused.command =
  match whnf Ident.emptytbl [] ty with
    Sgn sgn ->
      (* For signature types: create New with a forwarding branch.
         The body of the mu becomes the continuation. *)
      let bound = Ident.fresh () in
      let params = fresh_params (List.hd sgn.xtors) in  (* Single xtor for primitives *)
      let fwd_branch = 
        (List.hd sgn.xtors, params, Focused.Let (bound, List.hd sgn.xtors, params, k bound))
      in
      Focused.New (sgn, x, [fwd_branch], transform_command cmd)
  | Ext Int ->
      (* For Int: the body produces a value that jumps to x.
         Transform body and replace axioms to x with continuation. *)
      let bound = Ident.fresh () in
      let body' = transform_command (rename_command x bound cmd) in
      replace_int_ret bound body' k
  | _ ->
      failwith "bind_mu: unsupported type"

(** Replace Ret/Axiom targeting a variable with continuation application *)
and replace_int_ret (target: Ident.t) (cmd: Focused.command) 
    (k: Ident.t -> Focused.command) : Focused.command =
  match cmd with
    Focused.Axiom (_ty, v, dest) when Ident.equal dest target ->
      k v
  | Focused.Axiom (ty, v, dest) -> Focused.Axiom (ty, v, dest)
  | Focused.Let (x, xtor, args, body) ->
      Focused.Let (x, xtor, args, replace_int_ret target body k)
  | Focused.Switch (sgn, x, branches) ->
      let branches' = List.map (fun (xtor, vars, body) ->
        (xtor, vars, replace_int_ret target body k)
      ) branches in
      Focused.Switch (sgn, x, branches')
  | Focused.New (sgn, x, branches, body) ->
      let branches' = List.map (fun (xtor, vars, branch_body) ->
        (xtor, vars, replace_int_ret target branch_body k)
      ) branches in
      Focused.New (sgn, x, branches', replace_int_ret target body k)
  | Focused.Invoke (x, xtor, args) -> Focused.Invoke (x, xtor, args)
  | Focused.Lit (n, x, body) ->
      Focused.Lit (n, x, replace_int_ret target body k)
  | Focused.Add (a, b, r, body) ->
      Focused.Add (a, b, r, replace_int_ret target body k)
  | Focused.Ifz (x, then_cmd, else_cmd) ->
      Focused.Ifz (x, replace_int_ret target then_cmd k,
                      replace_int_ret target else_cmd k)
  | Focused.End -> Focused.End
  | Focused.Ret (ty, v) -> Focused.Ret (ty, v)

(* ========================================================================= *)
(* Cut Transformation                                                        *)
(* ========================================================================= *)

(** Transform a Cut based on the shapes of lhs and rhs.
    This is the heart of focusing. *)
and transform_cut (ty: typ) (lhs: Core.term) (rhs: Core.term) : Focused.command =
  match whnf Ident.emptytbl [] ty with
    Ext Int -> transform_cut_int lhs rhs
  | Sgn sgn -> transform_cut_sgn sgn ty lhs rhs
  | _ -> failwith "transform_cut: unsupported type"

(** Transform cuts at Int type *)
and transform_cut_int (lhs: Core.term) (rhs: Core.term) : Focused.command =
  match lhs, rhs with
  (* Var | Var: Axiom *)
  | Core.Var x, Core.Var y ->
      Focused.Axiom (Ext Int, x, y)
  (* Var | MuRhs: substitute *)
  | Core.Var x, Core.MuRhs (_, a, cmd) ->
      transform_command (rename_command a x cmd)
  (* Lit | Var: bind literal, axiom *)
  | Core.Lit n, Core.Var y ->
      let v = Ident.fresh () in
      Focused.Lit (n, v, Focused.Axiom (Ext Int, v, y))
  (* Lit | MuRhs: bind literal *)
  | Core.Lit n, Core.MuRhs (_, a, cmd) ->
      Focused.Lit (n, a, transform_command cmd)
  (* MuLhs | Var: substitute *)
  | Core.MuLhs (_, x, cmd), Core.Var y ->
      transform_command (rename_command x y cmd)
  (* MuLhs | MuRhs: sequence *)
  | Core.MuLhs (_, x, lhs_cmd), Core.MuRhs (_, a, rhs_cmd) ->
      let bound = Ident.fresh () in
      let lhs' = transform_command (rename_command x bound lhs_cmd) in
      let rhs' = transform_command rhs_cmd in
      replace_int_ret bound lhs' (fun v ->
        subst_var a v rhs')
  | _ -> failwith "transform_cut_int: unsupported form"

(** Transform cuts at signature types *)
and transform_cut_sgn (sgn: sgn_typ) (_ty: typ) (lhs: Core.term) (rhs: Core.term) : Focused.command =
  match lhs, rhs with
  (* Var | Var: eta-expand with Switch/Invoke *)
  | Core.Var x, Core.Var y ->
      let branches = List.map (fun xtor ->
        let params = fresh_params xtor in
        (xtor, params, Focused.Invoke (y, xtor, params))
      ) sgn.xtors in
      Focused.Switch (sgn, x, branches)

  (* Var | Match/Comatch: Switch *)
  | Core.Var x, Core.Match (_, branches) ->
      let focused_branches = List.map (fun (xtor, vars, cmd) ->
        (xtor, vars, transform_command cmd)
      ) branches in
      Focused.Switch (sgn, x, focused_branches)
  | Core.Var x, Core.Comatch (_, branches) ->
      let focused_branches = List.map (fun (xtor, vars, cmd) ->
        (xtor, vars, transform_command cmd)
      ) branches in
      Focused.Switch (sgn, x, focused_branches)

  (* Var | MuRhs: substitute *)
  | Core.Var x, Core.MuRhs (_, a, cmd) ->
      transform_command (rename_command a x cmd)

  (* Ctor/Dtor | Var: bind and Invoke *)
  | Core.Ctor (_, xtor, args), Core.Var y ->
      bind_terms args (fun arg_vars ->
        Focused.Invoke (y, xtor, arg_vars))
  | Core.Dtor (_, xtor, args), Core.Var y ->
      bind_terms args (fun arg_vars ->
        Focused.Invoke (y, xtor, arg_vars))

  (* Ctor/Dtor | Match/Comatch: inline the matching branch (beta reduction) *)
  | Core.Ctor (_, xtor, args), Core.Match (_, branches) ->
      inline_branch xtor args branches
  | Core.Ctor (_, xtor, args), Core.Comatch (_, branches) ->
      inline_branch xtor args branches
  | Core.Dtor (_, xtor, args), Core.Match (_, branches) ->
      inline_branch xtor args branches
  | Core.Dtor (_, xtor, args), Core.Comatch (_, branches) ->
      inline_branch xtor args branches

  (* Ctor/Dtor | MuRhs: Let binding *)
  | Core.Ctor (_, xtor, args), Core.MuRhs (_, a, cmd) ->
      bind_terms args (fun arg_vars ->
        Focused.Let (a, xtor, arg_vars, transform_command cmd))
  | Core.Dtor (_, xtor, args), Core.MuRhs (_, a, cmd) ->
      bind_terms args (fun arg_vars ->
        Focused.Let (a, xtor, arg_vars, transform_command cmd))

  (* Match/Comatch | Ctor/Dtor: inline the matching branch (beta reduction) *)
  | Core.Match (_, branches), Core.Ctor (_, xtor, args) ->
      inline_branch xtor args branches
  | Core.Match (_, branches), Core.Dtor (_, xtor, args) ->
      inline_branch xtor args branches
  | Core.Comatch (_, branches), Core.Ctor (_, xtor, args) ->
      inline_branch xtor args branches
  | Core.Comatch (_, branches), Core.Dtor (_, xtor, args) ->
      inline_branch xtor args branches

  (* Match/Comatch | Var: bind and Switch with eta-branches *)
  | Core.Match (_, _branches) as m, Core.Var y ->
      bind_term m (fun x ->
        let eta_branches = List.map (fun xtor ->
          let params = fresh_params xtor in
          (xtor, params, Focused.Invoke (y, xtor, params))
        ) sgn.xtors in
        Focused.Switch (sgn, x, eta_branches))
  | Core.Comatch (_, branches) as _m, Core.Var y ->
      (* Comatch | Var: bind the comatch, then eta-expand via Switch.
         This ensures proper call-by-need semantics for codata. *)
      let v = Ident.fresh () in
      let focused_branches = List.map (fun (xtor, vars, cmd) ->
        (xtor, vars, transform_command cmd)
      ) branches in
      let eta_branches = List.map (fun xtor ->
        let params = fresh_params xtor in
        (xtor, params, Focused.Invoke (y, xtor, params))
      ) sgn.xtors in
      Focused.New (sgn, v, focused_branches, Focused.Switch (sgn, v, eta_branches))

  (* Match/Comatch | Match/Comatch: bind lhs, then Switch *)
  | (Core.Match _ | Core.Comatch _ as m1), 
    (Core.Match (_, branches2) | Core.Comatch (_, branches2)) ->
      bind_term m1 (fun x ->
        let focused_branches = List.map (fun (xtor, vars, cmd) ->
          (xtor, vars, transform_command cmd)
        ) branches2 in
        Focused.Switch (sgn, x, focused_branches))

  (* Match/Comatch | MuRhs: bind *)
  | (Core.Match _ | Core.Comatch _ as m), Core.MuRhs (_, a, cmd) ->
      bind_term m (fun x ->
        transform_command (rename_command a x cmd))

  (* MuLhs | Var: substitute *)
  | Core.MuLhs (_, x, cmd), Core.Var y ->
      transform_command (rename_command x y cmd)

  (* MuLhs | Match/Comatch: New *)
  | Core.MuLhs (_, x, mu_cmd), Core.Match (_, branches) ->
      let focused_branches = List.map (fun (xtor, vars, cmd) ->
        (xtor, vars, transform_command cmd)
      ) branches in
      Focused.New (sgn, x, focused_branches, transform_command mu_cmd)
  | Core.MuLhs (_, x, mu_cmd), Core.Comatch (_, branches) ->
      let focused_branches = List.map (fun (xtor, vars, cmd) ->
        (xtor, vars, transform_command cmd)
      ) branches in
      Focused.New (sgn, x, focused_branches, transform_command mu_cmd)

  (* MuLhs | MuRhs: New with forwarding *)
  | Core.MuLhs (_, x, mu_cmd), Core.MuRhs (_, a, rhs_cmd) ->
      let fwd_branches = List.map (fun xtor ->
        let params = fresh_params xtor in
        (xtor, params, Focused.Let (a, xtor, params, transform_command rhs_cmd))
      ) sgn.xtors in
      Focused.New (sgn, x, fwd_branches, transform_command mu_cmd)

  | _ -> 
      let lhs_form = match lhs with
        | Core.Var _ -> "Var"
        | Core.Lit _ -> "Lit"
        | Core.Ctor _ -> "Ctor"
        | Core.Dtor _ -> "Dtor"
        | Core.Match _ -> "Match"
        | Core.Comatch _ -> "Comatch"
        | Core.MuLhs _ -> "MuLhs"
        | Core.MuRhs _ -> "MuRhs"
      in
      let rhs_form = match rhs with
        | Core.Var _ -> "Var"
        | Core.Lit _ -> "Lit"
        | Core.Ctor _ -> "Ctor"
        | Core.Dtor _ -> "Dtor"
        | Core.Match _ -> "Match"
        | Core.Comatch _ -> "Comatch"
        | Core.MuLhs _ -> "MuLhs"
        | Core.MuRhs _ -> "MuRhs"
      in
      failwith (Printf.sprintf "transform_cut_sgn: unsupported form %s | %s" lhs_form rhs_form)

(** Inline a branch: find matching branch and substitute args for params directly.
    This enables pack/unpack elimination by letting Ctor(pack, [arg]) meet
    Match(pack, [x], cmd) and substitute arg directly into cmd. *)
and inline_branch (xtor: xtor) (args: Core.term list) (branches: Core.branch list) 
    : Focused.command =
  match List.find_opt (fun (x, _, _) -> Path.equal x.name xtor.name) branches with
    None -> failwith "inline_branch: xtor not found"
  | Some (_, params, cmd) ->
      (* Substitute terms directly into the command, then transform.
         This allows nested Ctor|Match pairs to meet and cancel. *)
      let cmd' = List.fold_left2 
        (fun c param arg -> subst_term_in_cmd param arg c)
        cmd params args
      in
      transform_command cmd'

(** Substitute a Core term for a variable in a Core command *)
and subst_term_in_cmd (x: Ident.t) (t: Core.term) (cmd: Core.command) : Core.command =
  match cmd with
  | Core.Cut (ty, lhs, rhs) ->
      Core.Cut (ty, subst_term_in_term x t lhs, subst_term_in_term x t rhs)
  | Core.Add (a, b, c) ->
      Core.Add (subst_term_in_term x t a, subst_term_in_term x t b, subst_term_in_term x t c)
  | Core.Ifz (v, then_cmd, else_cmd) ->
      Core.Ifz (subst_term_in_term x t v, subst_term_in_cmd x t then_cmd, subst_term_in_cmd x t else_cmd)
  | Core.Call (path, ty_args, args) ->
      Core.Call (path, ty_args, List.map (subst_term_in_term x t) args)
  | Core.End -> Core.End

(** Substitute a Core term for a variable in a Core term *)
and subst_term_in_term (x: Ident.t) (replacement: Core.term) (tm: Core.term) : Core.term =
  match tm with
  | Core.Var y -> if Ident.equal y x then replacement else tm
  | Core.Lit n -> Core.Lit n
  | Core.Ctor (sgn, xtor, args) ->
      Core.Ctor (sgn, xtor, List.map (subst_term_in_term x replacement) args)
  | Core.Dtor (sgn, xtor, args) ->
      Core.Dtor (sgn, xtor, List.map (subst_term_in_term x replacement) args)
  | Core.Match (sgn, branches) ->
      Core.Match (sgn, List.map (fun (xtor, vars, cmd) ->
        if List.exists (Ident.equal x) vars then (xtor, vars, cmd)
        else (xtor, vars, subst_term_in_cmd x replacement cmd)
      ) branches)
  | Core.Comatch (sgn, branches) ->
      Core.Comatch (sgn, List.map (fun (xtor, vars, cmd) ->
        if List.exists (Ident.equal x) vars then (xtor, vars, cmd)
        else (xtor, vars, subst_term_in_cmd x replacement cmd)
      ) branches)
  | Core.MuLhs (ty, y, cmd) ->
      if Ident.equal y x then tm
      else Core.MuLhs (ty, y, subst_term_in_cmd x replacement cmd)
  | Core.MuRhs (ty, y, cmd) ->
      if Ident.equal y x then tm
      else Core.MuRhs (ty, y, subst_term_in_cmd x replacement cmd)

(** Substitute a variable for another in Focused command *)
and subst_var (x: Ident.t) (v: Ident.t) (cmd: Focused.command) : Focused.command =
  let sv y = if Ident.equal y x then v else y in
  let sv_list = List.map sv in
  match cmd with
    Focused.Let (y, xtor, args, body) ->
      if Ident.equal y x then Focused.Let (y, xtor, sv_list args, body)
      else Focused.Let (y, xtor, sv_list args, subst_var x v body)
  | Focused.Switch (sgn, y, branches) ->
      let branches' = List.map (fun (xtor, params, body) ->
        if List.exists (Ident.equal x) params then (xtor, params, body)
        else (xtor, params, subst_var x v body)
      ) branches in
      Focused.Switch (sgn, sv y, branches')
  | Focused.New (sgn, y, branches, body) ->
      let branches' = List.map (fun (xtor, params, branch_body) ->
        if List.exists (Ident.equal x) params then (xtor, params, branch_body)
        else (xtor, params, subst_var x v branch_body)
      ) branches in
      let body' = if Ident.equal y x then body else subst_var x v body in
      Focused.New (sgn, y, branches', body')
  | Focused.Invoke (y, xtor, args) ->
      Focused.Invoke (sv y, xtor, sv_list args)
  | Focused.Axiom (ty, y, k) ->
      Focused.Axiom (ty, sv y, sv k)
  | Focused.Lit (n, y, body) ->
      if Ident.equal y x then Focused.Lit (n, y, body)
      else Focused.Lit (n, y, subst_var x v body)
  | Focused.Add (a, b, r, body) ->
      if Ident.equal r x then Focused.Add (sv a, sv b, r, body)
      else Focused.Add (sv a, sv b, r, subst_var x v body)
  | Focused.Ifz (y, then_cmd, else_cmd) ->
      Focused.Ifz (sv y, subst_var x v then_cmd, subst_var x v else_cmd)
  | Focused.End -> Focused.End
  | Focused.Ret (ty, y) -> Focused.Ret (ty, sv y)

(* ========================================================================= *)
(* Main Transformation                                                       *)
(* ========================================================================= *)

(** Main transformation: Core.command -> Focused.command *)
and transform_command (cmd: Core.command) : Focused.command =
  match cmd with
    Core.End -> Focused.End
  | Core.Cut (ty, lhs, rhs) ->
      transform_cut ty lhs rhs
  | Core.Call (_path, _ty_args, _tm_args) ->
      (* TODO: Handle calls - for now, just fail *)
      failwith "transform_command: Call not yet implemented"
  | Core.Add (t1, t2, t3) ->
      bind_term t1 (fun v1 ->
        bind_term t2 (fun v2 ->
          match t3 with
            Core.Var k ->
              let r = Ident.fresh () in
              Focused.Add (v1, v2, r, Focused.Axiom (Ext Int, r, k))
          | Core.MuRhs (_, a, cmd) ->
              Focused.Add (v1, v2, a, transform_command cmd)
          | _ -> failwith "Add continuation must be Var or MuRhs"))
  | Core.Ifz (cond, then_cmd, else_cmd) ->
      bind_term cond (fun v ->
        Focused.Ifz (v, transform_command then_cmd, transform_command else_cmd))

(* ========================================================================= *)
(* Optimization pass (currently a no-op traversal)                           *)
(* ========================================================================= *)

(** Optimize focused commands. Currently just recursively processes subexpressions.
    Future work: inline New/Switch pairs when safe. *)
let rec optimize (cmd: Focused.command) : Focused.command =
  match cmd with
  | Focused.Let (x, xtor, args, body) ->
      Focused.Let (x, xtor, args, optimize body)
  | Focused.Switch (sgn, v, branches) ->
      Focused.Switch (sgn, v, 
        List.map (fun (x, vs, b) -> (x, vs, optimize b)) branches)
  | Focused.New (sgn, v, branches, body) ->
      Focused.New (sgn, v,
        List.map (fun (x, vs, b) -> (x, vs, optimize b)) branches,
        optimize body)
  | Focused.Lit (n, v, body) ->
      Focused.Lit (n, v, optimize body)
  | Focused.Add (a, b, r, body) ->
      Focused.Add (a, b, r, optimize body)
  | Focused.Ifz (v, then_cmd, else_cmd) ->
      Focused.Ifz (v, optimize then_cmd, optimize else_cmd)
  | Focused.Invoke _ | Focused.Axiom _ | Focused.End | Focused.Ret _ ->
      cmd

(** Entry point: transform a Core command to Focused command *)
let focus (cmd: Core.command) : Focused.command =
  let result = transform_command cmd in
  optimize result
