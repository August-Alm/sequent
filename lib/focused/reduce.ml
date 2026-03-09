(**
  module: Focused.Reduce
  description: Reduction/inlining pass for focused commands.
  
  This pass eliminates single-use continuations by inlining:
  
  1. NewInt reduction:
     new k = { v => branch }; cont   where cont has exactly one ⟨r | k⟩
     ==>  cont[⟨r | k⟩ := branch[v := r]]
     
  2. New reduction:
     new k = { m1(xs) => b1, ... }; cont   where cont has exactly one invoke k.m2(ys)
     ==>  cont[invoke k.m2(ys) := b2[xs := ys]]
     
  3. Administrative shifts reduction (always inlined):
     - raise.thunk: let v = raise.thunk(x); ... switch v { raise.thunk(p) => body } ...
       ==> ... body[p := x] ...  (for ALL such switches)
     - lower.return: new k = { lower.return(p) => body }; ... k.lower.return(x) ...
       ==> ... body[p := x] ...  (for ALL such invokes)
*)

open Common.Identifiers
open Common.Types

open Terms

(* ========================================================================= *)
(* Administrative Shifts Detection                                           *)
(* ========================================================================= *)

(** Check if a path is the raise.thunk constructor *)
let is_raise_thunk (p: Path.t) : bool = Path.equal p Prim.thunk_sym

(** Check if a path is the lower.return destructor *)
let is_lower_return (p: Path.t) : bool = Path.equal p Prim.return_sym

(* ========================================================================= *)
(* Variable Substitution                                                     *)
(* ========================================================================= *)

(** Substitute a single variable: cmd[old := new] *)
let subst_var (old_v: var) (new_v: var) (cmd: command) : command =
  let sv v = if Ident.equal v old_v then new_v else v in
  let svs vs = List.map sv vs in
  let rec go cmd =
    match cmd with
      Let (v, dec, xtor, args, body) ->
        Let (v, dec, xtor, svs args, if Ident.equal v old_v then body else go body)
    | Switch (v, dec, branches) ->
        Switch (sv v, dec, List.map go_branch branches)
    | New (k, dec, branches, cont) ->
        New (k, dec, List.map go_branch branches,
             if Ident.equal k old_v then cont else go cont)
    | Invoke (v, dec, xtor, args) ->
        Invoke (sv v, dec, xtor, svs args)
    | Jump (label, args) ->
        Jump (label, svs args)
    | Axiom (ty, v, k) ->
        Axiom (ty, sv v, sv k)
    | Lit (n, v, body) ->
        Lit (n, v, if Ident.equal v old_v then body else go body)
    | NewInt (k, v, branch, cont) ->
        let branch' = if Ident.equal v old_v then branch else go branch in
        let cont' = if Ident.equal k old_v then cont else go cont in
        NewInt (k, v, branch', cont')
    | Add (x, y, r, body) ->
        Add (sv x, sv y, r, if Ident.equal r old_v then body else go body)
    | Sub (x, y, r, body) ->
        Sub (sv x, sv y, r, if Ident.equal r old_v then body else go body)
    | Mul (x, y, r, body) ->
        Mul (sv x, sv y, r, if Ident.equal r old_v then body else go body)
    | Div (x, y, r, body) ->
        Div (sv x, sv y, r, if Ident.equal r old_v then body else go body)
    | Rem (x, y, r, body) ->
        Rem (sv x, sv y, r, if Ident.equal r old_v then body else go body)
    | Ifz (v, then_cmd, else_cmd) ->
        Ifz (sv v, go then_cmd, go else_cmd)
    | Ret (ty, v) ->
        Ret (ty, sv v)
    | End -> End
  and go_branch (xtor, ty_vars, tm_vars, body) =
    let shadowed = List.exists (Ident.equal old_v) tm_vars in
    (xtor, ty_vars, tm_vars, if shadowed then body else go body)
  in
  go cmd

(** Substitute multiple variables in parallel: cmd[old1 := new1, old2 := new2, ...] *)
let subst_vars (pairs: (var * var) list) (cmd: command) : command =
  List.fold_left (fun acc (old_v, new_v) -> subst_var old_v new_v acc) cmd pairs

(* ========================================================================= *)
(* Usage Counting                                                            *)
(* ========================================================================= *)

(** Count occurrences of variable v in command *)
let rec count_uses (v: var) (cmd: command) : int =
  let cv x = if Ident.equal x v then 1 else 0 in
  let cvs xs = List.fold_left (fun acc x -> acc + cv x) 0 xs in
  match cmd with
    Let (_, _, _, args, body) ->
      cvs args + count_uses v body
  | Switch (x, _, branches) ->
      cv x + List.fold_left (fun acc (_, _, _, b) -> acc + count_uses v b) 0 branches
  | New (_, _, branches, cont) ->
      List.fold_left (fun acc (_, _, _, b) -> acc + count_uses v b) 0 branches
      + count_uses v cont
  | Invoke (x, _, _, args) ->
      cv x + cvs args
  | Jump (_, args) ->
      cvs args
  | Axiom (_, x, k) ->
      cv x + cv k
  | Lit (_, _, body) ->
      count_uses v body
  | NewInt (_, _, branch, cont) ->
      count_uses v branch + count_uses v cont
  | Add (x, y, _, body) ->
      cv x + cv y + count_uses v body
  | Sub (x, y, _, body) ->
      cv x + cv y + count_uses v body
  | Mul (x, y, _, body) ->
      cv x + cv y + count_uses v body
  | Div (x, y, _, body) ->
      cv x + cv y + count_uses v body
  | Rem (x, y, _, body) ->
      cv x + cv y + count_uses v body
  | Ifz (x, then_cmd, else_cmd) ->
      cv x + count_uses v then_cmd + count_uses v else_cmd
  | Ret (_, x) ->
      cv x
  | End -> 0

(* ========================================================================= *)
(* Replace-All for Administrative Boxing                                     *)
(* ========================================================================= *)

(** Replace ALL occurrences of `switch v { xtor(params) => body }` where v matches target.
    Used to always inline raise.thunk regardless of use count.
    For each switch, replaces it with body[params := ctor_args]. *)
let rec replace_all_switches_with_args (v: var) (xtor: sym) (ctor_args: var list) (cmd: command) : command =
  let go = replace_all_switches_with_args v xtor ctor_args in
  match cmd with
    Switch (v', _, branches) when Ident.equal v v' ->
      (* Find the matching branch and inline *)
      (match List.find_opt (fun (x, _, _, _) -> Path.equal x xtor) branches with
        Some (_, _, params, branch_body) -> 
          subst_vars (List.combine params ctor_args) (go branch_body)
      | None -> 
          (* xtor not in branches - keep but recurse into branch bodies *)
          Switch (v', cmd |> (function Switch (_, dec, _) -> dec | _ -> assert false),
                  List.map (fun (x, ty, tm, b) -> (x, ty, tm, go b)) branches))
  | Switch (v', dec, branches) ->
      Switch (v', dec, List.map (fun (x, ty, tm, b) -> (x, ty, tm, go b)) branches)
  | Let (x, dec, xt, args, body) ->
      Let (x, dec, xt, args, go body)
  | New (k, dec, branches, cont) ->
      New (k, dec, List.map (fun (x, ty, tm, b) -> (x, ty, tm, go b)) branches, go cont)
  | Invoke (x, dec, xt, args) ->
      Invoke (x, dec, xt, args)
  | Jump (label, args) ->
      Jump (label, args)
  | Axiom (ty, x, k) ->
      Axiom (ty, x, k)
  | Lit (n, x, body) ->
      Lit (n, x, go body)
  | NewInt (k, x, branch, cont) ->
      NewInt (k, x, go branch, go cont)
  | Add (x, y, r, body) ->
      Add (x, y, r, go body)
  | Sub (x, y, r, body) ->
      Sub (x, y, r, go body)
  | Mul (x, y, r, body) ->
      Mul (x, y, r, go body)
  | Div (x, y, r, body) ->
      Div (x, y, r, go body)
  | Rem (x, y, r, body) ->
      Rem (x, y, r, go body)
  | Ifz (x, then_cmd, else_cmd) ->
      Ifz (x, go then_cmd, go else_cmd)
  | Ret (ty, x) ->
      Ret (ty, x)
  | End -> End

(** Replace ALL occurrences of `k.xtor(args)` where k matches target.
    Used to always inline lower.return regardless of use count.
    replacement_fn takes the args from the invoke and returns the inlined body. *)
let rec replace_all_invokes (k: var) (xtor: sym) (replacement_fn: var list -> command) (cmd: command) : command =
  let go = replace_all_invokes k xtor replacement_fn in
  match cmd with
    Invoke (k', _, xtor', args) when Ident.equal k k' && Path.equal xtor xtor' ->
      replacement_fn args
  | Invoke (x, dec, xt, args) ->
      Invoke (x, dec, xt, args)
  | Let (x, dec, xt, args, body) ->
      Let (x, dec, xt, args, go body)
  | Switch (v, dec, branches) ->
      Switch (v, dec, List.map (fun (x, ty, tm, b) -> (x, ty, tm, go b)) branches)
  | New (k', dec, branches, cont) ->
      New (k', dec, List.map (fun (x, ty, tm, b) -> (x, ty, tm, go b)) branches, go cont)
  | Jump (label, args) ->
      Jump (label, args)
  | Axiom (ty, x, k') ->
      Axiom (ty, x, k')
  | Lit (n, x, body) ->
      Lit (n, x, go body)
  | NewInt (k', x, branch, cont) ->
      NewInt (k', x, go branch, go cont)
  | Add (x, y, r, body) ->
      Add (x, y, r, go body)
  | Sub (x, y, r, body) ->
      Sub (x, y, r, go body)
  | Mul (x, y, r, body) ->
      Mul (x, y, r, go body)
  | Div (x, y, r, body) ->
      Div (x, y, r, go body)
  | Rem (x, y, r, body) ->
      Rem (x, y, r, go body)
  | Ifz (x, then_cmd, else_cmd) ->
      Ifz (x, go then_cmd, go else_cmd)
  | Ret (ty, x) ->
      Ret (ty, x)
  | End -> End

(* ========================================================================= *)
(* Single-Use Detection and Replacement                                      *)
(* ========================================================================= *)

(** Result of trying to find and inline a single use of k *)
type 'a inline_result =
    NotFound           (* k not used *)
  | MultipleUses       (* k used more than once *)
  | Found of 'a        (* k used exactly once, here's the replacement *)

(** Try to find a single Axiom(ty, r, k) and replace it with replacement_fn(r).
    Returns the transformed command if successful. *)
let rec find_and_replace_axiom (k: var) (replacement_fn: var -> command) (cmd: command)
    : command inline_result =
  match cmd with
    Axiom (_, r, k') when Ident.equal k k' ->
      Found (replacement_fn r)
  | Axiom (_, _, _) -> NotFound
  | Let (v, dec, xtor, args, body) ->
      (match find_and_replace_axiom k replacement_fn body with
        Found body' -> Found (Let (v, dec, xtor, args, body'))
      | other -> other)
  | Switch (v, dec, branches) ->
      find_and_replace_in_branches k replacement_fn branches
        (fun bs -> Switch (v, dec, bs))
  | New (k', dec, branches, cont) ->
      (* Don't look in branches - k is the consumer being invoked, not created here *)
      (match find_and_replace_axiom k replacement_fn cont with
        Found cont' -> Found (New (k', dec, branches, cont'))
      | other -> other)
  | Invoke (_, _, _, _) -> NotFound
  | Jump (_, _) -> NotFound
  | Lit (n, v, body) ->
      (match find_and_replace_axiom k replacement_fn body with
        Found body' -> Found (Lit (n, v, body'))
      | other -> other)
  | NewInt (k', v, branch, cont) ->
      (* k might be used in branch (if k is captured) or in cont *)
      let in_branch = count_uses k branch in
      let in_cont = count_uses k cont in
      if in_branch > 0 && in_cont > 0 then MultipleUses
      else if in_branch > 0 then
        (match find_and_replace_axiom k replacement_fn branch with
          Found branch' -> Found (NewInt (k', v, branch', cont))
        | other -> other)
      else
        (match find_and_replace_axiom k replacement_fn cont with
          Found cont' -> Found (NewInt (k', v, branch, cont'))
        | other -> other)
  | Add (x, y, r, body) ->
      (match find_and_replace_axiom k replacement_fn body with
        Found body' -> Found (Add (x, y, r, body'))
      | other -> other)
  | Sub (x, y, r, body) ->
      (match find_and_replace_axiom k replacement_fn body with
        Found body' -> Found (Sub (x, y, r, body'))
      | other -> other)
  | Mul (x, y, r, body) ->
      (match find_and_replace_axiom k replacement_fn body with
        Found body' -> Found (Mul (x, y, r, body'))
      | other -> other)
  | Div (x, y, r, body) ->
      (match find_and_replace_axiom k replacement_fn body with
        Found body' -> Found (Div (x, y, r, body'))
      | other -> other)
  | Rem (x, y, r, body) ->
      (match find_and_replace_axiom k replacement_fn body with
        Found body' -> Found (Rem (x, y, r, body'))
      | other -> other)
  | Ifz (v, then_cmd, else_cmd) ->
      (* k might be in both branches - that's OK if at most one use per branch *)
      let in_then = count_uses k then_cmd in
      let in_else = count_uses k else_cmd in
      (* Multiple uses within a single branch is not OK *)
      if in_then > 1 || in_else > 1 then MultipleUses
      (* No uses at all *)
      else if in_then = 0 && in_else = 0 then NotFound
      (* Uses in both branches (at most one each) - try to inline in both *)
      else if in_then > 0 && in_else > 0 then
        (match find_and_replace_axiom k replacement_fn then_cmd,
               find_and_replace_axiom k replacement_fn else_cmd with
          Found then', Found else' -> Found (Ifz (v, then', else'))
        | Found then', NotFound -> Found (Ifz (v, then', else_cmd))
        | NotFound, Found else' -> Found (Ifz (v, then_cmd, else'))
        | NotFound, NotFound -> NotFound
        | _ -> MultipleUses)
      (* Use in only one branch *)
      else if in_then > 0 then
        (match find_and_replace_axiom k replacement_fn then_cmd with
          Found then' -> Found (Ifz (v, then', else_cmd))
        | other -> other)
      else
        (match find_and_replace_axiom k replacement_fn else_cmd with
          Found else' -> Found (Ifz (v, then_cmd, else'))
        | other -> other)
  | Ret (_, _) -> NotFound
  | End -> NotFound

and find_and_replace_in_branches (k: var) (replacement_fn: var -> command)
    (branches: branch list) (rebuild: branch list -> command) : command inline_result =
  (* Check which branches contain k - at most one use per branch is OK *)
  let with_counts = List.map (fun ((_, _, _, body) as br) ->
    (br, count_uses k body)
  ) branches in
  (* Check if any branch has more than one use *)
  let has_multi = List.exists (fun (_, c) -> c > 1) with_counts in
  let has_any = List.exists (fun (_, c) -> c > 0) with_counts in
  if has_multi then MultipleUses
  else if not has_any then NotFound
  else
    (* At most one use per branch - try to inline in all branches that have k *)
    let any_replaced = ref false in
    let replaced_branches = List.map (fun ((xtor, ty_vars, tm_vars, body), cnt) ->
      if cnt = 0 then (xtor, ty_vars, tm_vars, body)
      else
        match find_and_replace_axiom k replacement_fn body with
          Found body' -> any_replaced := true; (xtor, ty_vars, tm_vars, body')
        | _ -> (xtor, ty_vars, tm_vars, body)
    ) with_counts in
    if !any_replaced then Found (rebuild replaced_branches)
    else NotFound

(** Try to find a single Invoke(k, _, xtor, args) and replace it.
    Returns (xtor, args, transformed_cont) if successful. *)
let rec find_and_replace_invoke (k: var) (cmd: command)
    : (sym * var list * (command -> command)) inline_result =
  match cmd with
    Invoke (k', _, xtor, args) when Ident.equal k k' ->
      Found (xtor, args, fun replacement -> replacement)
  | Invoke (_, _, _, _) -> NotFound
  | Let (v, dec, xtor, args, body) ->
      (match find_and_replace_invoke k body with
        Found (x, a, rebuild) ->
          Found (x, a, fun r -> Let (v, dec, xtor, args, rebuild r))
      | other -> other)
  | Switch (v, dec, branches) ->
      find_invoke_in_branches k branches
        (fun bs -> Switch (v, dec, bs))
  | New (k', dec, branches, cont) ->
      (match find_and_replace_invoke k cont with
        Found (x, a, rebuild) ->
          Found (x, a, fun r -> New (k', dec, branches, rebuild r))
      | other -> other)
  | Axiom (_, _, _) -> NotFound
  | Jump (_, _) -> NotFound
  | Lit (n, v, body) ->
      (match find_and_replace_invoke k body with
       | Found (x, a, rebuild) ->
           Found (x, a, fun r -> Lit (n, v, rebuild r))
       | other -> other)
  | NewInt (k', v, branch, cont) ->
      let in_branch = count_uses k branch in
      let in_cont = count_uses k cont in
      if in_branch > 0 && in_cont > 0 then MultipleUses
      else if in_branch > 0 then
        (match find_and_replace_invoke k branch with
          Found (x, a, rebuild) ->
            Found (x, a, fun r -> NewInt (k', v, rebuild r, cont))
        | other -> other)
      else
        (match find_and_replace_invoke k cont with
          Found (x, a, rebuild) ->
            Found (x, a, fun r -> NewInt (k', v, branch, rebuild r))
        | other -> other)
  | Add (x, y, r, body) ->
      (match find_and_replace_invoke k body with
        Found (xtor, a, rebuild) ->
          Found (xtor, a, fun rep -> Add (x, y, r, rebuild rep))
      | other -> other)
  | Sub (x, y, r, body) ->
      (match find_and_replace_invoke k body with
        Found (xtor, a, rebuild) ->
          Found (xtor, a, fun rep -> Sub (x, y, r, rebuild rep))
      | other -> other)
  | Mul (x, y, r, body) ->
      (match find_and_replace_invoke k body with
        Found (xtor, a, rebuild) ->
          Found (xtor, a, fun rep -> Mul (x, y, r, rebuild rep))
      | other -> other)
  | Div (x, y, r, body) ->
      (match find_and_replace_invoke k body with
        Found (xtor, a, rebuild) ->
          Found (xtor, a, fun rep -> Div (x, y, r, rebuild rep))
      | other -> other)
  | Rem (x, y, r, body) ->
      (match find_and_replace_invoke k body with
        Found (xtor, a, rebuild) ->
          Found (xtor, a, fun rep -> Rem (x, y, r, rebuild rep))
      | other -> other)
  | Ifz (v, then_cmd, else_cmd) ->
      let in_then = count_uses k then_cmd in
      let in_else = count_uses k else_cmd in
      if in_then > 0 && in_else > 0 then MultipleUses
      else if in_then > 0 then
        (match find_and_replace_invoke k then_cmd with
          Found (x, a, rebuild) ->
            Found (x, a, fun r -> Ifz (v, rebuild r, else_cmd))
        | other -> other)
      else
        (match find_and_replace_invoke k else_cmd with
          Found (x, a, rebuild) ->
            Found (x, a, fun r -> Ifz (v, then_cmd, rebuild r))
        | other -> other)
  | Ret (_, _) -> NotFound
  | End -> NotFound

and find_invoke_in_branches (k: var) (branches: branch list)
    (rebuild_switch: branch list -> command)
    : (sym * var list * (command -> command)) inline_result =
  let with_counts = List.map (fun ((_, _, _, body) as br) ->
    (br, count_uses k body)
  ) branches in
  let total = List.fold_left (fun acc (_, c) -> acc + c) 0 with_counts in
  if total = 0 then NotFound
  else if total > 1 then MultipleUses
  else
    let rec process prefix = function
        [] -> NotFound
      | ((xtor, ty_vars, tm_vars, body), cnt) :: rest ->
          if cnt = 0 then
            process (prefix @ [(xtor, ty_vars, tm_vars, body)]) rest
          else
            match find_and_replace_invoke k body with
              Found (x, a, rebuild_body) ->
                let rest_branches = List.map fst rest in
                Found (x, a, fun r ->
                  rebuild_switch (prefix @ [(xtor, ty_vars, tm_vars, rebuild_body r)] @ rest_branches))
            | other -> other
    in
    process [] with_counts

(* ========================================================================= *)
(* Main Reduction Pass                                                       *)
(* ========================================================================= *)

(** Reduce a single command, attempting to inline single-use continuations *)
let rec reduce_cmd (cmd: command) : command =
  match cmd with
    NewInt (k, v, branch, cont) ->
      let branch' = reduce_cmd branch in
      let cont' = reduce_cmd cont in
      (* Try to inline: find Axiom(ty, r, k) and replace with branch'[v := r] *)
      (match find_and_replace_axiom k (fun r -> subst_var v r branch') cont' with
        Found result -> result
      | _ -> NewInt (k, v, branch', cont'))
        
  | New (k, dec, branches, cont) ->
      let branches' = List.map reduce_branch branches in
      let cont' = reduce_cmd cont in
      (* Special case: lower.return is administrative boxing - always inline ALL invokes *)
      (match branches' with
       [(xtor, _, tm_vars, body)] when is_lower_return xtor ->
          (* Replace all k.lower.return(args) with body[tm_vars := args] *)
          let result = replace_all_invokes k xtor 
            (fun args -> subst_vars (List.combine tm_vars args) body) cont' in
          (* If k is still used (in non-invoke contexts), keep the New *)
          if count_uses k result > 0 then New (k, dec, branches', result)
          else result
      | _ ->
          (* Normal case: try to inline single-use invoke *)
          (match find_and_replace_invoke k cont' with
            Found (xtor, args, rebuild) ->
              (* Find the matching branch *)
              (match List.find_opt (fun (x, _, _, _) -> Path.equal x xtor) branches' with
                Some (_, _ty_vars, tm_vars, body) ->
                  (* Substitute args for params in the branch body *)
                  let pairs = List.combine tm_vars args in
                  let inlined = subst_vars pairs body in
                  rebuild inlined
              | None ->
                  (* xtor not found - shouldn't happen, keep original *)
                  New (k, dec, branches', cont'))
          | _ -> New (k, dec, branches', cont')))

  (* Recursively reduce in all other constructs *)
  | Let (v, dec, xtor, args, body) ->
      let body' = reduce_cmd body in
      (* Special case: raise.thunk is administrative boxing - always inline ALL switches *)
      if is_raise_thunk xtor then
        (* Replace all `switch v { raise.thunk(params) => branch }` with branch[params := args] *)
        let result = replace_all_switches_with_args v xtor args body' in
        (* If v is still used (in non-switch contexts), keep the Let *)
        if count_uses v result > 0 then Let (v, dec, xtor, args, result)
        else result
      else
        (* Normal case: case-of-known-constructor *)
        (match body' with
          Switch (v', dec', branches) when Ident.equal v v' && Path.equal dec.name dec'.name ->
            (* v is used as switch scrutinee - find matching branch *)
            (match List.find_opt (fun (x, _, _, _) -> Path.equal x xtor) branches with
              Some (_, _ty_vars, tm_vars, branch_body) ->
                (* Only inline if v is not used in branch_body *)
                if count_uses v branch_body = 0 then
                  let pairs = List.combine tm_vars args in
                  subst_vars pairs branch_body
                else
                  Let (v, dec, xtor, args, body')
            | None ->
                (* xtor not found - keep original *)
                Let (v, dec, xtor, args, body'))
        | _ -> Let (v, dec, xtor, args, body'))
  | Switch (v, dec, branches) ->
      Switch (v, dec, List.map reduce_branch branches)
  | Invoke (v, dec, xtor, args) ->
      Invoke (v, dec, xtor, args)
  | Jump (label, args) ->
      Jump (label, args)
  | Axiom (ty, v, k) ->
      Axiom (ty, v, k)
  | Lit (n, v, body) ->
      Lit (n, v, reduce_cmd body)
  | Add (x, y, r, body) ->
      Add (x, y, r, reduce_cmd body)
  | Sub (x, y, r, body) ->
      Sub (x, y, r, reduce_cmd body)
  | Mul (x, y, r, body) ->
      Mul (x, y, r, reduce_cmd body)
  | Div (x, y, r, body) ->
      Div (x, y, r, reduce_cmd body)
  | Rem (x, y, r, body) ->
      Rem (x, y, r, reduce_cmd body)
  | Ifz (v, then_cmd, else_cmd) ->
      Ifz (v, reduce_cmd then_cmd, reduce_cmd else_cmd)
  | Ret (ty, v) ->
      Ret (ty, v)
  | End -> End

and reduce_branch ((xtor, ty_vars, tm_vars, body): branch) : branch =
  (xtor, ty_vars, tm_vars, reduce_cmd body)

(** Reduce a definition *)
let reduce_def (def: definition) : definition =
  { def with body = reduce_cmd def.body }

(** Reduce all definitions *)
let reduce_defs (defs: definition Path.tbl) : definition Path.tbl =
  Path.map_tbl reduce_def defs
