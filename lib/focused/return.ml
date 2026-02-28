(**
  module: Focused.Return
  description: Utility for closing focused commands by replacing return
  continuations with Ret.

  Return continuations are represented as continuation variables (e.g., 'k')
  that are passed around. When we want to "close" a command (e.g., the body of
  main) by replacing the return continuation with an actual primitive return (Ret),
  that represents the outside world.
*)
open Common.Identifiers
open Types.FocusedTypes
open Terms

(* Close a focused command by replacing axiom/invoke on 'ret' with Ret.
   This is applied after focusing main to properly terminate the program. *)
let rec close_ret (ret_ty: typ) (cmd: command) : command =
  match cmd with
  | Axiom (_, v, k) when Ident.name k = "ret" -> Ret (ret_ty, v)
  | Invoke (k, _, _, args) when Ident.name k = "ret" ->
      (match args with v :: _ -> Ret (ret_ty, v) | [] -> cmd)
  | Switch (k, sg, branches) when Ident.name k = "ret" ->
      let v = Ident.fresh () in
      let branches' = List.map (fun (xtor, ty_vars, tm_vars, b) ->
        (xtor, ty_vars, tm_vars, close_ret ret_ty b)
      ) branches in
      New (v, sg, branches', Ret (ret_ty, v))
  | Let (v, dec, xtor, args, body) -> 
      Let (v, dec, xtor, args, close_ret ret_ty body)
  | New (v, sg, branches, body) ->
      let branches' = List.map (fun (xtor, ty_vars, tm_vars, b) ->
        (xtor, ty_vars, tm_vars, close_ret ret_ty b)
      ) branches in
      New (v, sg, branches', close_ret ret_ty body)
  | Switch (x, sg, branches) ->
      let branches' = List.map (fun (xtor, ty_vars, tm_vars, b) ->
        (xtor, ty_vars, tm_vars, close_ret ret_ty b)
      ) branches in
      Switch (x, sg, branches')
  | Lit (n, v, body) -> Lit (n, v, close_ret ret_ty body)
  | Add (a, b, r, body) -> Add (a, b, r, close_ret ret_ty body)
  | Sub (a, b, r, body) -> Sub (a, b, r, close_ret ret_ty body)
  | NewInt (k, v, branch, cont) ->
      NewInt (k, v, close_ret ret_ty branch, close_ret ret_ty cont)
  | Ifz (v, t, e) -> Ifz (v, close_ret ret_ty t, close_ret ret_ty e)
  | Jump (p, args) -> Jump (p, args)
  | Ret (ty, v) -> Ret (ty, v)
  | End -> End
  | Axiom (ty, v, k) -> Axiom (ty, v, k)
  | Invoke (k, dec, xtor, args) -> Invoke (k, dec, xtor, args)

(* Close a focused command by replacing axiom/invoke on a specific return continuation
   variable with Ret. This is used for main where the return continuation is a 
   fresh variable, not named "ret". *)
let rec close_ret_var (ret_ty: typ) (ret_k: Ident.t) (cmd: command) : command =
  let open Terms in
  let open Common.Identifiers in
  match cmd with
  | Axiom (_, v, k) when Ident.equal k ret_k -> Ret (ret_ty, v)
  | Invoke (k, _, _, args) when Ident.equal k ret_k ->
      (match args with v :: _ -> Ret (ret_ty, v) | [] -> cmd)
  | Switch (k, sg, branches) when Ident.equal k ret_k ->
      let v = Ident.fresh () in
      let branches' = List.map (fun (xtor, ty_vars, tm_vars, b) ->
        (xtor, ty_vars, tm_vars, close_ret_var ret_ty ret_k b)
      ) branches in
      New (v, sg, branches', Ret (ret_ty, v))
  | Let (v, dec, xtor, args, body) -> 
      (* If ret_k appears in args (e.g., as a continuation argument to a destructor),
        we need to wrap with NewInt to capture the result that flows to ret_k *)
      if List.exists (Ident.equal ret_k) args then
        let result_v = Ident.fresh () in
        let new_ret_k = Ident.fresh () in
        let new_args = List.map (fun a ->
          if Ident.equal a ret_k then new_ret_k else a
        ) args in
        NewInt (new_ret_k, result_v, Ret (ret_ty, result_v),
          Let (v, dec, xtor, new_args, close_ret_var ret_ty ret_k body))
      else
        Let (v, dec, xtor, args, close_ret_var ret_ty ret_k body)
  | New (v, sg, branches, body) ->
      let branches' = List.map (fun (xtor, ty_vars, tm_vars, b) ->
        (xtor, ty_vars, tm_vars, close_ret_var ret_ty ret_k b)
      ) branches in
      New (v, sg, branches', close_ret_var ret_ty ret_k body)
  | Switch (x, sg, branches) ->
      let branches' = List.map (fun (xtor, ty_vars, tm_vars, b) ->
        (xtor, ty_vars, tm_vars, close_ret_var ret_ty ret_k b)
      ) branches in
      Switch (x, sg, branches')
  | Lit (n, v, body) -> Lit (n, v, close_ret_var ret_ty ret_k body)
  | Add (a, b, r, body) -> Add (a, b, r, close_ret_var ret_ty ret_k body)
  | Sub (a, b, r, body) -> Sub (a, b, r, close_ret_var ret_ty ret_k body)
  | NewInt (k, v, branch, cont) ->
      NewInt (k, v, close_ret_var ret_ty ret_k branch, close_ret_var ret_ty ret_k cont)
  | Ifz (v, t, e) -> Ifz (v, close_ret_var ret_ty ret_k t, close_ret_var ret_ty ret_k e)
  | Jump (p, args) -> 
      (* For jump to another function with ret_k in args, we need to handle this.
         When main tail-calls another function passing ret_k, that function's result
         should go to the outside world. We wrap with NewInt to capture the result. *)
      if List.exists (Ident.equal ret_k) args then
        let result_v = Ident.fresh () in
        let new_ret_k = Ident.fresh () in
        let new_args = List.map (fun a -> if Ident.equal a ret_k then new_ret_k else a) args in
        NewInt (new_ret_k, result_v, Ret (ret_ty, result_v), Jump (p, new_args))
      else
        Jump (p, args)
  | Ret (ty, v) -> Ret (ty, v)
  | End -> End
  | Axiom (ty, v, k) -> Axiom (ty, v, k)
  | Invoke (k, dec, xtor, args) -> Invoke (k, dec, xtor, args)
