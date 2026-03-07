(**
  module: Focused.Return
  description: Utility for closing focused commands by replacing return
  continuations with Ret.

  When main returns an integer, it has a return continuation parameter k.
  To close it, we:
  1. Remove k from the parameters
  2. Wrap the body with: NewInt k { v => Ret v }; body
  
  This way any use of k (whether direct axiom or passed to other functions)
  naturally flows through the NewInt and returns via Ret.
*)
open Common.Identifiers
open Terms

let close_ret_var (ret_ty: Types.FocusedTypes.typ) (ret_k: Ident.t) (cmd: command) : command =
  let result_v = Ident.fresh () in
  NewInt (ret_k, result_v, Ret (ret_ty, result_v), cmd)

(** Close main's return continuation by wrapping the body with NewInt.
   
   Given:
     def main(x1, ..., xN, k: cns int) = body
   
   Produces:
     def main_c(x1, ..., xN) = NewInt k { v => Ret v }; body
   
   The ret_k parameter should be removed from term_params by the caller.
*)
let close_main (main: definition) : definition = 
  match List.rev main.term_params with
    (ret_k, Types.FocusedBase.Cns ret_ty) :: rest_params_rev ->
      (* Close by: 1) removing ret_k from params, 2) wrapping body with NewInt *)
      let new_params = List.rev rest_params_rev in
      let closed_body = close_ret_var ret_ty ret_k main.body in
      { main with term_params = new_params; body = closed_body }
  | _ -> main