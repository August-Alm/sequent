(** Free variables in Core AST *)

open Common.Identifiers
open Terms

let rec free_vars_producer (p: producer) : Ident.t list =
  match p with
  | Var x -> [x]
  | Mu (alpha, s) ->
    List.filter (fun v -> not (Ident.equal v alpha)) (free_vars_statement s)
  | Constructor (_ctor, (_ty_args, prods, cons)) ->
    List.concat_map free_vars_producer prods @
    List.concat_map free_vars_consumer cons
  | Cocase patterns ->
    List.concat_map free_vars_pattern patterns
  | Int _ -> []

and free_vars_consumer (c: consumer) : Ident.t list =
  match c with
  | Covar alpha -> [alpha]
  | MuTilde (x, s) ->
    List.filter (fun v -> not (Ident.equal v x)) (free_vars_statement s)
  | Destructor (_dtor, (_ty_args, prods, cons)) ->
    List.concat_map free_vars_producer prods @
    List.concat_map free_vars_consumer cons
  | Case patterns ->
    List.concat_map free_vars_pattern patterns

and free_vars_statement (s: statement) : Ident.t list =
  match s with
  | Cut (p, _ty, c) ->
    free_vars_producer p @ free_vars_consumer c
  | Add (p1, p2, c) ->
    free_vars_producer p1 @ free_vars_producer p2 @ free_vars_consumer c
  | Call (_f, _ty_args, prods, cons) ->
    List.concat_map free_vars_producer prods @
    List.concat_map free_vars_consumer cons

and free_vars_pattern (pat: pattern) : Ident.t list =
  let bound_vars = pat.variables @ pat.covariables in
  let free_in_body = free_vars_statement pat.statement in
  List.filter (fun v -> not (List.mem v bound_vars)) free_in_body
