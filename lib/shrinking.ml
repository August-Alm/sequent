(**
  Module: Shrinking
  Pass 1: Naming + Shrinking (Core -> Core)
  
  Implements the complete naming and shrinking transformation from normalization.txt:
  
  1. Naming: Lift non-variable arguments to ANF using μ/μ̃ bindings
  2. Renaming: ⟨x | μ̃y.s⟩ → s{y→x} and ⟨μβ.s | α⟩ → s{β→α}
  3. Known cuts: ⟨C(Γ) | case⟩ and ⟨cocase | D(Γ)⟩
  4. Unknown cuts: ⟨x | α⟩ with η-expansion
  5. Critical pairs: ⟨μα.s | μ̃x.s⟩ with η-expansion
*)

open Common.Identifiers
open Common.Types
module CT = Core.Terms

type shrink_context = {
  defs: CT.definitions;
}

let fresh_var =
  let counter = ref 0 in
  fun () ->
    incr counter;
    Ident.mk (Printf.sprintf "x%d" !counter)

let fresh_covar =
  let counter = ref 0 in
  fun () ->
    incr counter;
    Ident.mk (Printf.sprintf "a%d" !counter)

(** Substitution on Core AST *)
let rec subst_producer (subst: (Ident.t * Ident.t) list) (p: CT.producer) : CT.producer =
  match p with
  | CT.Var x -> CT.Var (List.assoc_opt x subst |> Option.value ~default:x)
  | CT.Mu (alpha, s) -> 
    let subst' = List.filter (fun (v, _) -> not (Ident.equal v alpha)) subst in
    CT.Mu (alpha, subst_statement subst' s)
  | CT.Constructor (ctor, (ty_args, prods, cons)) ->
    CT.Constructor (ctor, (ty_args, 
                           List.map (subst_producer subst) prods, 
                           List.map (subst_consumer subst) cons))
  | CT.Cocase patterns ->
    CT.Cocase (List.map (subst_pattern subst) patterns)
  | CT.Int n -> CT.Int n

and subst_consumer (subst: (Ident.t * Ident.t) list) (c: CT.consumer) : CT.consumer =
  match c with
  | CT.Covar alpha -> CT.Covar (List.assoc_opt alpha subst |> Option.value ~default:alpha)
  | CT.MuTilde (x, s) ->
    let subst' = List.filter (fun (v, _) -> not (Ident.equal v x)) subst in
    CT.MuTilde (x, subst_statement subst' s)
  | CT.Destructor (dtor, (ty_args, prods, cons)) ->
    CT.Destructor (dtor, (ty_args, 
                         List.map (subst_producer subst) prods, 
                         List.map (subst_consumer subst) cons))
  | CT.Case patterns ->
    CT.Case (List.map (subst_pattern subst) patterns)

and subst_statement (subst: (Ident.t * Ident.t) list) (s: CT.statement) : CT.statement =
  match s with
  | CT.Cut (p, ty, c) -> CT.Cut (subst_producer subst p, ty, subst_consumer subst c)
  | CT.Add (p1, p2, c) -> CT.Add (subst_producer subst p1, subst_producer subst p2, subst_consumer subst c)
  | CT.Call (f, ty_args, prods, cons) ->
    CT.Call (f, ty_args, 
            List.map (subst_producer subst) prods, 
            List.map (subst_consumer subst) cons)

and subst_pattern (subst: (Ident.t * Ident.t) list) (pat: CT.pattern) : CT.pattern =
  let bound_vars = pat.variables @ pat.covariables in
  let subst' = List.filter (fun (v, _) -> 
    not (List.exists (Ident.equal v) bound_vars)
  ) subst in
  { pat with statement = subst_statement subst' pat.statement }

(** Check if type is data (vs codata) *)
let is_data_type (ctx: shrink_context) (ty: typ) : bool option =
  match ty with
  | TyDef (Data _) -> Some true
  | TyDef (Code _) -> Some false
  | TySym path ->
    (* Look up the type symbol in definitions *)
    (match List.assoc_opt path ctx.defs.type_defs with
    | Some (Data _, _) -> Some true
    | Some (Code _, _) -> Some false
    | Some (Prim _, _) -> None
    | None -> None)
  | _ -> None

(** Get constructors/destructors from type *)
let get_xtors (ctx: shrink_context) (ty: typ) : ty_xtor list option =
  match ty with
  | TyDef (Data td) -> Some td.xtors
  | TyDef (Code td) -> Some td.xtors
  | TySym path ->
    (* Look up the type symbol in definitions *)
    (match List.assoc_opt path ctx.defs.type_defs with
    | Some (Data td, _) -> Some td.xtors
    | Some (Code td, _) -> Some td.xtors
    | Some (Prim _, _) -> None
    | None -> None)
  | _ -> None

(** Main shrinking transformation *)
let rec shrink_statement (ctx: shrink_context) (s: CT.statement) : CT.statement =
  match s with
  | CT.Cut (p, ty, c) -> shrink_cut ctx p ty c
  | CT.Add _ as add -> add
  | CT.Call (f, ty_args, prods, cons) -> shrink_call ctx f ty_args prods cons

(** Shrink a call: apply naming to ensure all arguments are variables *)
and shrink_call (ctx: shrink_context) (f: Path.t) (ty_args: typ list) 
    (prods: CT.producer list) (cons: CT.consumer list) : CT.statement =
  (* Check if all producers are variables *)
  let all_prods_vars = List.for_all (function CT.Var _ -> true | _ -> false) prods in
  let all_cons_vars = List.for_all (function CT.Covar _ -> true | _ -> false) cons in
  

  if all_prods_vars && all_cons_vars then
    (* All arguments are already variables, return as-is *)
    CT.Call (f, ty_args, prods, cons)
  else
    (* Apply naming: lift non-variable arguments *)
    (* Use a dummy type for intermediate bindings - the actual type doesn't matter for µ/µ̃ *)
    let dummy_ty = TySym (Path.of_string "?") in
    let rec lift_prods prods_acc = function
      | [] -> lift_cons prods_acc [] cons
      | (CT.Var _ as v) :: rest -> lift_prods (v :: prods_acc) rest
      | p :: rest ->
        (* Lift non-variable producer *)

        let x = fresh_var () in
        (* Shrink the new cut to handle nested non-variable terms *)
        shrink_cut ctx p dummy_ty (CT.MuTilde (x, 
          CT.Call (f, ty_args, List.rev prods_acc @ (CT.Var x :: rest), cons)))
    and lift_cons prods_acc cons_acc = function
      | [] -> 
        (* All arguments are variables now *)
        CT.Call (f, ty_args, List.rev prods_acc, List.rev cons_acc)
      | (CT.Covar _ as cov) :: rest -> lift_cons prods_acc (cov :: cons_acc) rest
      | c :: rest ->
        (* Lift non-variable consumer *)

        let alpha = fresh_covar () in
        (* Shrink the new cut to handle nested non-variable terms *)
        shrink_cut ctx (CT.Mu (alpha,
          CT.Call (f, ty_args, List.rev prods_acc, List.rev cons_acc @ (CT.Covar alpha :: rest)))) 
          dummy_ty c
    in
    lift_prods [] prods

(** Shrink a cut: apply reduction rules from normalization.txt *)
and shrink_cut (ctx: shrink_context) (p: CT.producer) (ty: typ) (c: CT.consumer) : CT.statement =
  match (p, c) with
  
  (* RENAMING: ⟨x | μ̃y.s⟩ → s{y → x} *)
  | (CT.Var x, CT.MuTilde (y, s)) ->
    shrink_statement ctx (subst_statement [(y, x)] (shrink_statement ctx s))
  
  (* RENAMING: ⟨μβ.s | α⟩ → s{β → α} *)
  | (CT.Mu (beta, s), CT.Covar alpha) ->
    shrink_statement ctx (subst_statement [(beta, alpha)] (shrink_statement ctx s))
  
  (* KNOWN CUT: ⟨C(Γ0) | case {..., C(Γ) ⇒ s, ...}⟩ → s{Γ → Γ0} *)
  | (CT.Constructor (ctor, (_, prods, cons)), CT.Case patterns) ->
    (match List.find_opt (fun (pat: CT.pattern) -> Path.equal pat.xtor ctor) patterns with
     | Some pat ->
       (* Extract variables from arguments *)
       let prod_vars = List.map (function CT.Var x -> x | _ -> failwith "Expected variables after naming") prods in
       let cons_vars = List.map (function CT.Covar a -> a | _ -> failwith "Expected covariables after naming") cons in
       let subst = List.combine (pat.variables @ pat.covariables) (prod_vars @ cons_vars) in
       shrink_statement ctx (subst_statement subst pat.statement)
     | None -> failwith "No matching pattern in case")
  
  (* KNOWN CUT: ⟨cocase {..., D(Γ) ⇒ s, ...} | D(Γ0)⟩ → s{Γ → Γ0} *)
  | (CT.Cocase patterns, CT.Destructor (dtor, (_, prods, cons))) ->
    (match List.find_opt (fun (pat: CT.pattern) -> Path.equal pat.xtor dtor) patterns with
     | Some pat ->
       let prod_vars = List.map (function CT.Var x -> x | _ -> failwith "Expected variables") prods in
       let cons_vars = List.map (function CT.Covar a -> a | _ -> failwith "Expected covariables") cons in
       let subst = List.combine (pat.variables @ pat.covariables) (prod_vars @ cons_vars) in
       shrink_statement ctx (subst_statement subst pat.statement)
     | None -> failwith "No matching pattern in cocase")
  
  (* NAMING: Lift non-variable arguments in constructors *)
  | (CT.Constructor (ctor, (ty_args, prods, cons)), c) 
    when not (List.for_all (function CT.Var _ -> true | _ -> false) prods &&
              List.for_all (function CT.Covar _ -> true | _ -> false) cons) ->
    let rec lift_prods prods_acc = function
      | [] -> lift_cons prods_acc [] cons
      | (CT.Var _ as v) :: rest -> lift_prods (v :: prods_acc) rest
      | p :: rest ->
        let x = fresh_var () in
        CT.Cut (p, ty, CT.MuTilde (x, 
          shrink_statement ctx (CT.Cut (
            CT.Constructor (ctor, (ty_args, List.rev prods_acc @ (CT.Var x :: rest), cons)),
            ty, c))))
    and lift_cons prods_acc cons_acc = function
      | [] -> 
        (* All arguments are variables, continue with other patterns *)
        let prods' = List.rev prods_acc in
        let cons' = List.rev cons_acc in
        shrink_cut ctx (CT.Constructor (ctor, (ty_args, prods', cons'))) ty c
      | (CT.Covar _ as cov) :: rest -> lift_cons prods_acc (cov :: cons_acc) rest
      | cons :: rest ->
        let alpha = fresh_covar () in
        CT.Cut (CT.Mu (alpha,
          shrink_statement ctx (CT.Cut (
            CT.Constructor (ctor, (ty_args, List.rev prods_acc, List.rev cons_acc @ (CT.Covar alpha :: rest))),
            ty, cons))), ty, cons)
    in
    lift_prods [] prods
  
  (* NAMING: Lift non-variable arguments in destructors *)
  | (p, CT.Destructor (dtor, (ty_args, prods, cons)))
    when not (List.for_all (function CT.Var _ -> true | _ -> false) prods &&
              List.for_all (function CT.Covar _ -> true | _ -> false) cons) ->
    let rec lift_prods prods_acc = function
      | [] -> lift_cons prods_acc [] cons
      | (CT.Var _ as v) :: rest -> lift_prods (v :: prods_acc) rest
      | prod :: rest ->
        let x = fresh_var () in
        CT.Cut (prod, ty, CT.MuTilde (x,
          shrink_statement ctx (CT.Cut (
            p,
            ty,
            CT.Destructor (dtor, (ty_args, List.rev prods_acc @ (CT.Var x :: rest), cons))))))
    and lift_cons prods_acc cons_acc = function
      | [] ->
        (* All arguments are variables, continue with other patterns *)
        let prods' = List.rev prods_acc in
        let cons' = List.rev cons_acc in
        shrink_cut ctx p ty (CT.Destructor (dtor, (ty_args, prods', cons')))
      | (CT.Covar _ as cov) :: rest -> lift_cons prods_acc (cov :: cons_acc) rest
      | cons :: rest ->
        let alpha = fresh_covar () in
        CT.Cut (CT.Mu (alpha,
          shrink_statement ctx (CT.Cut (
            p,
            ty,
            CT.Destructor (dtor, (ty_args, List.rev prods_acc, List.rev cons_acc @ (CT.Covar alpha :: rest)))))), ty, cons)
    in
    lift_prods [] prods
  
  (* η-EXPANSION: ⟨x | α⟩ at data type → expand consumer *)
  | (CT.Var x, CT.Covar alpha) ->
    (match is_data_type ctx ty with
     | Some true ->
       (* data type: expand consumer with case *)
       (match get_xtors ctx ty with
        | Some xtors ->
          let patterns = List.map (fun xtor ->
            let vars = List.map (fun _ -> fresh_var ()) xtor.producers in
            let covars = List.map (fun _ -> fresh_covar ()) xtor.consumers in
            {
              CT.xtor = xtor.symbol;
              type_vars = List.map fst xtor.quantified;
              variables = vars;
              covariables = covars;
              statement = CT.Cut (
                CT.Constructor (xtor.symbol, ([], 
                                             List.map (fun v -> CT.Var v) vars,
                                             List.map (fun a -> CT.Covar a) covars)),
                ty,
                CT.Covar alpha
              )
            }
          ) xtors in
          shrink_statement ctx (CT.Cut (CT.Var x, ty, CT.Case patterns))
        | None -> CT.Cut (p, ty, c))
     | Some false ->
       (* codata type: expand producer with cocase *)
       (match get_xtors ctx ty with
        | Some xtors ->
          let patterns = List.map (fun xtor ->
            let vars = List.map (fun _ -> fresh_var ()) xtor.producers in
            let covars = List.map (fun _ -> fresh_covar ()) xtor.consumers in
            {
              CT.xtor = xtor.symbol;
              type_vars = List.map fst xtor.quantified;
              variables = vars;
              covariables = covars;
              statement = CT.Cut (
                CT.Var x,
                ty,
                CT.Destructor (xtor.symbol, ([],
                                            List.map (fun v -> CT.Var v) vars,
                                            List.map (fun a -> CT.Covar a) covars))
              )
            }
          ) xtors in
          shrink_statement ctx (CT.Cut (CT.Cocase patterns, ty, CT.Covar alpha))
        | None -> CT.Cut (p, ty, c))
     | None -> CT.Cut (p, ty, c))
  
  (* CRITICAL PAIR: ⟨μα.s1 | μ̃x.s2⟩ at data type → expand μ̃ *)
  | (CT.Mu (alpha, s1), CT.MuTilde (x, s2)) ->
    (match is_data_type ctx ty with
     | Some true ->
       (* data type: expand μ̃ with case *)
       (match get_xtors ctx ty with
        | Some xtors ->
          let patterns = List.map (fun xtor ->
            let vars = List.map (fun _ -> fresh_var ()) xtor.producers in
            let covars = List.map (fun _ -> fresh_covar ()) xtor.consumers in
            {
              CT.xtor = xtor.symbol;
              type_vars = List.map fst xtor.quantified;
              variables = vars;
              covariables = covars;
              statement = CT.Cut (
                CT.Constructor (xtor.symbol, ([],
                                             List.map (fun v -> CT.Var v) vars,
                                             List.map (fun a -> CT.Covar a) covars)),
                ty,
                CT.MuTilde (x, shrink_statement ctx s2)
              )
            }
          ) xtors in
          shrink_statement ctx (CT.Cut (CT.Mu (alpha, shrink_statement ctx s1), ty, CT.Case patterns))
        | None -> 
          Printf.eprintf "Warning: Critical pair but no xtors for type\n%!";
          CT.Cut (CT.Mu (alpha, shrink_statement ctx s1), ty, CT.MuTilde (x, shrink_statement ctx s2)))
     | Some false ->
       (* codata type: expand μ with cocase *)
       (match get_xtors ctx ty with
        | Some xtors ->
          let patterns = List.map (fun xtor ->
            let vars = List.map (fun _ -> fresh_var ()) xtor.producers in
            let covars = List.map (fun _ -> fresh_covar ()) xtor.consumers in
            {
              CT.xtor = xtor.symbol;
              type_vars = List.map fst xtor.quantified;
              variables = vars;
              covariables = covars;
              statement = CT.Cut (
                CT.Mu (alpha, shrink_statement ctx s1),
                ty,
                CT.Destructor (xtor.symbol, ([],
                                            List.map (fun v -> CT.Var v) vars,
                                            List.map (fun a -> CT.Covar a) covars))
              )
            }
          ) xtors in
          shrink_statement ctx (CT.Cut (CT.Cocase patterns, ty, CT.MuTilde (x, shrink_statement ctx s2)))
        | None -> 
          Printf.eprintf "Warning: Critical pair but no xtors for codata type\n%!";
          CT.Cut (CT.Mu (alpha, shrink_statement ctx s1), ty, CT.MuTilde (x, shrink_statement ctx s2)))
     | None -> 
       Printf.eprintf "Warning: Critical pair but type is not recognized\n%!";
       CT.Cut (CT.Mu (alpha, shrink_statement ctx s1), ty, CT.MuTilde (x, shrink_statement ctx s2)))
  
  (* All other forms: recursively shrink subterms *)
  | (CT.Mu (alpha, s), _) -> 
    CT.Cut (CT.Mu (alpha, shrink_statement ctx s), ty, c)
  | (_, CT.MuTilde (x, s)) ->
    CT.Cut (p, ty, CT.MuTilde (x, shrink_statement ctx s))
  | (CT.Cocase patterns, _) ->
    let patterns' = List.map (fun (pat: CT.pattern) ->
      { pat with statement = shrink_statement ctx pat.statement }
    ) patterns in
    CT.Cut (CT.Cocase patterns', ty, c)
  | (_, CT.Case patterns) ->
    let patterns' = List.map (fun (pat: CT.pattern) ->
      { pat with statement = shrink_statement ctx pat.statement }
    ) patterns in
    CT.Cut (p, ty, CT.Case patterns')
  | _ -> CT.Cut (p, ty, c)

(** Shrink a term definition *)
let shrink_term_def (ctx: shrink_context) (def: CT.term_def) : CT.term_def =
  { def with body = shrink_statement ctx def.body }

(** Entry point *)
let shrink_definitions (defs: CT.definitions) : CT.definitions =
  let ctx = { defs } in
  let term_defs' = List.map (fun (name, def) -> 
    (name, shrink_term_def ctx def)
  ) defs.term_defs in
  { defs with term_defs = term_defs' }
