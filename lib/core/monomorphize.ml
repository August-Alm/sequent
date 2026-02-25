(**
  module: Core.Monomorphize
  description: Monomorphization transformation for the Core language.
  
  This module transforms polymorphic definitions into monomorphic ones by:
  1. Analyzing flow constraints to find all type instantiations
  2. For each polymorphic definition, generating a codata type where each
     destructor carries the specialized term parameters
  3. Transforming the polymorphic definition into a monomorphic one that
     takes a single consumer of the codata type
  4. Transforming call sites to use the appropriate destructor
  
  Example transformation:
  
    def id{a}(x: Prd a, k: Cns a) = ⟨x | k⟩
    
    with instantiations [int, bool] becomes:
    
    codata id.For where
      inst_0(x: Prd int, k: Cns int) : id.For
      inst_1(x: Prd bool, k: Cns bool) : id.For
    
    def id.mono(u: Cns id.For) =
      ⟨Comatch(id.For, [
          inst_0(x, k) => ⟨x | k⟩
          inst_1(x, k) => ⟨x | k⟩
        ]) | u⟩
    
    Call site id{int}(42, k) becomes:
      Call(id.mono, [], [Dtor(id.For, inst_0, [42, k])])
*)

open Common.Identifiers
open Common.Types
open Types.CoreBase
open Types.CoreTypes

(* Open Terms for direct access to term/command constructors *)
module T = Terms

(* ========================================================================= *)
(* Types for Monomorphization                                                *)
(* ========================================================================= *)

(** A specific instantiation of type parameters *)
type instantiation = Specialization.ground_arg list

(** Information about a polymorphic definition's monomorphization *)
type mono_info = 
  { original_path: Path.t
  ; type_params: (Ident.t * typ) list   (* Original type parameters *)
  ; term_params: (Ident.t * chiral_typ) list  (* Original term parameters *)
  ; instantiations: instantiation list  (* All discovered instantiations *)
  ; generated_codata: dec               (* The generated For_X codata type *)
  ; mono_path: Path.t                   (* Path of monomorphized definition *)
  }

(** Result of monomorphization *)
type mono_result =
  { main: Terms.definition
  ; definitions: Terms.definition list
  ; new_declarations: dec list
  ; mono_infos: mono_info Path.tbl      (* keyed by original definition path *)
  }

(* ========================================================================= *)
(* Error Types                                                               *)
(* ========================================================================= *)

(** Errors that can occur during monomorphization *)
type mono_error =
  | GrowingCycle of (Path.t * int) list
  | NoMatchingInstantiation of
      { def_path: Path.t; instantiation: Specialization.ground_arg list }

type 'a mono_check = ('a, mono_error) result

let ( let* ) = Result.bind

(* ========================================================================= *)
(* Instantiation Utilities                                                   *)
(* ========================================================================= *)

(** Convert ground_arg to a Core typ *)
let rec ground_arg_to_typ (arg: Specialization.ground_arg): typ =
  match arg with
    Specialization.GroundExt Int -> Ext Int
  | Specialization.GroundSgn (name, args) ->
      Sgn (name, List.map ground_arg_to_typ args)

(** Generate destructor name for an instantiation *)
let dtor_name_for_inst (base_path: Path.t) (idx: int): Path.t =
  Path.access base_path ("inst_" ^ string_of_int idx)

(** Apply type substitution to a chiral type *)
let apply_subst_chiral (subst: typ Ident.tbl) (ct: chiral_typ): chiral_typ =
  chiral_map (apply_fresh_subst subst) ct

(* ========================================================================= *)
(* Codata Generation                                                         *)
(* ========================================================================= *)

(** Generate the codata declaration for a polymorphic definition.
    
    For a definition like:
      def foo{a, b}(x: T1[a], y: T2[b], k: R[a,b]) = body
    
    With instantiations [(int, bool), (string, char)], generates:
    
    codata foo.For where
      inst_0(x: T1[int], y: T2[bool], k: R[int,bool]) : foo.For
      inst_1(x: T1[string], y: T2[char], k: R[string,char]) : foo.For
    
    Note: The destructor arguments are the specialized term parameters,
    and the main type is the codata type itself.
*)
let generate_codata_for_def 
    (def: T.definition)
    (instantiations: instantiation list)
    : dec * Path.t =
  
  let codata_name = Path.access def.path "For" in
  let codata_typ = Sgn (codata_name, []) in
  
  let xtors = List.mapi (fun idx inst ->
    (* Create substitution: type_param_i -> inst_arg_i *)
    let subst = List.fold_left2 (fun acc (tvar, _kind) arg ->
      Ident.add tvar (ground_arg_to_typ arg) acc
    ) Ident.emptytbl def.type_params inst in
    
    (* Specialize the term parameter types *)
    let specialized_params = List.map (fun (_var, ct) ->
      apply_subst_chiral subst ct
    ) def.term_params in
    
    { name = dtor_name_for_inst codata_name idx
    ; quantified = []
    ; existentials = []
    ; argument_types = specialized_params  (* Destructor carries the args! *)
    ; main = codata_typ                    (* Main type is the codata itself *)
    }
  ) instantiations in
  
  let codata_dec = 
    { name = codata_name
    ; data_sort = Codata
    ; param_kinds = []
    ; type_args = []
    ; xtors
    } in
  
  (codata_dec, codata_name)

(* ========================================================================= *)
(* Type Substitution in Terms and Commands                                   *)
(* ========================================================================= *)

(** Apply type substitution throughout a term *)
let rec subst_term (subst: typ Ident.tbl) (tm: T.term): T.term =
  match tm with
    T.Var _ | T.Lit _ -> tm
  | T.Ctor (dec, xtor, args) ->
      let dec' = subst_dec subst dec in
      T.Ctor (dec', xtor, List.map (subst_term subst) args)
  | T.Dtor (dec, xtor, args) ->
      let dec' = subst_dec subst dec in
      T.Dtor (dec', xtor, List.map (subst_term subst) args)
  | T.Match (dec, branches) ->
      let dec' = subst_dec subst dec in
      T.Match (dec', List.map (subst_branch subst) branches)
  | T.Comatch (dec, branches) ->
      let dec' = subst_dec subst dec in
      T.Comatch (dec', List.map (subst_branch subst) branches)
  | T.MuPrd (typ, var, cmd) ->
      T.MuPrd (apply_fresh_subst subst typ, var, subst_command subst cmd)
  | T.MuCns (typ, var, cmd) ->
      T.MuCns (apply_fresh_subst subst typ, var, subst_command subst cmd)
  | T.NewForall (tvar, kind, body_typ, cmd) ->
      (* Remove tvar from substitution to avoid capture *)
      let subst' = Ident.filter (fun k _ -> not (Ident.equal k tvar)) subst in
      T.NewForall (tvar, apply_fresh_subst subst' kind, 
                   apply_fresh_subst subst' body_typ, 
                   subst_command subst' cmd)
  | T.InstantiateDtor typ ->
      T.InstantiateDtor (apply_fresh_subst subst typ)

and subst_branch (subst: typ Ident.tbl) ((xtor, tvars, tmvars, cmd): T.branch): T.branch =
  (* Remove bound type vars from substitution *)
  let subst' = List.fold_left (fun s tv ->
    Ident.filter (fun k _ -> not (Ident.equal k tv)) s
  ) subst tvars in
  (xtor, tvars, tmvars, subst_command subst' cmd)

and subst_command (sbs: typ Ident.tbl) (cmd: T.command): T.command =
  match cmd with
    T.Cut (typ, p, c) ->
      T.Cut (apply_fresh_subst sbs typ, subst_term sbs p, subst_term sbs c)
  | T.Call (path, typs, args) ->
      T.Call (path, List.map (apply_fresh_subst sbs) typs, List.map (subst_term sbs) args)
  | T.Add (t1, t2, t3) ->
      T.Add (subst_term sbs t1, subst_term sbs t2, subst_term sbs t3)
  | T.Sub (t1, t2, t3) ->
      T.Sub (subst_term sbs t1, subst_term sbs t2, subst_term sbs t3)
  | T.Ifz (cond, then_cmd, else_cmd) ->
      T.Ifz (subst_term sbs cond, subst_command sbs then_cmd, subst_command sbs else_cmd)
  | T.Ret (typ, tm) ->
      T.Ret (apply_fresh_subst sbs typ, subst_term sbs tm)
  | T.End -> T.End

and subst_dec (sbs: typ Ident.tbl) (dec: dec): dec =
  { dec with
    param_kinds = List.map (apply_fresh_subst sbs) dec.param_kinds
  ; type_args = List.map (apply_fresh_subst sbs) dec.type_args
  ; xtors = List.map (fun x -> 
      { x with 
        argument_types = List.map (apply_subst_chiral sbs) x.argument_types
      ; main = apply_fresh_subst sbs x.main
      }) dec.xtors
  }

(* ========================================================================= *)
(* Call Site Transformation                                                  *)
(* ========================================================================= *)

(** Traverse a list of results, collecting all successes or returning first error *)
let traverse_result (results: ('a, 'e) result list): ('a list, 'e) result =
  List.fold_right (fun r acc ->
    match r, acc with
      Ok a, Ok rest -> Ok (a :: rest)
    | Error e, _ -> Error e
    | _, Error e -> Error e
  ) results (Ok [])

(** Convert a Core type to a ground argument for instantiation matching.
    This should never fail on well-typed terms - errors indicate earlier bugs. *)
let rec typ_to_ground_arg (t: typ): Specialization.ground_arg =
  match t with
    Ext Int -> Specialization.GroundExt Int
  | Sgn (name, args) -> Specialization.GroundSgn (name, List.map typ_to_ground_arg args)
  | TVar v -> failwith ("unexpected type variable in instantiation: " ^ Ident.name v)
  | TMeta v -> failwith ("unexpected meta variable in instantiation: " ^ Ident.name v)
  | Base _ -> failwith "unexpected base kind in instantiation"
  | Arrow _ -> failwith "unexpected arrow kind in instantiation"
  | Forall _ -> failwith "unexpected forall in instantiation"
  | PromotedCtor _ -> failwith "unexpected promoted ctor in instantiation"

(** Context for transformation *)
type transform_ctx =
  { mono_infos: mono_info Path.tbl
  }

(** Transform a term, handling call sites to monomorphized definitions *)
let rec transform_term (ctx: transform_ctx) (tm: T.term): T.term mono_check =
  match tm with
    T.Var _ | T.Lit _ -> Ok tm
  | T.Ctor (dec, xtor, args) ->
      let* args' = traverse_result (List.map (transform_term ctx) args) in
      Ok (T.Ctor (dec, xtor, args'))
  | T.Dtor (dec, xtor, args) ->
      let* args' = traverse_result (List.map (transform_term ctx) args) in
      Ok (T.Dtor (dec, xtor, args'))
  | T.Match (dec, branches) ->
      let* branches' = traverse_result (List.map (transform_branch ctx) branches) in
      Ok (T.Match (dec, branches'))
  | T.Comatch (dec, branches) ->
      let* branches' = traverse_result (List.map (transform_branch ctx) branches) in
      Ok (T.Comatch (dec, branches'))
  | T.MuPrd (typ, var, cmd) ->
      let* cmd' = transform_command ctx cmd in
      Ok (T.MuPrd (typ, var, cmd'))
  | T.MuCns (typ, var, cmd) ->
      let* cmd' = transform_command ctx cmd in
      Ok (T.MuCns (typ, var, cmd'))
  | T.NewForall (tvar, kind, body_typ, cmd) ->
      let* cmd' = transform_command ctx cmd in
      Ok (T.NewForall (tvar, kind, body_typ, cmd'))
  | T.InstantiateDtor typ ->
      Ok (T.InstantiateDtor typ)

and transform_branch
    (ctx: transform_ctx) ((xtor, tvars, tmvars, cmd): T.branch): T.branch mono_check =
  let* cmd' = transform_command ctx cmd in
  Ok (xtor, tvars, tmvars, cmd')

(** Transform a command, replacing calls to polymorphic definitions *)
and transform_command (ctx: transform_ctx) (cmd: T.command): T.command mono_check =
  match cmd with
    T.Cut (typ, producer, consumer) ->
      let* producer' = transform_term ctx producer in
      let* consumer' = transform_term ctx consumer in
      Ok (T.Cut (typ, producer', consumer'))
  
  | T.Call (def_path, type_args, term_args) ->
      (* Check if the called definition was monomorphized *)
      (match Path.find_opt def_path ctx.mono_infos with
        None ->
          (* Not monomorphized, keep as-is but transform args *)
          let* term_args' = traverse_result (List.map (transform_term ctx) term_args) in
          Ok (T.Call (def_path, type_args, term_args'))
      
      | Some info ->
          (* The definition was monomorphized!
            Transform: Call(foo, [T], args) 
            becomes:   Call(foo.mono, [], [Dtor(For, inst_i, args)]) *)
          let* transformed_args = traverse_result (List.map (transform_term ctx) term_args) in
          
          (* Build the current instantiation from type_args *)
          let current_inst = List.map typ_to_ground_arg type_args in
          
          (* Find the matching instantiation index *)
          (match List.find_index (fun i -> i = current_inst) info.instantiations with
            None -> 
              Error (NoMatchingInstantiation { def_path; instantiation = current_inst })
          | Some idx ->
              let dtor_path = dtor_name_for_inst info.generated_codata.name idx in
              (* Build: Call(foo.mono, [], [Dtor(For, inst_i, args)]) *)
              let dtor = T.Dtor (info.generated_codata, dtor_path, transformed_args) in
              Ok (T.Call (info.mono_path, [], [dtor]))))
  
  | T.Add (t1, t2, t3) ->
      let* t1' = transform_term ctx t1 in
      let* t2' = transform_term ctx t2 in
      let* t3' = transform_term ctx t3 in
      Ok (T.Add (t1', t2', t3'))
  
  | T.Sub (t1, t2, t3) ->
      let* t1' = transform_term ctx t1 in
      let* t2' = transform_term ctx t2 in
      let* t3' = transform_term ctx t3 in
      Ok (T.Sub (t1', t2', t3'))
  
  | T.Ifz (cond, then_cmd, else_cmd) ->
      let* cond' = transform_term ctx cond in
      let* then_cmd' = transform_command ctx then_cmd in
      let* else_cmd' = transform_command ctx else_cmd in
      Ok (T.Ifz (cond', then_cmd', else_cmd'))
  
  | T.Ret (typ, tm) ->
      let* tm' = transform_term ctx tm in
      Ok (T.Ret (typ, tm'))
  
  | T.End -> Ok T.End

(* ========================================================================= *)
(* Definition Transformation                                                 *)
(* ========================================================================= *)

(** Transform a polymorphic definition into a monomorphic one.
    
    Original:
      def foo{a}(x: T[a], k: R[a]) = body
    
    Becomes:
      def foo.mono(u: cns foo.For) =
        ⟨Comatch(foo.For, [
            inst_0(x, k) => body[t0/a]
            inst_1(x, k) => body[t1/a]
            ...
          ]) | u⟩
*)
let transform_definition 
    (ctx: transform_ctx)
    (def: T.definition)
    (info: mono_info)
    : T.definition mono_check =
  
  let codata = info.generated_codata in
  let codata_typ = Sgn (codata.name, []) in
  
  (* Fresh variable for the consumer parameter *)
  let u = Ident.mk "u" in
  
  (* Generate one branch per instantiation *)
  let* branches = traverse_result (List.mapi (fun idx inst ->
    (* Create substitution: type_param_i -> inst_arg_i *)
    let subst = List.fold_left2 (fun acc (tvar, _kind) arg ->
      Ident.add tvar (ground_arg_to_typ arg) acc
    ) Ident.emptytbl def.type_params inst in
    
    (* The branch binds the original term parameter names *)
    let param_vars = List.map fst def.term_params in
    
    (* Specialize the body by applying the type substitution *)
    let specialized_body = subst_command subst def.body in
    
    (* Also transform any nested calls in the specialized body *)
    let* transformed_body = transform_command ctx specialized_body in
    
    (* Branch: (dtor_name, [], param_vars, transformed_body) *)
    let dtor_path = dtor_name_for_inst codata.name idx in
    Ok (dtor_path, [], param_vars, transformed_body)
  ) info.instantiations) in
  
  (* Body: ⟨Comatch(For, branches) | u⟩ *)
  let comatch = T.Comatch (codata, branches) in
  let body = T.Cut (codata_typ, comatch, T.Var u) in
  
  Ok { T.path = info.mono_path
     ; type_params = []                          (* Monomorphic! *)
     ; term_params = [(u, Cns codata_typ)]       (* Single consumer param *)
     ; body = body
     }

(* ========================================================================= *)
(* Main Entry Point                                                          *)
(* ========================================================================= *)

(** Monomorphize an execution context *)
let monomorphize (exe: Specialization.exe_ctx): mono_result mono_check =
  (* First, run the flow analysis *)
  match Specialization.analyze exe with
    Specialization.HasGrowingCycle cycle ->
      Error (GrowingCycle cycle)
  
  | Specialization.Solvable flows ->
      (* Group flows by destination definition *)
      let flows_by_def = 
        List.fold_left (fun acc (flow: Specialization.ground_flow) ->
          let existing = 
            match Path.find_opt flow.dst acc with
              Some lst -> lst | None -> []
          in
          Path.add flow.dst (flow.src :: existing) acc
        ) Path.emptytbl flows
      in
      
      (* Generate mono_info for each polymorphic definition *)
      let poly_defs = Path.to_list exe.defs 
        |> List.filter (fun (_path, (def: T.definition)) -> def.type_params <> [])
      in
      let mono_infos = poly_defs
        |> List.map (fun (path, (def: T.definition)) ->
            let instantiations = 
              match Path.find_opt path flows_by_def with
                Some insts -> List.sort_uniq compare insts | None -> []
            in
            let (codata, _codata_path) = 
              generate_codata_for_def def instantiations in
            let info = 
              { original_path = path
              ; type_params = def.type_params
              ; term_params = def.term_params
              ; instantiations
              ; generated_codata = codata
              ; mono_path = Path.access path "mono"
              } in
            (path, info)
          )
        |> Path.of_list
      in
      
      let ctx = { mono_infos } in
      
      (* Transform all definitions *)
      let* transformed_defs = traverse_result (Path.to_list exe.defs |> List.map (fun (path, def) ->
        match Path.find_opt path mono_infos with
        | Some info -> transform_definition ctx def info
        | None -> 
            (* Non-polymorphic definition: just transform calls *)
            let* body' = transform_command ctx def.body in
            Ok { def with body = body' }
      )) in
      
      (* Also transform main (main is typically monomorphic) *)
      let* main_body' = transform_command ctx exe.main.body in
      let transformed_main = { exe.main with body = main_body' } in
      
      (* Collect new declarations *)
      let new_decs = Path.to_list mono_infos 
        |> List.map (fun (_, info) -> info.generated_codata) in
      
      Ok
        { main = transformed_main
        ; definitions = transformed_defs
        ; new_declarations = new_decs
        ; mono_infos
        }
