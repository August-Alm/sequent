(**
  module: Core.Printing
  description: Pretty-printing for Core types and terms.
*)

open Common.Identifiers
open Types.CoreBase
open Types.CoreTypes
open Terms

(* ========================================================================= *)
(* Configuration                                                             *)
(* ========================================================================= *)

type config =
  { indent_size: int
  ; show_types: bool   (* whether to show type annotations *)
  }

let default_config =
  { indent_size = 2
  ; show_types = true
  }

(* ========================================================================= *)
(* Utilities                                                                 *)
(* ========================================================================= *)

let indent n = String.make n ' '

let parens s = "(" ^ s ^ ")"
let brackets s = "[" ^ s ^ "]"
let braces s = "{" ^ s ^ "}"
let angles s = "⟨" ^ s ^ "⟩"

let comma_sep xs = String.concat ", " xs
let space_sep xs = String.concat " " xs

let pp_var (v: var) : string = Ident.name v

let pp_sym (x: sym) : string = Path.name x

(* ========================================================================= *)
(* Polarity and Kind Printing                                                *)
(* ========================================================================= *)

let pp_polarity (p: polarity) : string =
  match p with Pos -> "+" | Neg -> "-"

let rec pp_kind ?(nested=false) (k: typ) : string =
  match k with
  | Base p -> pp_polarity p
  | Arrow (k1, k2) ->
      let inner = pp_kind ~nested:true k1 ^ " → " ^ pp_kind ~nested:false k2 in
      if nested then parens inner else inner
  | _ -> pp_typ ~nested k

(* ========================================================================= *)
(* Type Printing                                                             *)
(* ========================================================================= *)

and pp_typ ?(nested=false) (t: typ) : string =
  match t with
  | Base p -> pp_polarity p
  | Arrow (t1, t2) ->
      let inner = pp_typ ~nested:true t1 ^ " → " ^ pp_typ ~nested:false t2 in
      if nested then parens inner else inner
  | Ext Int -> "int"
  | TVar v -> pp_var v
  | TMeta v -> "?" ^ pp_var v
  | Sgn (name, []) -> pp_sym name
  | Sgn (name, args) ->
      let args_str = comma_sep (List.map (pp_typ ~nested:false) args) in
      pp_sym name ^ parens args_str
  | PromotedCtor (dec, ctor, []) ->
      "'" ^ pp_sym dec ^ "." ^ pp_sym ctor
  | PromotedCtor (dec, ctor, args) ->
      let args_str = comma_sep (List.map (pp_typ ~nested:false) args) in
      "'" ^ pp_sym dec ^ "." ^ pp_sym ctor ^ parens args_str
  | Forall (v, k, body) ->
      let inner = "∀" ^ pp_var v ^ ":" ^ pp_kind k ^ "." ^ pp_typ ~nested:false body in
      if nested then parens inner else inner

let typ_to_string (t: typ) : string = pp_typ ~nested:false t

(* ========================================================================= *)
(* Chiral Type Printing                                                      *)
(* ========================================================================= *)

let pp_chiral_typ (ct: chiral_typ) : string =
  match ct with
  | Prd t -> "prd(" ^ pp_typ t ^ ")"
  | Cns t -> "cns(" ^ pp_typ t ^ ")"

(* ========================================================================= *)
(* Term Printing                                                             *)
(* ========================================================================= *)

let rec pp_term ?(cfg=default_config) (tm: term) : string =
  match tm with
  | Var v -> pp_var v
  | Lit n -> string_of_int n
  
  | Ctor (dec, xtor, []) ->
      let ty_args = pp_type_args dec.type_args in
      pp_sym xtor ^ ty_args
  | Ctor (dec, xtor, args) ->
      let ty_args = pp_type_args dec.type_args in
      let args_str = comma_sep (List.map (pp_term ~cfg) args) in
      pp_sym xtor ^ ty_args ^ parens args_str
  
  | Dtor (dec, xtor, exist_tys, []) ->
      let ty_args = pp_type_args dec.type_args in
      let exist_args = if exist_tys = [] then "" else "[" ^ comma_sep (List.map pp_typ exist_tys) ^ "]" in
      pp_sym xtor ^ ty_args ^ exist_args
  | Dtor (dec, xtor, exist_tys, args) ->
      let ty_args = pp_type_args dec.type_args in
      let exist_args = if exist_tys = [] then "" else "[" ^ comma_sep (List.map pp_typ exist_tys) ^ "]" in
      let args_str = comma_sep (List.map (pp_term ~cfg) args) in
      pp_sym xtor ^ ty_args ^ exist_args ^ parens args_str
  
  | Match (dec, branches) ->
      let ty_args = pp_type_args dec.type_args in
      "match " ^ pp_sym dec.name ^ ty_args ^ " " ^ braces (pp_branches ~cfg 0 branches)
  
  | Comatch (dec, branches) ->
      let ty_args = pp_type_args dec.type_args in
      "comatch " ^ pp_sym dec.name ^ ty_args ^ " " ^ braces (pp_branches ~cfg 0 branches)
  
  | MuPrd (t, v, cmd) ->
      let ty_ann = if cfg.show_types then ":" ^ pp_typ t else "" in
      "μ+" ^ pp_var v ^ ty_ann ^ "." ^ pp_command ~cfg ~n:0 cmd
  
  | MuCns (t, v, cmd) ->
      let ty_ann = if cfg.show_types then ":" ^ pp_typ t else "" in
      "μ-" ^ pp_var v ^ ty_ann ^ "." ^ pp_command ~cfg ~n:0 cmd
  
  | NewForall (v, k, t, _cont, cmd) ->
      let forall_typ = "∀(" ^ pp_var v ^ ": " ^ pp_kind k ^ ")." ^ pp_typ t in
      "comatch " ^ forall_typ ^ " { instantiate{" ^ pp_var v ^ "} ⇒ " ^ pp_command ~cfg ~n:0 cmd ^ " }"
  
  | InstantiateDtor t ->
      "instantiate{" ^ pp_typ t ^ "}"

and pp_type_args (args: typ list) : string =
  match args with
  | [] -> ""
  | _ -> braces (comma_sep (List.map pp_typ args))

and pp_branch ?(cfg=default_config) (n: int) ((xtor, ty_vars, tm_vars, cmd): branch) : string =
  let ty_vars_str = 
    match ty_vars with
    | [] -> ""
    | _ -> brackets (comma_sep (List.map pp_var ty_vars))
  in
  let tm_vars_str =
    match tm_vars with
    | [] -> ""
    | _ -> parens (comma_sep (List.map pp_var tm_vars))
  in
  let ind = indent n in
  ind ^ pp_sym xtor ^ ty_vars_str ^ tm_vars_str ^ " ⇒ " ^ pp_command ~cfg ~n cmd

and pp_branches ?(cfg=default_config) (n: int) (branches: branch list) : string =
  " " ^ String.concat "; " (List.map (pp_branch ~cfg n) branches) ^ " "

(* ========================================================================= *)
(* Command Printing                                                          *)
(* ========================================================================= *)

and pp_command ?(cfg=default_config) ~(n: int) (cmd: command) : string =
  match cmd with
  | Cut (t, producer, consumer) ->
      let ty_ann = if cfg.show_types then brackets (pp_typ t) else "" in
      angles (pp_term ~cfg producer ^ " | " ^ pp_term ~cfg consumer) ^ ty_ann
  
  | Call (path, type_args, term_args) ->
      let ty_args = pp_type_args type_args in
      let tm_args =
        match term_args with
        | [] -> ""
        | _ -> parens (comma_sep (List.map (pp_term ~cfg) term_args))
      in
      "call " ^ pp_sym path ^ ty_args ^ tm_args
  
  | Add (t1, t2, t3) ->
      "add(" ^ pp_term ~cfg t1 ^ ", " ^ pp_term ~cfg t2 ^ ", " ^ pp_term ~cfg t3 ^ ")"
  
  | Sub (t1, t2, t3) ->
      "sub(" ^ pp_term ~cfg t1 ^ ", " ^ pp_term ~cfg t2 ^ ", " ^ pp_term ~cfg t3 ^ ")"
  
  | Ifz (cond, then_cmd, else_cmd) ->
      let ind = indent (n + cfg.indent_size) in
      "ifz " ^ pp_term ~cfg cond ^ " then\n" ^
      ind ^ pp_command ~cfg ~n:(n + cfg.indent_size) then_cmd ^ "\n" ^
      indent n ^ "else\n" ^
      ind ^ pp_command ~cfg ~n:(n + cfg.indent_size) else_cmd
  
  | Ret (t, tm) ->
      let ty_ann = if cfg.show_types then brackets (pp_typ t) else "" in
      "ret" ^ ty_ann ^ " " ^ pp_term ~cfg tm
  
  | End -> "end"

(* ========================================================================= *)
(* Definition Printing                                                       *)
(* ========================================================================= *)

let pp_definition ?(cfg=default_config) (def: definition) : string =
  let ty_params_str =
    match def.type_params with
    | [] -> ""
    | ps ->
        let params = List.map (fun (v, k) -> pp_var v ^ ": " ^ pp_kind k) ps in
        braces (comma_sep params)
  in
  let tm_params_str =
    match def.term_params with
    | [] -> ""
    | ps ->
        let params = List.map (fun (v, ct) -> pp_var v ^ ": " ^ pp_chiral_typ ct) ps in
        parens (comma_sep params)
  in
  "def " ^ pp_sym def.path ^ ty_params_str ^ tm_params_str ^ " =\n" ^
  "    " ^ pp_command ~cfg ~n:4 def.body

(* ========================================================================= *)
(* Declaration Printing                                                      *)
(* ========================================================================= *)

let pp_data_sort (ds: Common.Types.data_sort) : string =
  match ds with Data -> "data" | Codata -> "code"

let pp_xtor ?(cfg=default_config) (n: int) (x: xtor) : string =
  ignore cfg;
  let ind = indent n in
  let quantified_str =
    match x.quantified with
    | [] -> ""
    | qs ->
        let qs_str = List.map (fun (v, k) -> pp_var v ^ ": " ^ pp_kind k) qs in
        braces (comma_sep qs_str) ^ " "
  in
  let existentials_str =
    match x.existentials with
    | [] -> ""
    | es ->
        let es_str = List.map (fun (v, k) -> pp_var v ^ ": " ^ pp_kind k) es in
        "∃" ^ braces (comma_sep es_str) ^ " "
  in
  let args_str =
    match x.argument_types with
    | [] -> ""
    | args -> " → " ^ String.concat " → " (List.map pp_chiral_typ (List.rev args))
  in
  ind ^ pp_sym x.name ^ ": " ^ quantified_str ^ existentials_str ^ pp_typ x.main ^ args_str

let pp_dec ?(cfg=default_config) (dec: dec) : string =
  let result_kind = match dec.data_sort with Data -> "+" | Codata -> "-" in
  let kind_str =
    match dec.param_kinds with
    | [] -> ""
    | ks -> ": " ^ String.concat " → " (List.map pp_kind ks) ^ " → " ^ result_kind
  in
  let ty_args_str = pp_type_args dec.type_args in
  let header = pp_data_sort dec.data_sort ^ " " ^ pp_sym dec.name ^ ty_args_str ^ kind_str ^ " where" in
  let xtors_str =
    match dec.xtors with
    | [] -> ""
    | xs -> "\n" ^ String.concat "\n" (List.map (pp_xtor ~cfg 2) xs)
  in
  header ^ xtors_str

(* ========================================================================= *)
(* Error Printing                                                            *)
(* ========================================================================= *)

let pp_check_error (err: Terms.check_error) : string =
  match err with
  | Terms.UnboundVariable v ->
      "unbound variable: " ^ pp_var v
  | Terms.UnboundDefinition p ->
      "unbound definition: " ^ Path.name p
  | Terms.UnboundDeclaration p ->
      "unbound declaration: " ^ Path.name p
  | Terms.UnboundXtor (dec, xtor) ->
      "unbound xtor " ^ Path.name xtor ^ " in declaration " ^ Path.name dec
  | Terms.UnificationFailed (t1, t2) ->
      "unification failed: " ^ pp_typ t1 ^ " vs " ^ pp_typ t2
  | Terms.ChiralityMismatch { expected_chirality; actual } ->
      let expected_str = match expected_chirality with `Prd -> "producer" | `Cns -> "consumer" in
      "chirality mismatch: expected " ^ expected_str ^ ", got " ^ pp_chiral_typ actual
  | Terms.XtorArityMismatch { xtor; expected; got } ->
      "xtor arity mismatch for " ^ Path.name xtor ^ 
      ": expected " ^ string_of_int expected ^ " args, got " ^ string_of_int got
  | Terms.XtorArgTypeMismatch { xtor; index; expected; got } ->
      "xtor arg type mismatch for " ^ Path.name xtor ^ 
      " at index " ^ string_of_int index ^ 
      ": expected " ^ pp_chiral_typ expected ^ ", got " ^ pp_chiral_typ got
  | Terms.TypeVarArityMismatch { xtor; expected; got } ->
      "type var arity mismatch for " ^ Path.name xtor ^ 
      ": expected " ^ string_of_int expected ^ " type args, got " ^ string_of_int got
  | Terms.NonExhaustiveMatch { dec_name; missing } ->
      "non-exhaustive match on " ^ Path.name dec_name ^ 
      ": missing " ^ String.concat ", " (List.map Path.name missing)
  | Terms.CallTypeArityMismatch { defn; expected; got } ->
      "call type arity mismatch for " ^ Path.name defn ^ 
      ": expected " ^ string_of_int expected ^ " type args, got " ^ string_of_int got
  | Terms.CallTermArityMismatch { defn; expected; got } ->
      "call term arity mismatch for " ^ Path.name defn ^ 
      ": expected " ^ string_of_int expected ^ " term args, got " ^ string_of_int got
  | Terms.CallArgTypeMismatch { defn; index; expected; got } ->
      "call arg type mismatch for " ^ Path.name defn ^ 
      " at index " ^ string_of_int index ^ 
      ": expected " ^ pp_chiral_typ expected ^ ", got " ^ pp_chiral_typ got
  | Terms.AddTypeMismatch { arg1; arg2; result } ->
      "add type mismatch: " ^ pp_chiral_typ arg1 ^ " + " ^ pp_chiral_typ arg2 ^ 
      " → " ^ pp_chiral_typ result
  | Terms.IfzConditionNotInt ct ->
      "ifz condition not int: " ^ pp_chiral_typ ct

let check_error_to_string (err: Terms.check_error) : string =
  pp_check_error err

(* ========================================================================= *)
(* AST Printing                                                              *)
(* ========================================================================= *)

let command_to_string (cmd: command) : string =
  pp_command ~cfg:default_config ~n:0 cmd

let command_to_string_untyped (cmd: command) : string =
  pp_command ~cfg:{default_config with show_types = false} ~n:0 cmd

let term_to_string (tm: term) : string =
  pp_term ~cfg:default_config tm

let definition_to_string (def: definition) : string =
  pp_definition ~cfg:default_config def

let dec_to_string (dec: dec) : string =
  pp_dec ~cfg:default_config dec

(* ========================================================================= *)
(* Specialization Printing                                                   *)
(* ========================================================================= *)

(** Pretty-print a ground argument *)
let rec pp_ground_arg (arg: Specialization.ground_arg) : string =
  match arg with
  | Specialization.GroundExt Int -> "int"
  | Specialization.GroundSgn (name, []) -> Path.name name
  | Specialization.GroundSgn (name, args) ->
      Path.name name ^ parens (comma_sep (List.map pp_ground_arg args))

let ground_arg_to_string (arg: Specialization.ground_arg) : string =
  pp_ground_arg arg

(** Pretty-print a ground flow *)
let pp_ground_flow (flow: Specialization.ground_flow) : string =
  let args_str = match flow.src with
    | [] -> "()"
    | args -> parens (comma_sep (List.map pp_ground_arg args))
  in
  Path.name flow.dst ^ args_str

let ground_flow_to_string (flow: Specialization.ground_flow) : string =
  pp_ground_flow flow

(** Pretty-print analysis result *)
let pp_analysis_result (result: Specialization.analysis_result) : string =
  match result with
  | Specialization.HasGrowingCycle cycle ->
      "growing cycle detected: " ^ 
      String.concat " → " (List.map (fun (p, i) -> 
        Path.name p ^ "[" ^ string_of_int i ^ "]"
      ) cycle)
  | Specialization.Solvable flows ->
      "solvable with instantiations:\n" ^
      String.concat "\n" (List.map (fun f -> "  " ^ pp_ground_flow f) flows)

let analysis_result_to_string (result: Specialization.analysis_result) : string =
  pp_analysis_result result

(* ========================================================================= *)
(* Monomorphization Error Printing                                           *)
(* ========================================================================= *)

(** Pretty-print a monomorphization error *)
let pp_mono_error (err: Monomorphize.mono_error) : string =
  match err with
  | Monomorphize.GrowingCycle cycle ->
      "growing cycle detected: " ^
      String.concat " → " (List.map (fun (p, i) ->
        Path.name p ^ "[" ^ string_of_int i ^ "]"
      ) cycle)
  | Monomorphize.NoMatchingInstantiation { def_path; instantiation } ->
      "no matching instantiation for " ^ Path.name def_path ^ " with args " ^
      parens (comma_sep (List.map pp_ground_arg instantiation))

let mono_error_to_string (err: Monomorphize.mono_error) : string =
  pp_mono_error err
