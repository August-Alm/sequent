(**
  Module: Kore.Printing
  Description: Pretty-printing for Kore types and terms.
  
  Uses syntax like:
    ⟨µα.s | D(Γ)⟩
    ⟨x | case {C(Γ) ⇒ s, ... }⟩
    
    data tuple: + → + → + where {
       mk_tuple: {a: +, b: +} (a, b) ⊢ tuple(a, b) | ()
    }
*)

open Common.Identifiers
open Types
open Terms

(* ========================================================================= *)
(* Configuration                                                             *)
(* ========================================================================= *)

type config =
  { indent_size: int
  ; show_types: bool  (* Whether to show type annotations *)
  }

let default_config =
  { indent_size = 2
  ; show_types = false
  }

(* ========================================================================= *)
(* Utilities                                                                 *)
(* ========================================================================= *)

let indent n = String.make n ' '

let parens s = "(" ^ s ^ ")"
let braces s = "{" ^ s ^ "}"
let angles s = "⟨" ^ s ^ "⟩"
let brackets s = "[" ^ s ^ "]"

let comma_sep xs = String.concat ", " xs
let semi_sep xs = String.concat "; " xs
let newline_sep xs = String.concat "\n" xs

(* ========================================================================= *)
(* Kind printing                                                             *)
(* ========================================================================= *)

let rec kind_to_string (k: kind) : string =
  match k with
  | Pos -> "+"
  | Neg -> "-"
  | Ext -> "ext"
  | Arrow (k1, k2) ->
    let s1 = match k1 with Arrow _ -> parens (kind_to_string k1) | _ -> kind_to_string k1 in
    s1 ^ " → " ^ kind_to_string k2

(* ========================================================================= *)
(* Type printing                                                             *)
(* ========================================================================= *)

let var_to_string (v: variable) : string = Ident.name v

let sym_to_string (s: symbol) : string = Path.name s

let rec tpe_to_string (t: tpe) : string =
  match t with
  | TyVar x -> var_to_string x
  | TySym s -> sym_to_string s
  | TyExt s -> "ext " ^ sym_to_string s
  | TyApp (t1, t2) ->
    tpe_to_string t1 ^ parens (tpe_to_string t2)
  | TyPos sgn -> "data " ^ signature_header_to_string sgn
  | TyNeg sgn -> "code " ^ signature_header_to_string sgn

and signature_header_to_string (sgn: signature) : string =
  let name = sym_to_string sgn.name in
  if sgn.arguments = [] then name
  else
    let args = List.map (fun (t_opt, k) ->
      match t_opt with
      | None -> kind_to_string k
      | Some t -> tpe_to_string t
    ) sgn.arguments in
    name ^ parens (comma_sep args)

let chiral_to_string (ct: chiral_tpe) : string =
  match ct with
  | Lhs t -> "prd " ^ tpe_to_string t
  | Rhs t -> "cns " ^ tpe_to_string t

(* ========================================================================= *)
(* Xtor (constructor/destructor) printing                                    *)
(* ========================================================================= *)

let quantified_to_string (qs: (variable * kind) list) : string =
  if qs = [] then ""
  else
    let bindings = List.map (fun (v, k) ->
      var_to_string v ^ ": " ^ kind_to_string k
    ) qs in
    braces (comma_sep bindings) ^ " "

let params_to_string (params: chiral_tpe list) : string =
  let strs = List.map (fun ct ->
    match ct with
    | Lhs t -> tpe_to_string t
    | Rhs t -> tpe_to_string t
  ) params in
  parens (comma_sep strs)

let params_with_chirality_to_string (params: chiral_tpe list) : string =
  let lhs = List.filter_map (function Lhs t -> Some t | Rhs _ -> None) params in
  let rhs = List.filter_map (function Rhs t -> Some t | Lhs _ -> None) params in
  let lhs_str = if lhs = [] then "()" else parens (comma_sep (List.map tpe_to_string lhs)) in
  let rhs_str = if rhs = [] then "()" else parens (comma_sep (List.map tpe_to_string rhs)) in
  lhs_str ^ " | " ^ rhs_str

let xtor_to_string (x: xtor) : string =
  let name = sym_to_string x.name in
  let quant = quantified_to_string x.quantified in
  let params = params_with_chirality_to_string x.parameters in
  let parent_args = 
    if x.parent_arguments = [] then sym_to_string x.parent
    else sym_to_string x.parent ^ parens (comma_sep (List.map tpe_to_string x.parent_arguments))
  in
  let constraints_str = match x.constraints with
    | None -> ""
    | Some cs ->
      let cs_strs = List.map (fun (v, t) ->
        var_to_string v ^ " = " ^ tpe_to_string t
      ) cs in
      " where " ^ brackets (comma_sep cs_strs)
  in
  name ^ ": " ^ quant ^ params ^ " ⊢ " ^ parent_args ^ constraints_str

(* ========================================================================= *)
(* Signature printing                                                        *)
(* ========================================================================= *)

let polarity_keyword (pol: polarity) : string =
  match pol with
  | Positive -> "data"
  | Negative -> "code"

let signature_to_string ?(indent_level=0) (pol: polarity) (sgn: signature) : string =
  let ind = indent indent_level in
  let ind2 = indent (indent_level + 2) in
  let header = polarity_keyword pol ^ " " ^ sym_to_string sgn.name in
  let kind_sig = 
    if sgn.arguments = [] then ""
    else
      let args = List.map (fun (_, k) -> kind_to_string k) sgn.arguments in
      ": " ^ String.concat " → " args ^ " → " ^ (match pol with Positive -> "+" | Negative -> "-")
  in
  let xtors_str =
    if sgn.xtors = [] then ""
    else
      let xtor_strs = List.map (fun x -> ind2 ^ xtor_to_string x) sgn.xtors in
      " where {\n" ^ newline_sep xtor_strs ^ "\n" ^ ind ^ "}"
  in
  ind ^ header ^ kind_sig ^ xtors_str

(* ========================================================================= *)
(* Term printing                                                             *)
(* ========================================================================= *)

let rec term_to_string ?(cfg=default_config) ?(indent_level=0) (t: term) : string =
  match t with
  | Variable x -> var_to_string x
  
  | Constructor (xtor, ty_args, args) ->
    let name = sym_to_string xtor.name in
    let ty_args_str = 
      if ty_args = [] then ""
      else brackets (comma_sep (List.map tpe_to_string ty_args))
    in
    let args_str =
      if args = [] then ""
      else parens (comma_sep (List.map (term_to_string ~cfg ~indent_level) args))
    in
    name ^ ty_args_str ^ args_str
  
  | Destructor (xtor, ty_args, args) ->
    let name = sym_to_string xtor.name in
    let ty_args_str = 
      if ty_args = [] then ""
      else brackets (comma_sep (List.map tpe_to_string ty_args))
    in
    let args_str =
      if args = [] then ""
      else parens (comma_sep (List.map (term_to_string ~cfg ~indent_level) args))
    in
    name ^ ty_args_str ^ args_str
  
  | Match (_sgn, branches) ->
    let branches_str = branches_to_string ~cfg ~indent_level branches in
    "case " ^ braces branches_str
  
  | New (_sgn, branches) ->
    let branches_str = branches_to_string ~cfg ~indent_level branches in
    "cocase " ^ braces branches_str
  
  | MuLhsPos (ty, x, cmd) ->
    let body = command_to_string ~cfg ~indent_level:(indent_level + cfg.indent_size) cmd in
    let ty_ann = if cfg.show_types then " : " ^ tpe_to_string ty else "" in
    "µ" ^ var_to_string x ^ ty_ann ^ "." ^ body
  
  | MuRhsPos (ty, x, cmd) ->
    let body = command_to_string ~cfg ~indent_level:(indent_level + cfg.indent_size) cmd in
    let ty_ann = if cfg.show_types then " : " ^ tpe_to_string ty else "" in
    "µ̃" ^ var_to_string x ^ ty_ann ^ "." ^ body
  
  | MuLhsNeg (ty, x, cmd) ->
    let body = command_to_string ~cfg ~indent_level:(indent_level + cfg.indent_size) cmd in
    let ty_ann = if cfg.show_types then " : " ^ tpe_to_string ty else "" in
    "µ" ^ var_to_string x ^ ty_ann ^ "." ^ body
  
  | MuRhsNeg (ty, x, cmd) ->
    let body = command_to_string ~cfg ~indent_level:(indent_level + cfg.indent_size) cmd in
    let ty_ann = if cfg.show_types then " : " ^ tpe_to_string ty else "" in
    "µ̃" ^ var_to_string x ^ ty_ann ^ "." ^ body

and branches_to_string ?(cfg=default_config) ?(indent_level=0) (branches: branch list) : string =
  if branches = [] then ""
  else if List.length branches = 1 then
    branch_to_string ~cfg ~indent_level (List.hd branches)
  else
    let inner_indent = indent (indent_level + cfg.indent_size) in
    let branch_strs = List.map (fun br ->
      inner_indent ^ branch_to_string ~cfg ~indent_level:(indent_level + cfg.indent_size) br
    ) branches in
    "\n" ^ newline_sep branch_strs ^ "\n" ^ indent indent_level

and branch_to_string ?(cfg=default_config) ?(indent_level=0) (br: branch) : string =
  let name = sym_to_string br.xtor.name in
  let ty_vars_str =
    if br.type_vars = [] then ""
    else braces (comma_sep (List.map (fun (v, k) -> var_to_string v ^ ": " ^ kind_to_string k) br.type_vars))
  in
  let term_vars_str = parens (comma_sep (List.map var_to_string br.term_vars)) in
  let body = command_to_string ~cfg ~indent_level:(indent_level + cfg.indent_size) br.command in
  name ^ ty_vars_str ^ term_vars_str ^ " ⇒ " ^ body

(** Command printing - the core cut forms *)
and command_to_string ?(cfg=default_config) ?(indent_level=0) (cmd: command) : string =
  match cmd with
  | CutPos (ty, lhs, rhs) ->
    let lhs_str = term_to_string ~cfg ~indent_level lhs in
    let rhs_str = term_to_string ~cfg ~indent_level rhs in
    let ty_ann = if cfg.show_types then " : " ^ tpe_to_string ty else "" in
    angles (lhs_str ^ " | " ^ rhs_str) ^ ty_ann
  
  | CutNeg (ty, lhs, rhs) ->
    let lhs_str = term_to_string ~cfg ~indent_level lhs in
    let rhs_str = term_to_string ~cfg ~indent_level rhs in
    let ty_ann = if cfg.show_types then " : " ^ tpe_to_string ty else "" in
    angles (lhs_str ^ " | " ^ rhs_str) ^ ty_ann
  
  | Extern (sym, args, clauses) ->
    let name = sym_to_string sym in
    let args_str = parens (comma_sep (List.map (term_to_string ~cfg ~indent_level) args)) in
    let clauses_str = clauses_to_string ~cfg ~indent_level clauses in
    "extern " ^ name ^ args_str ^ " " ^ braces clauses_str
  
  | Call (sym, ty_args, args) ->
    let name = sym_to_string sym in
    let ty_args_str =
      if ty_args = [] then ""
      else brackets (comma_sep (List.map tpe_to_string ty_args))
    in
    let args_str = parens (comma_sep (List.map (term_to_string ~cfg ~indent_level) args)) in
    "call " ^ name ^ ty_args_str ^ args_str
  
  | End -> "end"

and clauses_to_string ?(cfg=default_config) ?(indent_level=0) (clauses: clause list) : string =
  if clauses = [] then ""
  else if List.length clauses = 1 then
    clause_to_string ~cfg ~indent_level (List.hd clauses)
  else
    let ind = indent (indent_level + cfg.indent_size) in
    let clause_strs = List.map (fun cl ->
      ind ^ clause_to_string ~cfg ~indent_level:(indent_level + cfg.indent_size) cl
    ) clauses in
    "\n" ^ newline_sep clause_strs ^ "\n" ^ indent indent_level

and clause_to_string ?(cfg=default_config) ?(indent_level=0) (cl: clause) : string =
  let params_str = parens (comma_sep (List.map var_to_string cl.parameters)) in
  let body = command_to_string ~cfg ~indent_level:(indent_level + cfg.indent_size) cl.body in
  params_str ^ " ⇒ " ^ body

(* ========================================================================= *)
(* Definition printing                                                       *)
(* ========================================================================= *)

let definition_to_string ?(cfg=default_config) (def: definition) : string =
  let name = sym_to_string def.name in
  let ty_params_str =
    if def.type_params = [] then ""
    else brackets (comma_sep (List.map (fun (v, k) -> var_to_string v ^ ": " ^ kind_to_string k) def.type_params))
  in
  let term_params_str = 
    if def.term_params = [] then "()"
    else
      let strs = List.map (fun (v, ct) ->
        var_to_string v ^ ": " ^ chiral_to_string ct
      ) def.term_params in
      parens (comma_sep strs)
  in
  let body_str = command_to_string ~cfg ~indent_level:2 def.body in
  "def " ^ name ^ ty_params_str ^ term_params_str ^ " =\n  " ^ body_str

(* ========================================================================= *)
(* Convenience functions                                                     *)
(* ========================================================================= *)

(** Print a type *)
let pp_type = tpe_to_string

(** Print a kind *)
let pp_kind = kind_to_string

(** Print a chiral type *)
let pp_chiral = chiral_to_string

(** Print a term *)
let pp_term ?(show_types=false) t =
  term_to_string ~cfg:{default_config with show_types} t

(** Print a command *)
let pp_command ?(show_types=false) cmd =
  command_to_string ~cfg:{default_config with show_types} cmd

(** Print a signature with its xtors *)
let pp_signature pol sgn =
  signature_to_string pol sgn

(** Print a definition *)
let pp_definition ?(show_types=false) def =
  definition_to_string ~cfg:{default_config with show_types} def

(** Print an xtor *)
let pp_xtor = xtor_to_string

(* ========================================================================= *)
(* Type error pretty-printing                                                *)
(* ========================================================================= *)

let polarity_to_string (p: Types.polarity) : string =
  match p with
  | Types.Positive -> "positive"
  | Types.Negative -> "negative"

(** Pretty-print a type-checking exception *)
let pp_type_check_exn (e: exn) : string =
  match e with
  (* Type/chirality mismatch errors *)
  | Terms.TypeMismatchCommand (cmd, expected, actual) ->
    Printf.sprintf "Type mismatch in command:\n  command:  %s\n  expected: %s\n  actual:   %s"
      (command_to_string cmd)
      (tpe_to_string expected)
      (tpe_to_string actual)
  
  | Terms.TypeMismatchTerm (trm, expected, actual) ->
    Printf.sprintf "Type mismatch in term:\n  term:     %s\n  expected: %s\n  actual:   %s"
      (term_to_string trm)
      (tpe_to_string expected)
      (tpe_to_string actual)
  
  | Terms.ChiralityMismatchTerm (trm, expected, actual) ->
    Printf.sprintf "Chirality mismatch in term:\n  term:     %s\n  expected: %s\n  actual:   %s"
      (term_to_string trm)
      (chiral_to_string expected)
      (chiral_to_string actual)
  
  (* Polarity mismatch errors *)
  | Terms.PolarityMismatchCommand (cmd, expected, actual) ->
    Printf.sprintf "Polarity mismatch in command:\n  command:  %s\n  expected: %s\n  actual:   %s"
      (command_to_string cmd)
      (polarity_to_string expected)
      (polarity_to_string actual)
  
  | Terms.PolarityMismatchTerm (trm, expected, actual) ->
    Printf.sprintf "Polarity mismatch in term:\n  term:     %s\n  expected: %s\n  actual:   %s"
      (term_to_string trm)
      (polarity_to_string expected)
      (polarity_to_string actual)
  
  (* Undefined/missing errors *)
  | Terms.UndefinedTerm sym ->
    Printf.sprintf "Undefined term: %s"
      (sym_to_string sym)
  
  | Terms.MissingBranch xtor ->
    Printf.sprintf "Missing branch for constructor/destructor: %s"
      (xtor_to_string xtor)
  
  | Terms.DuplicateBranch xtor ->
    Printf.sprintf "Duplicate branch for constructor/destructor: %s"
      (xtor_to_string xtor)
  
  (* Arity mismatch errors *)
  | Terms.TypeArgumentNumberMismatch ->
    "Type argument count mismatch"
  
  | Terms.TermArgumentNumberMismatch ->
    "Term argument count mismatch"
  
  | Terms.ClauseNumberMismatch ->
    "Clause count mismatch"
  
  | Terms.ClauseParameterNumberMismatch ->
    "Clause parameter count mismatch"
  
  | Terms.BranchNumberMismatch ->
    "Branch count mismatch"
  
  (* Cannot infer errors *)
  | Terms.CannotInferTypeOfCommand cmd ->
    Printf.sprintf "Cannot infer type of command: %s"
      (command_to_string cmd)
  
  | Terms.CannotInferTypeOfTerm trm ->
    Printf.sprintf "Cannot infer type of term: %s"
      (term_to_string trm)
  
  (* Wrong polarity errors *)
  | Terms.NewOfNonCodataType trm ->
    Printf.sprintf "New expression requires codata (negative) type, but got:\n  %s"
      (term_to_string trm)
  
  | Terms.MatchOfNonDataType trm ->
    Printf.sprintf "Match expression requires data (positive) type, but got:\n  %s"
      (term_to_string trm)
  
  | Terms.ConstructorOfNonDataType trm ->
    Printf.sprintf "Constructor requires data (positive) type, but got:\n  %s"
      (term_to_string trm)
  
  | Terms.DestructorOfNonCodataType trm ->
    Printf.sprintf "Destructor requires codata (negative) type, but got:\n  %s"
      (term_to_string trm)
  
  (* Fallback for unknown exceptions *)
  | e -> Printexc.to_string e
