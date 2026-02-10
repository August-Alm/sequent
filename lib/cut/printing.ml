(**
  Module: Cut.Printing
  Description: Pretty-printing for Cut types and terms.
  
  Uses syntax like:
    jump l[τ, ...]
    forward x to k
    substitute [v → v', ...]; s
    extern m(v, ...){(Γ) ⇒ s, ...}
    let v = m[τ, ...](Γ); s
    new v : T[τ, ...] = (Γ)b; s
    switch v b
    invoke v m[τ, ...](v, ...)
*)

open Common.Identifiers
open Types
open Terms

(* ========================================================================= *)
(* Configuration                                                             *)
(* ========================================================================= *)

type config =
  { indent_size: int
  ; show_types: bool  (* Whether to show type annotations in detail *)
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
let brackets s = "[" ^ s ^ "]"

let comma_sep xs = String.concat ", " xs
let newline_sep xs = String.concat "\n" xs

(* ========================================================================= *)
(* Kind printing                                                             *)
(* ========================================================================= *)

let rec kind_to_string (k: kind) : string =
  match k with
  | KStar -> "type"
  | KArrow (k1, k2) ->
    let s1 = match k1 with KArrow _ -> parens (kind_to_string k1) | _ -> kind_to_string k1 in
    s1 ^ " → " ^ kind_to_string k2

(* ========================================================================= *)
(* Type printing                                                             *)
(* ========================================================================= *)

let var_to_string (v: Ident.t) : string = Ident.name v

let sym_to_string (s: Path.t) : string = Path.name s

let label_to_string (MkLabel l) : string = Path.name l

let rec typ_to_string ?(nested=false) (t: typ) : string =
  match t with
  | TyVar x -> var_to_string x
  | TySym s -> sym_to_string s
  | TyPrim (s, _k) -> sym_to_string s
  | TyApp (t1, t2) ->
    let inner = typ_to_string ~nested:true t1 ^ parens (typ_to_string t2) in
    if nested then parens inner else inner
  | TyDef sgn -> sym_to_string sgn.symbol

let chirality_to_string (ct: chirality_type) : string =
  match ct with
  | Prd t -> "prd " ^ typ_to_string ~nested:true t
  | Cns t -> "cns " ^ typ_to_string ~nested:true t
  | Ext t -> "ext " ^ typ_to_string ~nested:true t

(* ========================================================================= *)
(* Environment printing                                                      *)
(* ========================================================================= *)

let typed_param_to_string ((v, ct): Ident.t * chirality_type) : string =
  var_to_string v ^ " : " ^ chirality_to_string ct

let typ_env_to_string (env: typ_env) : string =
  comma_sep (List.map typed_param_to_string env)

let typ_list_to_string (tys: typ list) : string =
  if tys = [] then ""
  else brackets (comma_sep (List.map typ_to_string tys))

let var_list_to_string (vars: variable list) : string =
  parens (comma_sep (List.map var_to_string vars))

(* ========================================================================= *)
(* Method signature printing                                                 *)
(* ========================================================================= *)

let quantified_to_string (qs: (Ident.t * kind) list) : string =
  if qs = [] then ""
  else
    let bindings = List.map (fun (v, k) ->
      var_to_string v ^ " : " ^ kind_to_string k
    ) qs in
    "∀" ^ comma_sep bindings ^ ". "

let constraints_to_string (cs: (Ident.t * typ) list option) : string =
  match cs with
  | None -> ""
  | Some constraints ->
    let cs_strs = List.map (fun (v, t) ->
      var_to_string v ^ " = " ^ typ_to_string t
    ) constraints in
    " where " ^ brackets (comma_sep cs_strs)

let method_sig_to_string (m: method_sig) : string =
  let quant = quantified_to_string m.quantified in
  let name = sym_to_string m.symbol in
  let env = parens (typ_env_to_string m.environment) in
  let result = chirality_to_string m.result_type in
  let constrs = constraints_to_string m.constraints in
  quant ^ name ^ " : " ^ env ^ " ⊢ " ^ result ^ constrs

(* ========================================================================= *)
(* Signature printing                                                        *)
(* ========================================================================= *)

let signature_to_string ?(indent_level=0) (sgn: signature) : string =
  let ind = indent indent_level in
  let ind2 = indent (indent_level + 2) in
  let name = sym_to_string sgn.symbol in
  let params_str =
    if sgn.parameters = [] then ""
    else
      let args = List.map (fun (t_opt, k) ->
        (match t_opt with None -> "_" | Some t -> typ_to_string t) ^
        " : " ^ kind_to_string k
      ) sgn.parameters in
      parens (comma_sep args)
  in
  let methods_str =
    if sgn.methods = [] then ""
    else
      let method_strs = List.map (fun m -> ind2 ^ method_sig_to_string m) sgn.methods in
      " {\n" ^ newline_sep method_strs ^ "\n" ^ ind ^ "}"
  in
  ind ^ "signature " ^ name ^ params_str ^ methods_str

(* ========================================================================= *)
(* Substitution printing                                                     *)
(* ========================================================================= *)

let substitution_to_string ((v1, v2): variable * variable) : string =
  var_to_string v1 ^ " → " ^ var_to_string v2

let substitutions_to_string (subst: substitutions) : string =
  brackets (comma_sep (List.map substitution_to_string subst))

(* ========================================================================= *)
(* Statement printing                                                        *)
(* ========================================================================= *)

let rec statement_to_string ?(cfg=default_config) ?(indent_level=0) (s: statement) : string =
  let ind = indent indent_level in
  let next_level = indent_level + cfg.indent_size in
  match s with
  (* jump l[τ, ...] *)
  | Jump (l, tys) ->
    ind ^ "jump " ^ label_to_string l ^ typ_list_to_string tys
  
  (* forward x to k *)
  | Forward (x, k) ->
    ind ^ "forward " ^ var_to_string x ^ " to " ^ var_to_string k
  
  (* substitute [v → v', ...]; s *)
  | Substitute (subst, s') ->
    ind ^ "substitute " ^ substitutions_to_string subst ^ ";\n" ^
    statement_to_string ~cfg ~indent_level s'
  
  (* extern m(v, ...){(Γ) ⇒ s, ...} *)
  | Extern (sym, vars, branches) ->
    let vars_str = var_list_to_string vars in
    let branches_str = extern_branches_to_string ~cfg ~indent_level:next_level branches in
    ind ^ "extern " ^ sym_to_string sym ^ vars_str ^ " {\n" ^
    branches_str ^ "\n" ^ ind ^ "}"
  
  (* let v = m[τ, ...](Γ); s *)
  | Let (v, m, tys, gamma, s') ->
    let gamma_str = 
      if gamma = [] then "()"
      else parens (typ_env_to_string gamma)
    in
    ind ^ "let " ^ var_to_string v ^ " = " ^ 
    sym_to_string m ^ typ_list_to_string tys ^ gamma_str ^ ";\n" ^
    statement_to_string ~cfg ~indent_level s'
  
  (* new v : T = (Γ)b; s *)
  | New (v, ty, gamma, branches, s') ->
    let gamma_str = parens (typ_env_to_string gamma) in
    let branches_str = branches_to_string ~cfg ~indent_level:next_level branches in
    ind ^ "new " ^ var_to_string v ^ " : " ^ typ_to_string ty ^
    " = " ^ gamma_str ^ " {\n" ^
    branches_str ^ "\n" ^ ind ^ "};\n" ^
    statement_to_string ~cfg ~indent_level s'
  
  (* switch v b *)
  | Switch (v, branches) ->
    let branches_str = branches_to_string ~cfg ~indent_level:next_level branches in
    ind ^ "switch " ^ var_to_string v ^ " {\n" ^
    branches_str ^ "\n" ^ ind ^ "}"
  
  (* invoke v m[τ, ...](v, ...) *)
  | Invoke (v, m, tys, args) ->
    let args_str = 
      if args = [] then ""
      else var_list_to_string args
    in
    ind ^ "invoke " ^ var_to_string v ^ " " ^ 
    sym_to_string m ^ typ_list_to_string tys ^ args_str

(* branches b ::= {m[τ, ...](Γ) ⇒ s, ...} *)
and branches_to_string ?(cfg=default_config) ?(indent_level=0) 
    (branches: (symbol * typ list * typ_env * statement) list) : string =
  let ind = indent indent_level in
  let branch_strs = List.map (fun (m, tys, gamma, s) ->
    let gamma_str = parens (typ_env_to_string gamma) in
    let body = statement_to_string ~cfg ~indent_level:(indent_level + cfg.indent_size) s in
    ind ^ sym_to_string m ^ typ_list_to_string tys ^ gamma_str ^ " ⇒\n" ^ body
  ) branches in
  newline_sep branch_strs

(* extern branches {(Γ) ⇒ s, ...} *)
and extern_branches_to_string ?(cfg=default_config) ?(indent_level=0)
    (branches: extern_branches) : string =
  let ind = indent indent_level in
  let branch_strs = List.map (fun (gamma, s) ->
    let gamma_str = parens (typ_env_to_string gamma) in
    let body = statement_to_string ~cfg ~indent_level:(indent_level + cfg.indent_size) s in
    ind ^ gamma_str ^ " ⇒\n" ^ body
  ) branches in
  newline_sep branch_strs

(* ========================================================================= *)
(* Program and definition printing                                           *)
(* ========================================================================= *)

let definition_to_string ?(cfg=default_config) ((l, gamma, s): label * typ_env * statement) : string =
  let gamma_str = parens (typ_env_to_string gamma) in
  let body = statement_to_string ~cfg ~indent_level:cfg.indent_size s in
  "define " ^ label_to_string l ^ gamma_str ^ " =\n" ^ body

let program_to_string ?(cfg=default_config) (prog: program) : string =
  let defs = List.map (definition_to_string ~cfg) prog in
  String.concat "\n\n" defs

let definitions_to_string ?(cfg=default_config) (defs: definitions) : string =
  let sigs = List.map (fun (_, (sgn, _k)) -> signature_to_string sgn) defs.signatures in
  let prog = program_to_string ~cfg defs.program in
  if sigs = [] then prog
  else String.concat "\n\n" sigs ^ "\n\n" ^ prog

(* ========================================================================= *)
(* Convenience functions                                                     *)
(* ========================================================================= *)

(** Print a type *)
let pp_type = typ_to_string

(** Print a kind *)
let pp_kind = kind_to_string

(** Print a chirality type *)
let pp_chirality = chirality_to_string

(** Print a statement *)
let pp_statement ?(show_types=false) s =
  statement_to_string ~cfg:{default_config with show_types} s

(** Print a signature *)
let pp_signature sgn =
  signature_to_string sgn

(** Print a method signature *)
let pp_method_sig = method_sig_to_string

(** Print a definition *)
let pp_definition ?(show_types=false) def =
  definition_to_string ~cfg:{default_config with show_types} def

(** Print a program *)
let pp_program ?(show_types=false) prog =
  program_to_string ~cfg:{default_config with show_types} prog

(** Print a label *)
let pp_label = label_to_string

(** Print a type environment *)
let pp_typ_env = typ_env_to_string

(* ========================================================================= *)
(* Type error pretty-printing                                                *)
(* ========================================================================= *)

(** Pretty-print a type-checking exception *)
let pp_type_check_exn (e: exn) : string =
  match e with
  (* Variable/environment errors *)
  | Terms.VariableNotInEnv (v, gamma) ->
    Printf.sprintf "Variable %s not found in environment %s"
      (var_to_string v) (parens (typ_env_to_string gamma))
  
  | Terms.LabelNotInEnv l ->
    Printf.sprintf "Label %s not found in label environment"
      (label_to_string l)
  
  | Terms.SignatureNotFound sym ->
    Printf.sprintf "Signature not found for type symbol %s"
      (sym_to_string sym)
  
  | Terms.MethodNotFound (m, sgn) ->
    Printf.sprintf "Method %s not found in signature %s"
      (sym_to_string m) (sym_to_string sgn.Types.symbol)
  
  | Terms.ExternNotFound sym ->
    Printf.sprintf "Extern symbol %s not found"
      (sym_to_string sym)
  
  | Terms.EnvTooShort (n, gamma) ->
    Printf.sprintf "Environment too short: expected at least %d elements, got %s"
      n (parens (typ_env_to_string gamma))
  
  | Terms.EnvSplitMismatch (expected, actual) ->
    Printf.sprintf "Environment split mismatch:\n  expected: %s\n  actual:   %s"
      (parens (typ_env_to_string expected))
      (parens (typ_env_to_string actual))
  
  | Terms.VariableNotAtFront (v, gamma) ->
    Printf.sprintf "Variable %s not at front of environment %s"
      (var_to_string v) (parens (typ_env_to_string gamma))
  
  (* Forward errors *)
  | Terms.ForwardTypeMismatch (x, x_ty, k, k_ty) ->
    Printf.sprintf "Forward type mismatch: %s : %s cannot forward to %s : %s"
      (var_to_string x) (chirality_to_string x_ty)
      (var_to_string k) (chirality_to_string k_ty)
  
  | Terms.ForwardNotProducer (v, ty) ->
    Printf.sprintf "Forward: expected producer, but %s has type %s"
      (var_to_string v) (chirality_to_string ty)
  
  | Terms.ForwardNotConsumer (v, ty) ->
    Printf.sprintf "Forward: expected consumer, but %s has type %s"
      (var_to_string v) (chirality_to_string ty)
  
  (* Jump errors *)
  | Terms.JumpEnvMismatch (l, expected, actual) ->
    Printf.sprintf "Jump environment mismatch for label %s:\n  expected: %s\n  actual:   %s"
      (label_to_string l)
      (parens (typ_env_to_string expected))
      (parens (typ_env_to_string actual))
  
  (* Extern errors *)
  | Terms.ExternArgCountMismatch (m, expected, actual) ->
    Printf.sprintf "Extern %s: expected %d arguments, got %d"
      (sym_to_string m) expected actual
  
  | Terms.ExternArgTypeMismatch (v, actual, expected) ->
    Printf.sprintf "Extern argument %s type mismatch:\n  expected: %s\n  actual:   %s"
      (var_to_string v)
      (chirality_to_string expected)
      (chirality_to_string actual)
  
  | Terms.ExternBranchCountMismatch (m, expected, actual) ->
    Printf.sprintf "Extern %s: expected %d branches, got %d"
      (sym_to_string m) expected actual
  
  | Terms.ExternBranchEnvMismatch (actual, expected) ->
    Printf.sprintf "Extern branch environment mismatch:\n  expected: %s\n  actual:   %s"
      (parens (typ_env_to_string expected))
      (parens (typ_env_to_string actual))
  
  (* Let errors *)
  | Terms.LetTypeArgCountMismatch (m, expected, actual) ->
    Printf.sprintf "Let %s: expected %d type arguments, got %d"
      (sym_to_string m) expected actual
  
  | Terms.LetArgCountMismatch (m, expected, actual) ->
    Printf.sprintf "Let %s: expected %d arguments, got %d"
      (sym_to_string m) expected actual
  
  | Terms.LetArgTypeMismatch (m, actual, expected) ->
    Printf.sprintf "Let %s: argument type mismatch:\n  expected: %s\n  actual:   %s"
      (sym_to_string m)
      (chirality_to_string expected)
      (chirality_to_string actual)
  
  (* New errors *)
  | Terms.NewBranchCountMismatch (sym, expected, actual) ->
    Printf.sprintf "New %s: expected %d branches, got %d"
      (sym_to_string sym) expected actual
  
  | Terms.NewBranchMethodMismatch (actual, expected) ->
    Printf.sprintf "New: branch method mismatch, expected %s, got %s"
      (sym_to_string expected) (sym_to_string actual)
  
  | Terms.NewBranchArgCountMismatch (m, expected, actual) ->
    Printf.sprintf "New branch %s: expected %d arguments, got %d"
      (sym_to_string m) expected actual
  
  | Terms.NewBranchArgTypeMismatch (m, actual, expected) ->
    Printf.sprintf "New branch %s: argument type mismatch:\n  expected: %s\n  actual:   %s"
      (sym_to_string m)
      (chirality_to_string expected)
      (chirality_to_string actual)
  
  | Terms.NewExpectedSignatureType ty ->
    Printf.sprintf "New: expected signature type, got %s"
      (typ_to_string ty)
  
  (* Switch errors *)
  | Terms.SwitchNotProducer (v, ty) ->
    Printf.sprintf "Switch: expected producer, but %s has type %s"
      (var_to_string v) (chirality_to_string ty)
  
  | Terms.SwitchVariableNotAtFront (v, gamma) ->
    Printf.sprintf "Switch: variable %s not at front of environment %s"
      (var_to_string v) (parens (typ_env_to_string gamma))
  
  | Terms.SwitchBranchCountMismatch (sym, expected, actual) ->
    Printf.sprintf "Switch %s: expected %d branches, got %d"
      (sym_to_string sym) expected actual
  
  | Terms.SwitchBranchMethodMismatch (actual, expected) ->
    Printf.sprintf "Switch: branch method mismatch, expected %s, got %s"
      (sym_to_string expected) (sym_to_string actual)
  
  | Terms.SwitchBranchArgCountMismatch (m, expected, actual) ->
    Printf.sprintf "Switch branch %s: expected %d arguments, got %d"
      (sym_to_string m) expected actual
  
  | Terms.SwitchBranchArgTypeMismatch (m, actual, expected) ->
    Printf.sprintf "Switch branch %s: argument type mismatch:\n  expected: %s\n  actual:   %s"
      (sym_to_string m)
      (chirality_to_string expected)
      (chirality_to_string actual)
  
  | Terms.SwitchExpectedSignatureType ty ->
    Printf.sprintf "Switch: expected signature type, got %s"
      (typ_to_string ty)
  
  (* Invoke errors *)
  | Terms.InvokeNotConsumer (v, ty) ->
    Printf.sprintf "Invoke: expected consumer, but %s has type %s"
      (var_to_string v) (chirality_to_string ty)
  
  | Terms.InvokeVariableNotAtFront (v, gamma) ->
    Printf.sprintf "Invoke: variable %s not at front of environment %s"
      (var_to_string v) (parens (typ_env_to_string gamma))
  
  | Terms.InvokeArgCountMismatch (m, expected, actual) ->
    Printf.sprintf "Invoke %s: expected %d arguments, got %d"
      (sym_to_string m) expected actual
  
  | Terms.InvokeArgTypeMismatch (m, actual, expected) ->
    Printf.sprintf "Invoke %s: argument type mismatch:\n  expected: %s\n  actual:   %s"
      (sym_to_string m)
      (chirality_to_string expected)
      (chirality_to_string actual)
  
  | Terms.InvokeArgNotInEnv v ->
    Printf.sprintf "Invoke: argument %s not found in environment"
      (var_to_string v)
  
  | Terms.InvokeExpectedSignatureType ty ->
    Printf.sprintf "Invoke: expected signature type, got %s"
      (typ_to_string ty)
  
  (* Fallback for unknown exceptions *)
  | e -> Printexc.to_string e
