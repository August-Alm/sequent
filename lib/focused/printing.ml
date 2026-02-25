(**
  Module: Focused.Printing
  Description: Pretty-printing for Focused.Terms commands
*)

open Common.Identifiers
open Types.FocusedBase
open Types.FocusedTypes
open Terms

(* ========================================================================= *)
(* Configuration                                                             *)
(* ========================================================================= *)

type config =
  { indent_size: int
  ; show_types: bool   (* Whether to show type annotations *)
  ; unicode: bool      (* Use unicode symbols *)
  }

let default_config =
  { indent_size = 2
  ; show_types = false
  ; unicode = true
  }

(* ========================================================================= *)
(* Utilities                                                                 *)
(* ========================================================================= *)

let indent n = String.make n ' '

let parens s = "(" ^ s ^ ")"
let brackets s = "[" ^ s ^ "]"

let comma_sep xs = String.concat ", " xs

let pp_var (v: var) : string = Ident.name v

let pp_vars (vs: var list) : string = 
  comma_sep (List.map pp_var vs)

let pp_sym (x: sym) : string = Path.name x

(* ========================================================================= *)
(* Type printing                                                             *)
(* ========================================================================= *)

let rec pp_typ ?(cfg=default_config) ?(nested=false) (t: typ) : string =
  match t with
  | Base _ -> "type"
  | Arrow (k1, k2) ->
      let s1 = match k1 with
        | Arrow _ -> parens (pp_typ ~cfg ~nested:true k1)
        | _ -> pp_typ ~cfg ~nested:true k1
      in
      let arrow = if cfg.unicode then " → " else " -> " in
      s1 ^ arrow ^ pp_typ ~cfg ~nested:false k2
  | Ext Int -> "int"
  | TVar id -> Ident.name id
  | TMeta id -> "?" ^ Ident.name id
  | Sgn (name, []) -> pp_sym name
  | Sgn (name, args) ->
      let args_str = comma_sep (List.map (pp_typ ~cfg ~nested:false) args) in
      pp_sym name ^ brackets args_str
  | PromotedCtor (dec, ctor, []) -> 
      "'" ^ pp_sym dec ^ "." ^ pp_sym ctor
  | PromotedCtor (dec, ctor, args) ->
      let args_str = comma_sep (List.map (pp_typ ~cfg ~nested:false) args) in
      "'" ^ pp_sym dec ^ "." ^ pp_sym ctor ^ brackets args_str
  | Forall (id, k, body) ->
      let binder = 
        if cfg.show_types 
        then "∀(" ^ Ident.name id ^ " : " ^ pp_typ ~cfg ~nested:false k ^ "). "
        else "∀" ^ Ident.name id ^ ". "
      in
      let inner = binder ^ pp_typ ~cfg ~nested:false body in
      if nested then parens inner else inner

let typ_to_string (t: typ) : string = pp_typ ~cfg:default_config ~nested:false t

let pp_typs (ts: typ list) : string =
  if ts = [] then "" else "{" ^ comma_sep (List.map typ_to_string ts) ^ "}"

(* ========================================================================= *)
(* Chiral type printing                                                      *)
(* ========================================================================= *)

let pp_chiral_typ ?(cfg=default_config) (ct: chiral_typ) : string =
  if is_producer ct then
    "+" ^ pp_typ ~cfg ~nested:true (strip_chirality ct)
  else
    "-" ^ pp_typ ~cfg ~nested:true (strip_chirality ct)

(* ========================================================================= *)
(* Branch printing                                                           *)
(* ========================================================================= *)

let rec pp_branch ?(cfg=default_config) (indent_level: int) ((x, ty_params, params, body): branch) : string =
  let ind = indent indent_level in
  let ty_params_str = if ty_params = [] then "" else "[" ^ pp_vars ty_params ^ "]" in
  let params_str = if params = [] then "()" else "(" ^ pp_vars params ^ ")" in
  ind ^ pp_sym x ^ ty_params_str ^ params_str ^ " ⇒\n" ^
  pp_cmd ~cfg (indent_level + cfg.indent_size) body

and pp_branches ?(cfg=default_config) (indent_level: int) (branches: branch list) : string =
  String.concat "\n" (List.map (pp_branch ~cfg indent_level) branches)

(* ========================================================================= *)
(* Command printing                                                          *)
(* ========================================================================= *)

and pp_cmd ?(cfg=default_config) (n: int) (cmd: command) : string =
  let ind = indent n in
  match cmd with
  
  (* let v = m(args); body *)
  | Let (v, dec, x, args, body) ->
      let dec_str = if cfg.show_types then " : " ^ pp_sym dec.name else "" in
      let args_str = if args = [] then "()" else "(" ^ pp_vars args ^ ")" in
      ind ^ "let " ^ pp_var v ^ " = " ^ pp_sym x ^ args_str ^ dec_str ^ ";\n" ^
      pp_cmd ~cfg n body

  (* switch v { branches } *)
  | Switch (v, dec, branches) ->
      let ty_ann = if cfg.show_types then " : " ^ pp_sym dec.name else "" in
      ind ^ "switch " ^ pp_var v ^ ty_ann ^ " {\n" ^
      pp_branches ~cfg (n + cfg.indent_size) branches ^ "\n" ^
      ind ^ "}"

  (* new v = { branches }; body *)
  | New (v, dec, branches, body) ->
      let ty_ann = if cfg.show_types then " : " ^ pp_sym dec.name else "" in
      ind ^ "new " ^ pp_var v ^ ty_ann ^ " = {\n" ^
      pp_branches ~cfg (n + cfg.indent_size) branches ^ "\n" ^
      ind ^ "};\n" ^
      pp_cmd ~cfg n body

  (* invoke v m(args) *)
  | Invoke (v, dec, x, args) ->
      let dec_str = if cfg.show_types then " : " ^ pp_sym dec.name else "" in
      let args_str = if args = [] then "" else "(" ^ pp_vars args ^ ")" in
      ind ^ pp_var v ^ "." ^ pp_sym x ^ args_str ^ dec_str

  (* ⟨v | k⟩ *)
  | Axiom (ty, v, k) ->
      let ty_ann = if cfg.show_types then "[" ^ pp_typ (Ext ty) ^ "]" else "" in
      if cfg.unicode then
        ind ^ "⟨" ^ pp_var v ^ " | " ^ pp_var k ^ "⟩" ^ ty_ann
      else
        ind ^ "axiom" ^ ty_ann ^ "(" ^ pp_var v ^ ", " ^ pp_var k ^ ")"

  (* jump l(args) *)
  | Jump (label, args) ->
      let args_str = if args = [] then "" else "(" ^ pp_vars args ^ ")" in
      ind ^ "jump " ^ pp_sym label ^ args_str

  (* =========== Primitives =========== *)

  (* lit n { v ⇒ body } *)
  | Lit (n_, v, body) ->
      ind ^ "let " ^ pp_var v ^ " = " ^ string_of_int n_ ^ ";\n" ^
      pp_cmd ~cfg n body

  (* add(x, y) { r ⇒ body } *)
  | Add (x, y, r, body) ->
      ind ^ "let " ^ pp_var r ^ " = " ^ pp_var x ^ " + " ^ pp_var y ^ ";\n" ^
      pp_cmd ~cfg n body
  (* sub(x, y) { r ⇒ body } *)
  | Sub (x, y, r, body) ->
      ind ^ "let " ^ pp_var r ^ " = " ^ pp_var x ^ " - " ^ pp_var y ^ ";\\n" ^
      pp_cmd ~cfg n body
  (* new k = { v ⇒ branch }; cont *)
  | NewInt (k, v, branch, cont) ->
      let ind2 = String.make (n + cfg.indent_size) ' ' in
      ind ^ "new " ^ pp_var k ^ " = {\n" ^
      ind2 ^ pp_var v ^ " ⇒\n" ^
      pp_cmd ~cfg (n + 2 * cfg.indent_size) branch ^ "\n" ^
      ind ^ "};\n" ^
      pp_cmd ~cfg n cont

  (* ifz v { then } { else } *)
  | Ifz (v, then_cmd, else_cmd) ->
      ind ^ "ifz " ^ pp_var v ^ " {\n" ^
      pp_cmd ~cfg (n + cfg.indent_size) then_cmd ^ "\n" ^
      ind ^ "} else {\n" ^
      pp_cmd ~cfg (n + cfg.indent_size) else_cmd ^ "\n" ^
      ind ^ "}"

  (* =========== Terminals =========== *)

  (* ret{ty} v *)
  | Ret (ty, v) ->
      let ty_ann = if cfg.show_types then "{" ^ pp_typ ty ^ "}" else "" in
      ind ^ "ret" ^ ty_ann ^ " " ^ pp_var v

  (* end *)
  | End -> 
      ind ^ "end"

(* ========================================================================= *)
(* Public API                                                                *)
(* ========================================================================= *)

let pp_command ?(cfg=default_config) (cmd: command) : string =
  pp_cmd ~cfg 0 cmd

let command_to_string (cmd: command) : string =
  pp_command ~cfg:default_config cmd

(* ========================================================================= *)
(* Error Printing                                                            *)
(* ========================================================================= *)

let pp_check_error ?(cfg=default_config) (err: check_error) : string =
  match err with
  | UnboundVariable v ->
      "unbound variable: " ^ pp_var v
  | UnboundDeclaration p ->
      "unbound declaration: " ^ pp_sym p
  | UnboundDefinition p ->
      "unbound definition: " ^ pp_sym p
  | UnboundXtor (dec, xtor) ->
      "unbound constructor " ^ pp_sym xtor ^ " in " ^ pp_sym dec
  | UnificationFailed (t1, t2) ->
      "unification failed: " ^ pp_typ ~cfg t1 ^ " ≠ " ^ pp_typ ~cfg t2
  | ChiralityMismatch { expected_chirality; actual } ->
      let exp = match expected_chirality with `Prd -> "producer" | `Cns -> "consumer" in
      let act = match actual with Prd _ -> "producer" | Cns _ -> "consumer" in
      "chirality mismatch: expected " ^ exp ^ ", got " ^ act
  | XtorArityMismatch { xtor; expected; got } ->
      "constructor " ^ pp_sym xtor ^
      " expects " ^ string_of_int expected ^ " arguments, got " ^ string_of_int got
  | TypeVarArityMismatch { xtor; expected; got } ->
      "constructor " ^ pp_sym xtor ^
      " expects " ^ string_of_int expected ^ " type arguments, got " ^ string_of_int got
  | NonExhaustiveMatch { dec_name; missing } ->
      "non-exhaustive pattern match on " ^ pp_sym dec_name ^
      ": missing " ^ String.concat ", " (List.map pp_sym missing)
  | ArityMismatch { expected; got } ->
      "arity mismatch: expected " ^ string_of_int expected ^
      " arguments, got " ^ string_of_int got
  | ExpectedSignature t ->
      "expected signature type, got " ^ pp_typ ~cfg t

let check_error_to_string = pp_check_error ~cfg:default_config

let command_to_string_typed (cmd: command) : string =
  pp_command ~cfg:{default_config with show_types = true} cmd
