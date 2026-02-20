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
  | Base _ -> "Type"
  | Arrow (k1, k2) ->
      let s1 = match k1 with
        | Arrow _ -> parens (pp_typ ~cfg ~nested:true k1)
        | _ -> pp_typ ~cfg ~nested:true k1
      in
      let arrow = if cfg.unicode then " → " else " -> " in
      s1 ^ arrow ^ pp_typ ~cfg ~nested:false k2
  | Ext Int -> "Int"
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
  | Fun (t1, t2) ->
      let s1 = match t1 with
        | Fun _ | Forall _ -> parens (pp_typ ~cfg ~nested:true t1)
        | _ -> pp_typ ~cfg ~nested:true t1
      in
      let arrow = if cfg.unicode then " → " else " -> " in
      let inner = s1 ^ arrow ^ pp_typ ~cfg ~nested:false t2 in
      if nested then parens inner else inner
  | Forall (id, k, body) ->
      let binder = 
        if cfg.show_types 
        then "∀(" ^ Ident.name id ^ " : " ^ pp_typ ~cfg ~nested:false k ^ "). "
        else "∀" ^ Ident.name id ^ ". "
      in
      let inner = binder ^ pp_typ ~cfg ~nested:false body in
      if nested then parens inner else inner
  | Raise t -> 
      "↑" ^ pp_typ ~cfg ~nested:true t
  | Lower t -> 
      "↓" ^ pp_typ ~cfg ~nested:true t

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
  (* =========== Let forms =========== *)
  
  (* let v = m{tys}(args); body *)
  | Let (v, _, x, tys, args, body) ->
      let tys_str = pp_typs tys in
      let args_str = if args = [] then "()" else "(" ^ pp_vars args ^ ")" in
      ind ^ "let " ^ pp_var v ^ " = " ^ pp_sym x ^ tys_str ^ args_str ^ ";\n" ^
      pp_cmd ~cfg n body

  (* let v = apply{t1, t2}(x, y); body *)
  | LetApply (v, t1, t2, x, y, body) ->
      let tys_str = if cfg.show_types then "{" ^ pp_typ t1 ^ ", " ^ pp_typ t2 ^ "}" else "" in
      ind ^ "let " ^ pp_var v ^ " = apply" ^ tys_str ^ "(" ^ pp_var x ^ ", " ^ pp_var y ^ ");\n" ^
      pp_cmd ~cfg n body

  (* let v = instantiate[a]{k, t}; body *)
  | LetInstantiate (v, a, k, t, body) ->
      let tys_str = if cfg.show_types then "{" ^ pp_typ k ^ ", " ^ pp_typ t ^ "}" else "" in
      ind ^ "let " ^ pp_var v ^ " = instantiate[" ^ pp_var a ^ "]" ^ tys_str ^ ";\n" ^
      pp_cmd ~cfg n body

  (* let v = thunk{t}(x); body *)
  | LetThunk (v, t, x, body) ->
      let ty_str = if cfg.show_types then "{" ^ pp_typ t ^ "}" else "" in
      ind ^ "let " ^ pp_var v ^ " = thunk" ^ ty_str ^ "(" ^ pp_var x ^ ");\n" ^
      pp_cmd ~cfg n body

  (* let v = return{t}(x); body *)
  | LetReturn (v, t, x, body) ->
      let ty_str = if cfg.show_types then "{" ^ pp_typ t ^ "}" else "" in
      ind ^ "let " ^ pp_var v ^ " = return" ^ ty_str ^ "(" ^ pp_var x ^ ");\n" ^
      pp_cmd ~cfg n body

  (* =========== Switch forms =========== *)

  (* switch v { branches } *)
  | Switch (sg, v, branches) ->
      let ty_ann = if cfg.show_types then " : " ^ pp_sym sg else "" in
      ind ^ "switch " ^ pp_var v ^ ty_ann ^ " {\n" ^
      pp_branches ~cfg (n + cfg.indent_size) branches ^ "\n" ^
      ind ^ "}"

  (* switch v { apply{t1, t2}(x, y) ⇒ s } *)
  | SwitchFun (v, t1, t2, x, y, s) ->
      let tys_str = if cfg.show_types then "{" ^ pp_typ t1 ^ ", " ^ pp_typ t2 ^ "}" else "" in
      ind ^ "switch " ^ pp_var v ^ " {\n" ^
      ind ^ "  apply" ^ tys_str ^ "(" ^ pp_var x ^ ", " ^ pp_var y ^ ") ⇒\n" ^
      pp_cmd ~cfg (n + cfg.indent_size * 2) s ^ "\n" ^
      ind ^ "}"

  (* switch v { instantiate[a]{k} ⇒ s } *)
  | SwitchForall (v, a, k, s) ->
      let ty_str = if cfg.show_types then "{" ^ pp_typ k ^ "}" else "" in
      ind ^ "switch " ^ pp_var v ^ " {\n" ^
      ind ^ "  instantiate[" ^ pp_var a ^ "]" ^ ty_str ^ " ⇒\n" ^
      pp_cmd ~cfg (n + cfg.indent_size * 2) s ^ "\n" ^
      ind ^ "}"

  (* switch v { thunk{t}(x) ⇒ s } *)
  | SwitchRaise (v, t, x, s) ->
      let ty_str = if cfg.show_types then "{" ^ pp_typ t ^ "}" else "" in
      ind ^ "switch " ^ pp_var v ^ " {\n" ^
      ind ^ "  thunk" ^ ty_str ^ "(" ^ pp_var x ^ ") ⇒\n" ^
      pp_cmd ~cfg (n + cfg.indent_size * 2) s ^ "\n" ^
      ind ^ "}"

  (* switch v { return{t}(x) ⇒ s } *)
  | SwitchLower (v, t, x, s) ->
      let ty_str = if cfg.show_types then "{" ^ pp_typ t ^ "}" else "" in
      ind ^ "switch " ^ pp_var v ^ " {\n" ^
      ind ^ "  return" ^ ty_str ^ "(" ^ pp_var x ^ ") ⇒\n" ^
      pp_cmd ~cfg (n + cfg.indent_size * 2) s ^ "\n" ^
      ind ^ "}"

  (* =========== New forms =========== *)

  (* new v = { branches }; body *)
  | New (sg, v, branches, body) ->
      let ty_ann = if cfg.show_types then " : " ^ pp_sym sg else "" in
      ind ^ "new " ^ pp_var v ^ ty_ann ^ " = {\n" ^
      pp_branches ~cfg (n + cfg.indent_size) branches ^ "\n" ^
      ind ^ "};\n" ^
      pp_cmd ~cfg n body

  (* new v = { apply{t1, t2}(x, y) ⇒ s1 }; s2 *)
  | NewFun (v, t1, t2, x, y, s1, s2) ->
      let tys_str = if cfg.show_types then "{" ^ pp_typ t1 ^ ", " ^ pp_typ t2 ^ "}" else "" in
      ind ^ "new " ^ pp_var v ^ " = {\n" ^
      ind ^ "  apply" ^ tys_str ^ "(" ^ pp_var x ^ ", " ^ pp_var y ^ ") ⇒\n" ^
      pp_cmd ~cfg (n + cfg.indent_size * 2) s1 ^ "\n" ^
      ind ^ "};\n" ^
      pp_cmd ~cfg n s2

  (* new v = { instantiate[a]{k} ⇒ s1 }; s2 *)
  | NewForall (v, a, k, s1, s2) ->
      let ty_str = if cfg.show_types then "{" ^ pp_typ k ^ "}" else "" in
      ind ^ "new " ^ pp_var v ^ " = {\n" ^
      ind ^ "  instantiate[" ^ pp_var a ^ "]" ^ ty_str ^ " ⇒\n" ^
      pp_cmd ~cfg (n + cfg.indent_size * 2) s1 ^ "\n" ^
      ind ^ "};\n" ^
      pp_cmd ~cfg n s2

  (* new v = { thunk{t}(x) ⇒ s1 }; s2 *)
  | NewRaise (v, t, x, s1, s2) ->
      let ty_str = if cfg.show_types then "{" ^ pp_typ t ^ "}" else "" in
      ind ^ "new " ^ pp_var v ^ " = {\n" ^
      ind ^ "  thunk" ^ ty_str ^ "(" ^ pp_var x ^ ") ⇒\n" ^
      pp_cmd ~cfg (n + cfg.indent_size * 2) s1 ^ "\n" ^
      ind ^ "};\n" ^
      pp_cmd ~cfg n s2

  (* new v = { return{t}(x) ⇒ s1 }; s2 *)
  | NewLower (v, t, x, s1, s2) ->
      let ty_str = if cfg.show_types then "{" ^ pp_typ t ^ "}" else "" in
      ind ^ "new " ^ pp_var v ^ " = {\n" ^
      ind ^ "  return" ^ ty_str ^ "(" ^ pp_var x ^ ") ⇒\n" ^
      pp_cmd ~cfg (n + cfg.indent_size * 2) s1 ^ "\n" ^
      ind ^ "};\n" ^
      pp_cmd ~cfg n s2

  (* =========== Invoke forms =========== *)

  (* invoke v m{tys}(args) *)
  | Invoke (v, _, x, tys, args) ->
      let tys_str = pp_typs tys in
      let args_str = if args = [] then "" else "(" ^ pp_vars args ^ ")" in
      ind ^ pp_var v ^ "." ^ pp_sym x ^ tys_str ^ args_str

  (* invoke v apply{t1, t2}(x, y) *)
  | InvokeApply (v, t1, t2, x, y) ->
      let tys_str = if cfg.show_types then "{" ^ pp_typ t1 ^ ", " ^ pp_typ t2 ^ "}" else "" in
      ind ^ pp_var v ^ ".apply" ^ tys_str ^ "(" ^ pp_var x ^ ", " ^ pp_var y ^ ")"

  (* invoke v instantiate{ty, k} *)
  | InvokeInstantiate (v, ty, k) ->
      let tys_str = if cfg.show_types then "{" ^ pp_typ ty ^ ", " ^ pp_typ k ^ "}" else "" in
      ind ^ pp_var v ^ ".instantiate" ^ tys_str

  (* invoke v thunk{t}(x) *)
  | InvokeThunk (v, t, x) ->
      let ty_str = if cfg.show_types then "{" ^ pp_typ t ^ "}" else "" in
      ind ^ pp_var v ^ ".thunk" ^ ty_str ^ "(" ^ pp_var x ^ ")"

  (* invoke v return{t}(x) *)
  | InvokeReturn (v, t, x) ->
      let ty_str = if cfg.show_types then "{" ^ pp_typ t ^ "}" else "" in
      ind ^ pp_var v ^ ".return" ^ ty_str ^ "(" ^ pp_var x ^ ")"

  (* =========== Axiom =========== *)

  (* ⟨v | k⟩ *)
  | Axiom (ty, v, k) ->
      let ty_ann = if cfg.show_types then "[" ^ pp_typ ty ^ "]" else "" in
      if cfg.unicode then
        ind ^ "⟨" ^ pp_var v ^ " | " ^ pp_var k ^ "⟩" ^ ty_ann
      else
        ind ^ "axiom" ^ ty_ann ^ "(" ^ pp_var v ^ ", " ^ pp_var k ^ ")"

  (* =========== Primitives =========== *)

  (* lit n { v ⇒ body } *)
  | Lit (n_, v, body) ->
      ind ^ "let " ^ pp_var v ^ " = " ^ string_of_int n_ ^ ";\n" ^
      pp_cmd ~cfg n body

  (* add(x, y) { r ⇒ body } *)
  | Add (x, y, r, body) ->
      ind ^ "let " ^ pp_var r ^ " = " ^ pp_var x ^ " + " ^ pp_var y ^ ";\n" ^
      pp_cmd ~cfg n body

  (* ifz v { then } { else } *)
  | Ifz (v, then_cmd, else_cmd) ->
      ind ^ "ifz " ^ pp_var v ^ " {\n" ^
      pp_cmd ~cfg (n + cfg.indent_size) then_cmd ^ "\n" ^
      ind ^ "} else {\n" ^
      pp_cmd ~cfg (n + cfg.indent_size) else_cmd ^ "\n" ^
      ind ^ "}"

  (* =========== Terminals =========== *)

  (* ret[ty] v *)
  | Ret (ty, v) ->
      let ty_ann = if cfg.show_types then "[" ^ pp_typ ty ^ "]" else "" in
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

let command_to_string_typed (cmd: command) : string =
  pp_command ~cfg:{default_config with show_types = true} cmd
