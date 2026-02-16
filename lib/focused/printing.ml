(**
  Module: Focused.Printing
  Description: Pretty-printing for Focused.Terms commands
*)

open Common.Identifiers
open Common.Types
open Common.Printing
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

let pp_var (v: var) : string = Ident.name v

let pp_vars (vs: var list) : string = 
  String.concat ", " (List.map pp_var vs)

let pp_xtor_name (x: xtor) : string = Path.name x.name

(* ========================================================================= *)
(* Branch printing                                                           *)
(* ========================================================================= *)

let rec pp_branch ?(cfg=default_config) (indent_level: int) ((x, params, body): branch) : string =
  let ind = indent indent_level in
  let params_str = if params = [] then "()" else "(" ^ pp_vars params ^ ")" in
  ind ^ pp_xtor_name x ^ params_str ^ " ⇒\n" ^
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
    Let (v, x, args, body) ->
      let args_str = if args = [] then "()" else "(" ^ pp_vars args ^ ")" in
      ind ^ "let " ^ pp_var v ^ " = " ^ pp_xtor_name x ^ args_str ^ ";\n" ^
      pp_cmd ~cfg n body

  (* switch v { branches } *)
  | Switch (sg, v, branches) ->
      let ty_ann = if cfg.show_types then " : " ^ pp_sgn_typ sg else "" in
      ind ^ "switch " ^ pp_var v ^ ty_ann ^ " {\n" ^
      pp_branches ~cfg (n + cfg.indent_size) branches ^ "\n" ^
      ind ^ "}"

  (* new v = { branches }; body *)
  | New (sg, v, branches, body) ->
      let ty_ann = if cfg.show_types then " : " ^ pp_sgn_typ sg else "" in
      ind ^ "new " ^ pp_var v ^ ty_ann ^ " = {\n" ^
      pp_branches ~cfg (n + cfg.indent_size) branches ^ "\n" ^
      ind ^ "};\n" ^
      pp_cmd ~cfg n body

  (* invoke v m(args) *)
  | Invoke (v, x, args) ->
      let args_str = if args = [] then "" else "(" ^ pp_vars args ^ ")" in
      ind ^ pp_var v ^ "." ^ pp_xtor_name x ^ args_str

  (* ⟨v | k⟩ *)
  | Axiom (ty, v, k) ->
      let ty_ann = if cfg.show_types then "[" ^ typ_to_string ty ^ "]" else "" in
      if cfg.unicode then
        ind ^ "⟨" ^ pp_var v ^ " | " ^ pp_var k ^ "⟩" ^ ty_ann
      else
        ind ^ "axiom" ^ ty_ann ^ "(" ^ pp_var v ^ ", " ^ pp_var k ^ ")"

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

  (* ret[ty] v *)
  | Ret (ty, v) ->
      let ty_ann = if cfg.show_types then "[" ^ typ_to_string ty ^ "]" else "" in
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
