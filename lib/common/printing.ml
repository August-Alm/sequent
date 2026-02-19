(**
  Module: Common.Printing
  Description: Pretty-printing for Common.Types
*)
(*
open Identifiers
open Types

(* ========================================================================= *)
(* Configuration                                                             *)
(* ========================================================================= *)

type config =
  { indent_size: int
  ; show_kinds: bool   (* Whether to show kind annotations on binders *)
  ; unicode: bool      (* Use unicode symbols *)
  }

let default_config =
  { indent_size = 2
  ; show_kinds = false
  ; unicode = true
  }

(* ========================================================================= *)
(* Utilities                                                                 *)
(* ========================================================================= *)

let indent n = String.make n ' '

let parens s = "(" ^ s ^ ")"
let braces s = "{" ^ s ^ "}"
let brackets s = "[" ^ s ^ "]"
let angles s = "⟨" ^ s ^ "⟩"

let comma_sep xs = String.concat ", " xs
let space_sep xs = String.concat " " xs
let newline_sep xs = String.concat "\n" xs
let semi_sep xs = String.concat "; " xs

(* ========================================================================= *)
(* Identifier printing                                                       *)
(* ========================================================================= *)

let pp_ident (id: Ident.t) : string = Ident.name id

let pp_path (p: Path.t) : string = Path.name p

let pp_sym (s: sym) : string = Path.name s

(* ========================================================================= *)
(* Kind printing                                                             *)
(* ========================================================================= *)

let rec pp_kind ?(cfg=default_config) (k: kind) : string =
  match k with
    Star -> if cfg.unicode then "★" else "*"
  | Arrow (k1, k2) ->
      let s1 = match k1 with
          Arrow _ -> parens (pp_kind ~cfg k1)
        | _ -> pp_kind ~cfg k1
      in
      let arrow = if cfg.unicode then " → " else " -> " in
      s1 ^ arrow ^ pp_kind ~cfg k2

(* ========================================================================= *)
(* Type printing                                                             *)
(* ========================================================================= *)

let pp_ext_typ (e: ext_typ) : string =
  match e with
    Int -> "Int"

let rec pp_typ ?(cfg=default_config) ?(nested=false) (t: typ) : string =
  match t with
    Ext e -> pp_ext_typ e
  | Var {contents = Unbound id} -> pp_ident id
  | Var {contents = Link t'} -> pp_typ ~cfg ~nested t'
  | Rigid id -> pp_ident id
  | Sym (s, _) -> pp_sym s
  | App (f, []) -> pp_typ ~cfg ~nested:true f
  | App (f, args) ->
      let f_str = pp_typ ~cfg ~nested:true f in
      let args_str = comma_sep (List.map (pp_typ ~cfg ~nested:false) args) in
      let inner = f_str ^ brackets args_str in
      if nested then parens inner else inner
  | Sgn s -> pp_sgn_typ s

and pp_sgn_typ (s: sgn_typ) : string =
  let name = pp_path s.name in
  if s.parameters = [] then name
  else
    let params = comma_sep (List.map pp_kind s.parameters) in
    name ^ brackets params

(* ========================================================================= *)
(* Chiral type printing                                                      *)
(* ========================================================================= *)

let pp_chiral_typ ?(cfg=default_config) (ct: chiral_typ) : string =
  match ct with
    Lhs t -> "+" ^ pp_typ ~cfg ~nested:true t
  | Rhs t -> "-" ^ pp_typ ~cfg ~nested:true t

(* ========================================================================= *)
(* Xtor printing                                                             *)
(* ========================================================================= *)

let pp_binder ?(cfg=default_config) ((id, k): Ident.t * kind) : string =
  if cfg.show_kinds then
    pp_ident id ^ " : " ^ pp_kind ~cfg k
  else
    pp_ident id

let pp_binders ?(cfg=default_config) (bs: (Ident.t * kind) list) : string =
  if bs = [] then ""
  else brackets (comma_sep (List.map (pp_binder ~cfg) bs))

let pp_xtor_short (x: xtor) : string =
  pp_path x.name

let pp_xtor ?(cfg=default_config) (x: xtor) : string =
  let name = pp_path x.name in
  let params = pp_binders ~cfg x.parameters in
  let exists = 
    if x.existentials = [] then ""
    else "∃" ^ pp_binders ~cfg x.existentials ^ ". "
  in
  let args = 
    if x.arguments = [] then ""
    else parens (comma_sep (List.map (pp_chiral_typ ~cfg) x.arguments))
  in
  let main = pp_typ ~cfg x.main in
  name ^ params ^ exists ^ args ^ " : " ^ main

let pp_xtor_app (x: xtor) (args: Ident.t list) : string =
  let name = pp_path x.name in
  if args = [] then name
  else name ^ parens (comma_sep (List.map pp_ident args))

(* ========================================================================= *)
(* Full signature printing                                                   *)
(* ========================================================================= *)

let pp_sgn_full ?(cfg=default_config) ?(indent_level=0) (s: sgn_typ) : string =
  let ind = indent indent_level in
  let ind2 = indent (indent_level + cfg.indent_size) in
  let name = pp_path s.name in
  let params = 
    if s.parameters = [] then ""
    else brackets (comma_sep (List.map (pp_kind ~cfg) s.parameters))
  in
  let xtors_str =
    if s.xtors = [] then " {}"
    else
      let xtor_strs = List.map (fun x -> ind2 ^ pp_xtor ~cfg x) s.xtors in
      " {\n" ^ newline_sep xtor_strs ^ "\n" ^ ind ^ "}"
  in
  ind ^ name ^ params ^ xtors_str

(* ========================================================================= *)
(* Equation printing                                                         *)
(* ========================================================================= *)

let rec pp_equation ?(cfg=default_config) (eq: equation) : string =
  match eq with
    True -> "⊤"
  | Equal (t1, t2) ->
      pp_typ ~cfg t1 ^ " = " ^ pp_typ ~cfg t2
  | And (e1, e2) ->
      pp_equation ~cfg e1 ^ " ∧ " ^ pp_equation ~cfg e2
  | Exists (Unbound id, e) ->
      "∃" ^ pp_ident id ^ ". " ^ pp_equation ~cfg e
  | Exists (Link t, e) ->
      (* Linked variable - show the concrete type *)
      "[" ^ pp_typ ~cfg t ^ "] " ^ pp_equation ~cfg e
  | Implies (e1, e2) ->
      parens (pp_equation ~cfg e1) ^ " ⊃ " ^ pp_equation ~cfg e2

(* ========================================================================= *)
(* Convenience functions                                                     *)
(* ========================================================================= *)

let typ_to_string = pp_typ ~cfg:default_config ~nested:false
let kind_to_string = pp_kind ~cfg:default_config
let xtor_to_string = pp_xtor ~cfg:default_config
let chiral_to_string = pp_chiral_typ ~cfg:default_config
let sgn_to_string = pp_sgn_typ
*)