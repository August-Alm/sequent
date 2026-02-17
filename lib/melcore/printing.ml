(**
  Module: Melcore.Printing
  Description: Pretty-printing for Melcore types and terms.
  
  Formats output similarly to the surface syntax (Lang.Syntax).
*)

open Common.Identifiers
open Types
open Terms

(* ========================================================================= *)
(* Configuration                                                             *)
(* ========================================================================= *)

type config =
  { indent_size: int
  ; show_kinds: bool   (* Whether to show kind annotations on binders *)
  ; show_types: bool   (* Whether to show type annotations on terms *)
  }

let default_config =
  { indent_size = 2
  ; show_kinds = false
  ; show_types = false
  }

(* ========================================================================= *)
(* Utilities                                                                 *)
(* ========================================================================= *)

let indent n = "\n" ^ String.make n ' '

let parens s = "(" ^ s ^ ")"
let braces s = "{" ^ s ^ "}"

(* ========================================================================= *)
(* Identifier printing                                                       *)
(* ========================================================================= *)

let pp_ident (id: Ident.t) : string = Ident.name id

let pp_path (p: Path.t) : string = Path.name p

(* ========================================================================= *)
(* Kind printing                                                             *)
(* ========================================================================= *)

let rec pp_kind ?(cfg=default_config) (k: kind) : string =
  ignore cfg;
  match k with
    Star -> "type"
  | Arrow (k1, k2) ->
      let s1 = match k1 with
          Arrow _ -> parens (pp_kind k1)
        | _ -> pp_kind k1
      in
      s1 ^ " -> " ^ pp_kind k2

(* ========================================================================= *)
(* Type printing                                                             *)
(* ========================================================================= *)

let pp_ext_typ (e: ext_typ) : string =
  match e with
    Int -> "int"

let rec pp_typ ?(cfg=default_config) (t: typ) : string =
  match t with
    Ext e -> pp_ext_typ e
  | Var {contents = Unbound id} -> "?" ^ pp_ident id
  | Var {contents = Link t'} -> pp_typ ~cfg t'
  | Rigid id -> pp_ident id
  | Sym (s, _, _) -> pp_path s
  | App (f, []) -> pp_typ ~cfg f
  | App (f, args) ->
      let f_str = pp_typ_base ~cfg f in
      let args_str = List.map (fun a -> parens (pp_typ ~cfg a)) args in
      f_str ^ String.concat "" args_str
  | Fun (t1, t2) ->
      let t1_str = match t1 with
        | Fun _ -> parens (pp_typ ~cfg t1)
        | _ -> pp_typ ~cfg t1
      in
      t1_str ^ " -> " ^ pp_typ ~cfg t2
  | All ((x, k), t) ->
      let k_str = if cfg.show_kinds then ": " ^ pp_kind ~cfg k else "" in
      braces (pp_ident x ^ k_str) ^ " " ^ pp_typ ~cfg t
  | Data sgn -> pp_sgn_typ ~cfg sgn
  | Code sgn -> pp_sgn_typ ~cfg sgn

and pp_typ_base ?(cfg=default_config) (t: typ) : string =
  match t with
  | Ext _ | Var _ | Rigid _ | Sym _ -> pp_typ ~cfg t
  | _ -> parens (pp_typ ~cfg t)

and pp_typ_atom ?(cfg=default_config) (t: typ) : string =
  match t with
  | Ext _ | Var _ | Rigid _ | Sym _ -> pp_typ ~cfg t
  | _ -> parens (pp_typ ~cfg t)

and pp_sgn_typ ?(cfg=default_config) (s: sgn_typ) : string =
  ignore cfg;
  pp_path s.name

(* ========================================================================= *)
(* Xtor printing                                                             *)
(* ========================================================================= *)

let pp_binder ?(cfg=default_config) ((id, k): Ident.t * kind) : string =
  if cfg.show_kinds then
    braces (pp_ident id ^ ": " ^ pp_kind ~cfg k)
  else
    braces (pp_ident id)

let pp_xtor_name (x: xtor) : string = pp_path x.name

let pp_xtor ?(cfg=default_config) (x: xtor) : string =
  let name = pp_path x.name in
  let params_str = String.concat " " (List.map (pp_binder ~cfg) x.parameters) in
  let args_str = 
    if x.arguments = [] then ""
    else String.concat " -> " (List.map (pp_typ ~cfg) x.arguments)
  in
  let main_str = pp_typ ~cfg x.main in
  let sep = if params_str = "" || args_str = "" then "" else " " in
  let body = params_str ^ sep ^ args_str ^ " -> " ^ main_str in
  name ^ ": " ^ body

(* ========================================================================= *)
(* Signature printing                                                        *)
(* ========================================================================= *)

let pp_sgn_full ?(cfg=default_config) ?(lvl=0) (s: sgn_typ) (is_data: bool) : string =
  let keyword = if is_data then "data" else "code" in
  let name = pp_path s.name in
  let kind_str =
    if s.parameters = [] then "type"
    else String.concat " -> " (List.map (pp_kind ~cfg) s.parameters) ^ " -> type"
  in
  let xtors_str =
    if s.xtors = [] then "{ }"
    else
      let xtor_strs = List.map (pp_xtor ~cfg) s.xtors in
      "{ " ^ String.concat (indent (lvl + cfg.indent_size) ^ "; ") xtor_strs ^
      indent lvl ^ "}"
  in
  keyword ^ " " ^ name ^ ": " ^ kind_str ^ " where" ^
  indent lvl ^ xtors_str

(* ========================================================================= *)
(* Term printing                                                             *)
(* ========================================================================= *)

let rec pp_term ?(cfg=default_config) ?(lvl=0) (tm: term) : string =
  match tm with
    Int n -> string_of_int n
  
  | Add (t1, t2) ->
      parens (pp_term ~cfg ~lvl t1 ^ " + " ^ pp_term ~cfg ~lvl t2)
  
  | Var x -> pp_ident x
  
  | Sym p -> pp_path p
  
  | App (t, u) ->
      pp_term_app ~cfg ~lvl t ^ parens (pp_term ~cfg ~lvl u)
  
  | Ins (t, ty) ->
      pp_term_app ~cfg ~lvl t ^ braces (pp_typ ~cfg ty)
  
  | Lam (x, ty_opt, body) ->
      let ty_str = match ty_opt with
        | None -> pp_ident x
        | Some ty -> parens (pp_ident x ^ ": " ^ pp_typ ~cfg ty)
      in
      "fun " ^ ty_str ^ " => " ^ pp_term ~cfg ~lvl body
  
  | All ((x, k), body) ->
      let k_str = if cfg.show_kinds then ": " ^ pp_kind ~cfg k else "" in
      "fun " ^ braces (pp_ident x ^ k_str) ^ " => " ^ pp_term ~cfg ~lvl body
  
  | Let (x, t, u) ->
      "let " ^ pp_ident x ^ " = " ^ pp_term ~cfg ~lvl t ^ " in" ^
      indent lvl ^ pp_term ~cfg ~lvl u
  
  | Match (t, branches) ->
      let branches_str =
        branches
        |> List.map (pp_branch ~cfg ~lvl:(lvl + cfg.indent_size))
        |> String.concat (indent lvl ^ "; ")
      in
      (if lvl = 0 then "" else indent lvl) ^
      "match " ^ pp_term ~cfg ~lvl t ^ " with" ^
      indent lvl ^ "{ " ^ branches_str ^
      indent lvl ^ "}"
  
  | New (ty_opt, branches) ->
      let ty_str = match ty_opt with
        | None -> ""
        | Some ty -> " " ^ pp_typ_atom ~cfg ty
      in
      let branches_str =
        branches
        |> List.map (pp_branch ~cfg ~lvl)
        |> String.concat "; "
      in
      "new" ^ ty_str ^ " { " ^ branches_str ^ " }"
  
  | Ctor (xtor, args) ->
      let name = pp_xtor_name xtor in
      let args_str = List.map (fun a -> parens (pp_term ~cfg ~lvl a)) args in
      name ^ String.concat "" args_str
  
  | Dtor (xtor, args) ->
      let name = pp_xtor_name xtor in
      let args_str = List.map (fun a -> parens (pp_term ~cfg ~lvl a)) args in
      name ^ String.concat "" args_str
  
  | Ifz (c, t, e) ->
      "ifz " ^ pp_term ~cfg ~lvl c ^ " then " ^
      pp_term ~cfg ~lvl t ^ " else " ^ pp_term ~cfg ~lvl e

and pp_term_app ?(cfg=default_config) ?(lvl=0) (tm: term) : string =
  match tm with
  | Int _ | Var _ | Sym _ | Add _ | App _ | Ins _ | Ctor _ | Dtor _ ->
      pp_term ~cfg ~lvl tm
  | _ -> parens (pp_term ~cfg ~lvl tm)

and pp_branch ?(cfg=default_config) ?(lvl=0) ((xtor, vars, body): branch) : string =
  let name = pp_xtor_name xtor in
  let vars_str = List.map (fun x -> parens (pp_ident x)) vars in
  name ^ String.concat "" vars_str ^ " => " ^ pp_term ~cfg ~lvl body

(* ========================================================================= *)
(* Typed term printing                                                       *)
(* ========================================================================= *)

let rec pp_typed_term ?(cfg=default_config) ?(lvl=0) (tm: typed_term) : string =
  match tm with
    TypedInt n -> string_of_int n
  
  | TypedAdd (t1, t2) ->
      parens (pp_typed_term ~cfg ~lvl t1 ^ " + " ^ pp_typed_term ~cfg ~lvl t2)
  
  | TypedVar (x, ty) ->
      if cfg.show_types then pp_ident x ^ " : " ^ pp_typ ~cfg ty
      else pp_ident x
  
  | TypedSym (p, ty) ->
      if cfg.show_types then pp_path p ^ " : " ^ pp_typ ~cfg ty
      else pp_path p
  
  | TypedApp (t, u, _) ->
      pp_typed_term_app ~cfg ~lvl t ^ parens (pp_typed_term ~cfg ~lvl u)
  
  | TypedIns (t, ty, _, _) ->
      pp_typed_term_app ~cfg ~lvl t ^ braces (pp_typ ~cfg ty)
  
  | TypedLam (x, ty, body, _) ->
      "fun " ^ parens (pp_ident x ^ ": " ^ pp_typ ~cfg ty) ^
      " => " ^ pp_typed_term ~cfg ~lvl body
  
  | TypedAll ((x, k), body, _) ->
      let k_str = if cfg.show_kinds then ": " ^ pp_kind ~cfg k else "" in
      "fun " ^ braces (pp_ident x ^ k_str) ^ " => " ^ pp_typed_term ~cfg ~lvl body
  
  | TypedLet (x, t, u, _) ->
      "let " ^ pp_ident x ^ " = " ^ pp_typed_term ~cfg ~lvl t ^ " in" ^
      indent lvl ^ pp_typed_term ~cfg ~lvl u
  
  | TypedMatch (t, branches, _) ->
      let branches_str =
        branches
        |> List.map (pp_typed_clause ~cfg ~lvl:(lvl + cfg.indent_size))
        |> String.concat (indent lvl ^ "; ")
      in
      (if lvl = 0 then "" else indent lvl) ^
      "match " ^ pp_typed_term ~cfg ~lvl t ^ " with" ^
      indent lvl ^ "{ " ^ branches_str ^
      indent lvl ^ "}"
  
  | TypedNew (branches, _) ->
      let branches_str =
        branches
        |> List.map (pp_typed_clause ~cfg ~lvl)
        |> String.concat "; "
      in
      "new { " ^ branches_str ^ " }"
  
  | TypedCtor (xtor, args, _) ->
      let name = pp_xtor_name xtor in
      let args_str = List.map (fun a -> parens (pp_typed_term ~cfg ~lvl a)) args in
      name ^ String.concat "" args_str
  
  | TypedDtor (xtor, args, _) ->
      let name = pp_xtor_name xtor in
      let args_str = List.map (fun a -> parens (pp_typed_term ~cfg ~lvl a)) args in
      name ^ String.concat "" args_str
  
  | TypedIfz (c, t, e, _) ->
      "ifz " ^ pp_typed_term ~cfg ~lvl c ^ " then " ^
      pp_typed_term ~cfg ~lvl t ^ " else " ^ pp_typed_term ~cfg ~lvl e

and pp_typed_term_app ?(cfg=default_config) ?(lvl=0) (tm: typed_term) : string =
  match tm with
  | TypedInt _ | TypedVar _ | TypedSym _ | TypedAdd _ | TypedApp _ 
  | TypedIns _ | TypedCtor _ | TypedDtor _ ->
      pp_typed_term ~cfg ~lvl tm
  | _ -> parens (pp_typed_term ~cfg ~lvl tm)

and pp_typed_clause ?(cfg=default_config) ?(lvl=0) 
    ((xtor, _ty_vars, tm_vars, body): typed_clause) : string =
  let name = pp_xtor_name xtor in
  let vars_str = List.map (fun x -> parens (pp_ident x)) tm_vars in
  name ^ String.concat "" vars_str ^ " => " ^ pp_typed_term ~cfg ~lvl body

(* ========================================================================= *)
(* Term definition printing                                                  *)
(* ========================================================================= *)

let pp_term_def ?(cfg=default_config) (def: term_def) : string =
  let name = pp_path def.name in
  let ty_args_str = List.map (pp_binder ~cfg) def.type_args |> String.concat "" in
  let tm_args_str = 
    def.term_args 
    |> List.map (fun (x, ty) -> parens (pp_ident x ^ ": " ^ pp_typ ~cfg ty))
    |> String.concat ""
  in
  let ret_str = pp_typ ~cfg def.return_type in
  let body_str = pp_term ~cfg ~lvl:cfg.indent_size def.body in
  "let " ^ name ^ ty_args_str ^ tm_args_str ^ ": " ^ ret_str ^ " =" ^
  indent cfg.indent_size ^ body_str

let pp_typed_term_def ?(cfg=default_config) (def: typed_term_def) : string =
  let name = pp_path def.name in
  let ty_args_str = List.map (pp_binder ~cfg) def.type_args |> String.concat "" in
  let tm_args_str = 
    def.term_args 
    |> List.map (fun (x, ty) -> parens (pp_ident x ^ ": " ^ pp_typ ~cfg ty))
    |> String.concat ""
  in
  let ret_str = pp_typ ~cfg def.return_type in
  let body_str = pp_typed_term ~cfg ~lvl:cfg.indent_size def.body in
  "let " ^ name ^ ty_args_str ^ tm_args_str ^ ": " ^ ret_str ^ " =" ^
  indent cfg.indent_size ^ body_str

(* ========================================================================= *)
(* Convenience functions                                                     *)
(* ========================================================================= *)

let typ_to_string = pp_typ ~cfg:default_config
let kind_to_string = pp_kind ~cfg:default_config
let term_to_string = pp_term ~cfg:default_config ~lvl:0
let typed_term_to_string = pp_typed_term ~cfg:default_config ~lvl:0
let xtor_to_string = pp_xtor ~cfg:default_config
let term_def_to_string = pp_term_def ~cfg:default_config
let typed_term_def_to_string = pp_typed_term_def ~cfg:default_config
