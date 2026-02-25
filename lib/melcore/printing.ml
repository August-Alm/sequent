(**
  Module: Melcore.Printing
  Description: Pretty-printing for Melcore types and terms.
  
  Formats output similarly to the surface syntax (Lang.Syntax).
*)

open Common.Identifiers
open Types.MelcoreTypes
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
let brackets s = "[" ^ s ^ "]"

(* ========================================================================= *)
(* Identifier printing                                                       *)
(* ========================================================================= *)

let pp_ident (id: Ident.t) : string = Ident.name id

let pp_path (p: Path.t) : string = Path.name p

(* ========================================================================= *)
(* Type/Kind printing                                                        *)
(* ========================================================================= *)

(* In the modular type system, kinds are just types with Base polarity *)
let rec pp_kind ?(cfg=default_config) (k: typ) : string =
  ignore cfg;
  match k with
    Base _ -> "type"
  | Arrow (k1, k2) ->
      let s1 = match k1 with
          Arrow _ -> parens (pp_kind k1)
        | _ -> pp_kind k1
      in
      s1 ^ " -> " ^ pp_kind k2
  | _ -> pp_typ ~cfg k  (* Fall back to type printing for other cases *)

and pp_typ ?(cfg=default_config) ?(nested=false) (t: typ) : string =
  match t with
    Base _ -> "type"
  | Arrow (k1, k2) ->
      let s1 = match k1 with
          Arrow _ -> parens (pp_typ ~cfg ~nested:true k1)
        | _ -> pp_typ ~cfg ~nested:true k1
      in
      let inner = s1 ^ " -> " ^ pp_typ ~cfg ~nested:false k2 in
      if nested then parens inner else inner
  | Ext Int -> "int"
  | TVar id -> pp_ident id
  | TMeta id -> "?" ^ pp_ident id
  | Sgn (name, []) -> pp_path name
  | Sgn (s, [dom; cod]) when Path.equal s Common.Types.Prim.fun_sym ->
      (* Depolarize to show user-level types *)
      let dom_str = match dom with
          Sgn (s, [_; _]) when Path.equal s Common.Types.Prim.fun_sym ->
            parens (pp_typ ~cfg ~nested:true dom)
        | Forall _ -> parens (pp_typ ~cfg ~nested:true dom)
        | _ -> pp_typ ~cfg ~nested:true dom
      in
      let inner = dom_str ^ " -> " ^ pp_typ ~cfg ~nested:false cod in
      if nested then parens inner else inner
  | Sgn (name, args) ->
      let name_str = pp_path name in
      let args_str = List.map (fun a -> parens (pp_typ ~cfg ~nested:false a)) args in
      name_str ^ String.concat "" args_str
  | PromotedCtor (dec, ctor, []) ->
      "'" ^ pp_path dec ^ "." ^ pp_path ctor
  | PromotedCtor (dec, ctor, args) ->
      let base = "'" ^ pp_path dec ^ "." ^ pp_path ctor in
      let args_str = List.map (fun a -> parens (pp_typ ~cfg ~nested:false a)) args in
      base ^ String.concat "" args_str
  | Forall (x, k, body) ->
      (* Depolarize body to show user-level type *)
      let k_str = if cfg.show_kinds then ": " ^ pp_kind ~cfg k else "" in
      let inner = braces (pp_ident x ^ k_str) ^ " " ^ pp_typ ~cfg ~nested:false body in
      if nested then parens inner else inner

and pp_typ_base ?(cfg=default_config) (t: typ) : string =
  match t with
    Ext _ | TVar _ | TMeta _ | Sgn (_, []) -> pp_typ ~cfg t
  | _ -> parens (pp_typ ~cfg t)

(* pp_typ_atom: types that don't need outer parens in most contexts.
   App (Sgn with args) is included because its arguments are already parenthesized.
   Only Fun and Forall need parens since they use infix/prefix syntax. *)
and pp_typ_atom ?(cfg=default_config) (t: typ) : string =
  match t with
    Base _ | Ext _ | TVar _ | TMeta _ | Sgn _ | PromotedCtor _ | Arrow _ -> pp_typ ~cfg t
  | Forall _ -> parens (pp_typ ~cfg t)

(* ========================================================================= *)
(* Xtor printing                                                             *)
(* ========================================================================= *)

let pp_binder ?(cfg=default_config) ((id, k): Ident.t * typ) : string =
  if cfg.show_kinds then
    braces (pp_ident id ^ ": " ^ pp_kind ~cfg k)
  else
    braces (pp_ident id)

let pp_xtor_name (x: sym) : string = pp_path x

let pp_chiral_typ ?(cfg=default_config) (ct: chiral_typ) : string =
  pp_typ ~cfg (strip_chirality ct)

(** Print an xtor with its polarity context.
    - For constructors (data/positive): {qi's} arg0 -> ... -> argN -> main
    - For destructors (codata/negative): {qi's} main -> argN -> ... -> arg0 *)
let pp_xtor_with_polarity ?(cfg=default_config) (is_data: bool) (x: xtor) : string =
  let name = pp_path x.name in
  let params_str = String.concat " " (List.map (pp_binder ~cfg) x.quantified) in
  let args = List.map (pp_chiral_typ ~cfg) x.argument_types in
  let main_str = pp_typ ~cfg x.main in
  let components =
    if is_data then
      (* Constructor: arg0 -> ... -> argN -> main *)
      args @ [main_str]
    else
      (* Destructor: main -> argN -> ... -> arg0 *)
      [main_str] @ List.rev args
  in
  let body_str = String.concat " -> " components in
  let sep = if params_str = "" then "" else " " in
  name ^ ": " ^ params_str ^ sep ^ body_str

(** Print an xtor assuming constructor format (for backwards compatibility) *)
let pp_xtor ?(cfg=default_config) (x: xtor) : string =
  pp_xtor_with_polarity ~cfg true x

(* ========================================================================= *)
(* Declaration printing                                                      *)
(* ========================================================================= *)

let pp_dec_full ?(cfg=default_config) ?(lvl=0) (d: dec) : string =
  let is_data = (d.data_sort = Data) in
  let keyword = if is_data then "data" else "code" in
  let name = pp_path d.name in
  let kind_str =
    if d.param_kinds = [] then "type"
    else String.concat " -> " (List.map (pp_kind ~cfg) d.param_kinds) ^ " -> type"
  in
  let xtors_str =
    if d.xtors = [] then "{ }"
    else
      let xtor_strs = List.map (pp_xtor_with_polarity ~cfg is_data) d.xtors in
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
  
  | Sub (t1, t2) ->
      parens (pp_term ~cfg ~lvl t1 ^ " - " ^ pp_term ~cfg ~lvl t2)
  
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
        |> List.map (pp_branch ~cfg ~lvl:(lvl + cfg.indent_size))
        |> String.concat (indent lvl ^ "; ")
      in
      "new" ^ ty_str ^
      indent lvl ^ "{ " ^ branches_str ^
      indent lvl ^ "}"
  
  | Ctor (_, xtor, ty_args, tm_args) ->
      let name = pp_xtor_name xtor in
      let ty_args_str = List.map (fun a -> braces (pp_typ ~cfg a)) ty_args in
      let tm_args_str = List.map (fun a -> parens (pp_term ~cfg ~lvl a)) tm_args in
      name ^ String.concat "" ty_args_str ^ String.concat "" tm_args_str
  
  | Dtor (_, xtor, ty_args, tm_args) ->
      let name = pp_xtor_name xtor in
      let ty_args_str = List.map (fun a -> braces (pp_typ ~cfg a)) ty_args in
      let tm_args_str = List.map (fun a -> parens (pp_term ~cfg ~lvl a)) tm_args in
      name ^ String.concat "" ty_args_str ^ String.concat "" tm_args_str
  
  | Ifz (c, t, e) ->
      "ifz " ^ pp_term ~cfg ~lvl c ^ " then " ^
      pp_term ~cfg ~lvl t ^ " else " ^ pp_term ~cfg ~lvl e

and pp_term_app ?(cfg=default_config) ?(lvl=0) (tm: term) : string =
  match tm with
    Int _ | Var _ | Sym _ | Add _ | Sub _ | App _ | Ins _ | Ctor _ | Dtor _ ->
      pp_term ~cfg ~lvl tm
  | _ -> parens (pp_term ~cfg ~lvl tm)

and pp_branch ?(cfg=default_config) ?(lvl=0) ((xtor, ty_vars, tm_vars, body): branch) : string =
  let name = pp_xtor_name xtor in
  let ty_vars_str = List.map (fun x -> braces (pp_ident x)) ty_vars in
  let tm_vars_str = List.map (fun x -> parens (pp_ident x)) tm_vars in
  (* For multi-line bodies like Match/New, put on new line with extra indentation *)
  let body_str = match body with
      Match _ | New _ ->
        let body_lvl = lvl + cfg.indent_size in
        indent body_lvl ^ pp_term ~cfg ~lvl:body_lvl body
    | _ -> pp_term ~cfg ~lvl body
  in
  name ^ String.concat "" ty_vars_str ^ String.concat "" tm_vars_str ^ " => " ^ body_str

(* ========================================================================= *)
(* Typed term printing                                                       *)
(* ========================================================================= *)

let rec pp_typed_term ?(cfg=default_config) ?(lvl=0) (tm: typed_term) : string =
  match tm with
    TypedInt n -> string_of_int n
  
  | TypedAdd (t1, t2) ->
      parens (pp_typed_term ~cfg ~lvl t1 ^ " + " ^ pp_typed_term ~cfg ~lvl t2)
  
  | TypedSub (t1, t2) ->
      parens (pp_typed_term ~cfg ~lvl t1 ^ " - " ^ pp_typed_term ~cfg ~lvl t2)
  
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
  
  | TypedCtor (_, xtor, ty_args, args, _) ->
      let name = pp_xtor_name xtor in
      let ty_args_str = if ty_args = [] then ""
        else "{" ^ String.concat ", " (List.map (pp_typ ~cfg) ty_args) ^ "}"
      in
      let args_str = List.map (fun a -> parens (pp_typed_term ~cfg ~lvl a)) args in
      name ^ ty_args_str ^ String.concat "" args_str
  
  | TypedDtor (_, xtor, ty_args, args, _) ->
      let name = pp_xtor_name xtor in
      let ty_args_str = if ty_args = [] then ""
        else "{" ^ String.concat ", " (List.map (pp_typ ~cfg) ty_args) ^ "}"
      in
      let args_str = List.map (fun a -> parens (pp_typed_term ~cfg ~lvl a)) args in
      name ^ ty_args_str ^ String.concat "" args_str
  
  | TypedIfz (c, t, e, _) ->
      "ifz " ^ pp_typed_term ~cfg ~lvl c ^ " then " ^
      pp_typed_term ~cfg ~lvl t ^ " else " ^ pp_typed_term ~cfg ~lvl e

and pp_typed_term_app ?(cfg=default_config) ?(lvl=0) (tm: typed_term) : string =
  match tm with
    TypedInt _ | TypedVar _ | TypedSym _ | TypedAdd _ | TypedSub _ | TypedApp _ 
  | TypedIns _ | TypedCtor _ | TypedDtor _ -> pp_typed_term ~cfg ~lvl tm
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
  let ty_args_str = List.map (pp_binder ~cfg) def.type_params |> String.concat "" in
  let tm_args_str = 
    def.term_params 
    |> List.map (fun (x, ty) -> parens (pp_ident x ^ ": " ^ pp_typ ~cfg ty))
    |> String.concat ""
  in
  let ret_str = pp_typ ~cfg def.return_type in
  let body_str = pp_term ~cfg ~lvl:cfg.indent_size def.body in
  "let " ^ name ^ ty_args_str ^ tm_args_str ^ ": " ^ ret_str ^ " =" ^
  indent cfg.indent_size ^ body_str

let pp_typed_term_def ?(cfg=default_config) (def: typed_term_def) : string =
  let name = pp_path def.name in
  let ty_args_str = List.map (pp_binder ~cfg) def.type_params |> String.concat "" in
  let tm_args_str = 
    def.term_params 
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

(* ========================================================================= *)
(* Error Printing                                                            *)
(* ========================================================================= *)

(** Pretty-print a kind error *)
let pp_kind_error ?(cfg=default_config) (err: Types.MelcoreTypes.kind_error) : string =
  match err with
  | Unbound_type_variable v ->
      "unbound type variable: " ^ pp_ident v
  | Unbound_meta_variable v ->
      "unbound meta variable: ?" ^ pp_ident v
  | Unknown_data_type p ->
      "unknown data type: " ^ pp_path p
  | Unknown_promoted_ctor (dec, ctor) ->
      "unknown promoted constructor: '" ^ pp_path dec ^ "." ^ pp_path ctor
  | Not_a_promoted_type p ->
      "not a promoted type: " ^ pp_path p
  | Invalid_kind k ->
      "invalid kind: " ^ pp_typ ~cfg k
  | Kind_mismatch { expected; actual; in_type } ->
      "kind mismatch in " ^ pp_typ ~cfg in_type ^
      ": expected " ^ pp_kind ~cfg expected ^
      ", got " ^ pp_kind ~cfg actual
  | Arity_mismatch { kind; num_args } ->
      let kind_str = match kind with
        | Some k -> pp_kind ~cfg k
        | None -> "<unknown>"
      in
      "arity mismatch: kind " ^ kind_str ^
      " applied to " ^ string_of_int num_args ^ " arguments"
  | Arrow_domain_not_typ t ->
      "arrow domain is not a type: " ^ pp_typ ~cfg t
  | Arrow_codomain_not_typ t ->
      "arrow codomain is not a type: " ^ pp_typ ~cfg t
  | Too_many_arguments { kind; extra_args } ->
      "too many arguments for kind " ^ pp_kind ~cfg kind ^
      ": extra args " ^
      String.concat ", " (List.map (pp_typ ~cfg) extra_args)

let kind_error_to_string = pp_kind_error ~cfg:default_config

(** Pretty-print a type check error *)
let pp_check_error ?(cfg=default_config) (err: check_error) : string =
  match err with
  | UnboundVariable v ->
      "unbound variable: " ^ pp_ident v
  | UnboundSymbol s ->
      "unbound symbol: " ^ pp_path s
  | UnboundDeclaration s ->
      "unbound declaration: " ^ pp_path s
  | UnboundXtor (dec, xtor) ->
      "unbound constructor " ^ pp_path xtor ^ " in " ^ pp_path dec
  | TypeMismatch { expected; actual } ->
      "type mismatch: expected " ^ pp_typ ~cfg expected ^
      ", got " ^ pp_typ ~cfg actual
  | ExpectedFun t ->
      "expected function type, got " ^ pp_typ ~cfg t
  | ExpectedForall t ->
      "expected forall type, got " ^ pp_typ ~cfg t
  | ExpectedData t ->
      "expected data type, got " ^ pp_typ ~cfg t
  | ExpectedCodata t ->
      "expected codata type, got " ^ pp_typ ~cfg t
  | XtorArityMismatch { xtor; expected; got } ->
      "constructor " ^ pp_path xtor ^
      " expects " ^ string_of_int expected ^ " arguments, got " ^ string_of_int got
  | TypeArgArityMismatch { xtor; expected; got } ->
      "constructor " ^ pp_path xtor ^
      " expects " ^ string_of_int expected ^ " type arguments, got " ^ string_of_int got
  | NonExhaustive { dec; missing } ->
      "non-exhaustive pattern match on " ^ pp_path dec ^
      ": missing " ^ String.concat ", " (List.map pp_path missing)
  | UnificationFailed (t1, t2) ->
      "unification failed: " ^ pp_typ ~cfg t1 ^ " ≠ " ^ pp_typ ~cfg t2
  | KindError ke ->
      "kind error: " ^ pp_kind_error ~cfg ke

let check_error_to_string = pp_check_error ~cfg:default_config
