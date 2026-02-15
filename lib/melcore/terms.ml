(**
  module: Melcore.Terms
  description: Abstract syntax for the Melcore language.
*)

open Common.Identifiers
open Types

type var = Ident.t

type term =
  (* n *)
  | Int of int
  (* t + u *)
  | Add of term * term
  (* x *)
  | Var of var
  (* name *)
  | Sym of Path.t
  (* t(u) *)
  | App of term * term
  (* t{ty} *)
  | Ins of term * typ
  (* fun x => t or fun(x: a) => t *)
  | Lam of var * (typ option) * term
  (* all {a: k} t *)
  | All of (var * kind) * term
  (* let x = t in u *)
  | Let of var * term * term
  (* match t with { branches } *)
  | Match of term * (branch list)
  (* new { branches } or new ty { branches }*)
  | New of (typ option) * (branch list)
  (* ctor{ai's}(ti's); type and term arguments *)
  | Ctor of xtor * (term list)
  (* dtor{ai's}(ti's); type and term arguments *)
  | Dtor of xtor * (term list)

and branch =
  (* xtor(ti's) => t; type and term arguments, and return *)
  xtor * (var list) * term

(* Typed terms: AST with type annotations *)
type typed_term =
  | TypedInt of int
  | TypedAdd of typed_term * typed_term
  | TypedVar of var * typ
  | TypedSym of Path.t * typ
  | TypedApp of typed_term * typed_term * typ
  | TypedIns of typed_term * typ * kind * typ
  | TypedLam of var * typ * typed_term * typ
  | TypedAll of (var * kind) * typed_term * typ
  | TypedLet of var * typed_term * typed_term * typ
  | TypedMatch of typed_term * typed_clause list * typ
  | TypedNew of typ option * typed_clause list * typ
  | TypedCtor of xtor * typ list * typed_term list * typ
  | TypedDtor of xtor * typ list * typed_term list * typ

and typed_clause =
  xtor * var list * var list * typed_term

let get_type (tm: typed_term) : typ =
  match tm with
  | TypedInt _ -> Ext Int
  | TypedAdd (_, _) -> Ext Int
  | TypedVar (_, ty) -> ty
  | TypedSym (_, ty) -> ty
  | TypedApp (_, _, ty) -> ty
  | TypedIns (_, _, _, ty) -> ty
  | TypedLam (_, _, _, ty) -> ty
  | TypedAll (_, _, ty) -> ty
  | TypedLet (_, _, _, ty) -> ty
  | TypedMatch (_, _, ty) -> ty
  | TypedNew (_, _, ty) -> ty
  | TypedCtor (_, _, _, ty) -> ty
  | TypedDtor (_, _, _, ty) -> ty

type term_def =
  { name: Path.t
  ; type_args: (var * kind) list
  ; term_args: (var * typ) list
  ; return_type: typ
  ; body: term
  }

type typed_term_def =
  { name: Path.t
  ; type_args: (var * kind) list
  ; term_args: (var * typ) list
  ; return_type: typ
  ; body: typed_term
  }

type definitions = term_def Path.tbl

type typed_definitions = typed_term_def Path.tbl

type context =
  { kinds: kind Ident.tbl
  ; types: typ Ident.tbl
  }

type check_error =
    UnboundVariable of var
  | UnboundSymbol of Path.t
  | TypeMismatch of { expected: typ; actual: typ }
  | ExpectedData of typ  (* Type was expected to be a data type *)
  | ExpectedCode of typ  (* Type was expected to be a codata type *)
  | SignatureMismatch of sgn_typ * sgn_typ  (* Expected, actual *)
  | XtorNotInSignature of xtor * sgn_typ
  | NonExhaustive of xtor list  (* Missing branches for these reachable xtors *)
  | ArityMismatch of { xtor: xtor; expected: int; actual: int }
  | UnificationFailed of typ * typ

let lookup (ctx: context) (v: var) : (typ, check_error) result =
  match Ident.find_opt v ctx.types with
  | Some ct -> Ok ct
  | None -> Error (UnboundVariable v)

let extend (ctx: context) (v: var) (ct: typ) : context =
  { ctx with types = Ident.add v ct ctx.types }

let extend_many (ctx: context) (bindings: (var * typ) list) : context =
  List.fold_left (fun ctx (v, ct) -> extend ctx v ct) ctx bindings