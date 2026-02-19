(**
  module: Melcore.Types
  description: Type system of the Melcore language.

  It incorporates the following features:
  - Polarity (positive/negative) to distinguish data and codata types
  - Higher-kinded types
  - Generalized algebraic data types
  - Generalized algebraic codata types
  - Algebraic data types automatically promoted to the kind level
*)

open Common.Types

module MelcoreBase = struct
  type polarity = Pos | Neg
  let eq_polarity p1 p2 = (p1 = p2)
  let data_polarity = Pos
  let code_polarity = Neg
  let polarities = [Pos; Neg]

  type 'a chiral = 'a
  let chiral_map f x =  f x
  let strip_chirality x = x
  let mk_producer x = x
  let mk_consumer x = x
  let is_producer _ = true
  let is_consumer _ = true
end

module MelcoreTypes = TypeSystem(MelcoreBase)
open MelcoreTypes
open Common.Identifiers

(** Get the polarity of an inhabitable type.
    Returns None for non-inhabitable types (e.g., higher kinds, data kinds). *)
let polarity_of (ctx: context) (t: typ) : MelcoreBase.polarity option =
  match t with
    Base p -> Some p
  | Ext _ -> Some Pos  (* External types are positive/data *)
  | Sgn (name, _) ->
      (match Path.find_opt name ctx.decs with
        Some dec -> Some dec.polarity | None -> None)
  | Fun (_, _) -> Some Neg  (* Functions are codata *)
  | Forall (_, _, _) -> Some Neg  (* Forall is codata *)
  | Raise _ -> Some Pos  (* Raise lifts codata to data *)
  | Lower _ -> Some Neg  (* Lower lifts data to codata *)
  | TVar v | TMeta v ->
      (* Look up in context to see if we know the kind *)
      (match Ident.find_opt v ctx.typ_vars with
        Some (Base p) -> Some p | _ -> None)
  | PromotedCtor (_, _, _) -> None  (* Promoted ctors are type-level, not inhabitable *)
  | Arrow (_, _) -> None  (* Arrow is for kinds, not inhabitable *)

(** Polarize a type for use as the domain of Fun.
    Domain must be positive (data), so wrap negative types with Raise. *)
let polarize_domain (ctx: context) (t: typ) : typ =
  match polarity_of ctx t with
  | Some Neg -> Raise t
  | _ -> t  (* Pos or unknown: leave as-is *)

(** Polarize a type for use as the codomain of Fun.
    Codomain must be negative (codata), so wrap positive types with Lower. *)
let polarize_codomain (ctx: context) (t: typ) : typ =
  match polarity_of ctx t with Some Pos -> Lower t | _ -> t

(** Build a function type from user-level domain and codomain,
    applying appropriate polarity shifts. *)
let mk_fun (ctx: context) (dom: typ) (cod: typ) : typ =
  Fun (polarize_domain ctx dom, polarize_codomain ctx cod)

(** Extract the user-visible domain from a function type's internal domain.
    Unwraps Raise if present. *)
let depolarize_domain (t: typ) : typ =
  match t with Raise t' -> t' | _ -> t

(** Extract the user-visible codomain from a function type's internal codomain.
    Unwraps Lower if present. *)
let depolarize_codomain (t: typ) : typ =
  match t with Lower t' -> t' | _ -> t

(** Extract user-visible domain and codomain from an internal Fun type. *)
let unmk_fun (t: typ) : (typ * typ) option =
  match t with
    Fun (dom, cod) -> Some (depolarize_domain dom, depolarize_codomain cod)
  | _ -> None

(** Build a forall type from user-level body, applying appropriate polarity shift.
    Body must be negative (codata), so wrap positive types with Lower. *)
let mk_forall (ctx: context) (x: Ident.t) (k: typ) (body: typ) : typ =
  Forall (x, k, polarize_codomain ctx body)

(** Extract user-visible body from an internal Forall type.
    Unwraps Lower if present. *)
let unmk_forall (t: typ) : (Ident.t * typ * typ) option =
  match t with
    Forall (x, k, body) -> Some (x, k, depolarize_codomain body)
  | _ -> None
