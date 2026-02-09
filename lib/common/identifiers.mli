
module Ident: sig
  type t
  val mk: string -> t
  val name: t -> string
  val stamp: t -> int
  val equal: t -> t -> bool
  val compare: t -> t -> int

  val fresh: unit -> t
  val mk_primitive: int -> string -> t

  type 'a tbl
  val emptytbl: 'a tbl
  val is_empty: 'a tbl -> bool
  val add: t -> 'a -> 'a tbl -> 'a tbl
  val find: t -> 'a tbl -> 'a
  val find_opt: t -> 'a tbl -> 'a option
  val filter: (t -> 'a -> bool) -> 'a tbl -> 'a tbl
  val join: 'a tbl -> 'a tbl -> 'a tbl
  val of_list: (t * 'a) list -> 'a tbl
  val to_list: 'a tbl -> (t * 'a) list
  val contains_key: t -> 'a tbl -> bool
end

module Path: sig
  type t
  val equal: t -> t -> bool
  val compare: t -> t -> int
  val of_ident: Ident.t -> t
  val stamp_unsafe: t -> int
  val of_primitive: int -> string -> t
  val of_string: string -> t
  val as_ident: t -> Ident.t option
  val access: t -> string -> t
  val is_rooted_at: Ident.t -> t -> bool
  val name: t -> string

  type 'a tbl
  val emptytbl: 'a tbl
  val is_empty: 'a tbl -> bool
  val add: t -> 'a -> 'a tbl -> 'a tbl
  val find: t -> 'a tbl -> 'a
  val find_opt: t -> 'a tbl -> 'a option
  val filter: (t -> 'a -> bool) -> 'a tbl -> 'a tbl
  val join: 'a tbl -> 'a tbl -> 'a tbl
  val of_list: (t * 'a) list -> 'a tbl
  val to_list: 'a tbl -> (t * 'a) list
  val contains_key: t -> 'a tbl -> bool

  type subst
  val add_subst: Ident.t -> t -> subst -> subst
  val find_subst: Ident.t -> subst -> t
  val none: subst
  val path: t -> subst -> t
end
