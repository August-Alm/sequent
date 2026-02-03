(**
  Module: Common.Types
  Description: Types for sequent calculi.
  
  This module defines the type-level language of the intermediate representations
  based on sequent calculi. It includes generalized algebraic (co)data types and
  higher-kinded types.
*)

open Identifiers

type kind = KStar | KArrow of kind * kind

type typ =
  | TySym of Path.t
  | TyVar of Ident.t
  | TyApp of typ * typ
  (*
  | TyFun of typ * typ (* `->` type constructor *)
  | TyAll of (Ident.t * kind) * typ (* `forall` type constructor, `{a: k} ty` *)
  *)
  | TyDef of ty_def

and ty_def =
  | Data of ty_dec
  | Code of ty_dec
  | Prim of Path.t * kind

and ty_dec =
  { symbol: Path.t
  (* arguments are `None` until they are instantiated by type application *)
  ; arguments: (typ option * kind) list
  ; xtors: ty_xtor list
  }

and ty_xtor =
  { parent: Path.t (* parent ty_dec symbol *)
  ; symbol: Path.t
  ; quantified: (Ident.t * kind) list
  ; producers: typ list
  ; consumers: typ list
  ; arguments: typ list
  (* constraints imposed by instantiation and unification *)
  ; constraints: (Ident.t * typ) list option
  }

module Prim = struct
  let int_sym = Path.of_primitive 1 "int"
  let int_def = Prim (int_sym, KStar)
  let int_typ = TyDef int_def
  let add_sym = Path.of_primitive 2 "add"

  let fun_sym = Path.of_primitive 100 "$fun"
  let app_dtor_sym = Path.of_primitive 101 "$app"
  let fun_def =
    let a = Ident.mk "a" in
    let b = Ident.mk "b" in
    Code
    { symbol = fun_sym
    ; arguments = [(None, KStar); (None, KStar)]
    ; xtors =
        [ { parent = fun_sym
          ; symbol = app_dtor_sym
          ; quantified = [(a, KStar); (b, KStar)]
          ; producers = [TyVar a]
          ; consumers = [TyVar b]
          ; arguments = [TyVar a; TyVar b]
          ; constraints = None
          }
        ]
    }
  let fun_typ = TyDef fun_def

  (* injective encoding of kinds as positive even integers above 1000 *)
  let to_int (k: kind) : int =
    (* Cantor's pair(x, y) = (x + y)(x + y + 1)/2 + y is bijection ℕ × ℕ → ℕ *)
    let rec go k =
      match k with
      | KStar -> 0
      | KArrow (k1, k2) ->
        let n1 = go k1 in
        let n2 = go k2 in
        let sum = n1 + n2 in
        1 + (sum * (sum + 1)) / 2 + n2
    (* double and shift to integers > 999 *)
    in 1000 + 2 * go k

  (* inverse: decode integer back to kind; n >= 1000 and even *)
  let of_int (n: int): kind =
    (* inverse of Cantor's pairing function *)
    let unpair z =
      let w = int_of_float (floor ((sqrt (float_of_int (8 * z + 1)) -. 1.0) /. 2.0)) in
      let t = (w * (w + 1)) / 2 in
      let y = z - t in
      let x = w - y in
      (x, y)
    in
    (* undo shift and doubling *)
    let m = (n - 1000) / 2 in
    let rec go m =
      if m = 0 then KStar
      else
        let (n1, n2) = unpair (m - 1) in
        KArrow (go n1, go n2)
    in
    go m

  let all_sym k = Path.of_primitive (to_int k) "$forall"
  let ins_dtor_sym k = Path.of_primitive (1 + to_int k) "$inst"
  
  let of_all_sym (sym: Path.t) : kind option =
    match Path.as_ident sym with
    | Some id ->
      let stamp = Ident.stamp id in
      let name = Ident.name id in
      if name = "$forall" && stamp < 0 && (-stamp) >= 100 && (-stamp) mod 2 = 0 then
        Some (of_int (-stamp))
      else
        None
    | None -> None
  
  let all_def a k =
    let t = Ident.mk "t" in
    Code
    { symbol = all_sym k
    ; arguments = [(None, KArrow (k, KStar))]
    ; xtors =
        [ { parent = all_sym k
          ; symbol = ins_dtor_sym k
          ; quantified = [(t,KArrow (k, KStar)); (a, k)]
          ; producers = []
          ; consumers = [TyApp (TyVar t, TyVar a)]
          ; arguments = [TyVar t]
          ; constraints = None
          }
        ]
    }
  let all_typ a k = TyDef (all_def a k)

end

type ty_defs = (Path.t * (ty_def * kind)) list

let primitive_ty_defs : ty_defs =
  [ (Prim.int_sym, (Prim.int_def, KStar))
  ; (Prim.fun_sym, (Prim.fun_def, KArrow (KStar, KArrow (KStar, KStar))))
  ]

let rec get_def (defs: ty_defs) (sym: Path.t) =
  match defs with
  | [] -> failwith ("undefined type symbol: " ^ Path.name sym)
  | (s, def) :: rest -> if Path.equal s sym then def else get_def rest sym

let get_kind (ks: (typ option * kind) list) =
  let rec loop ks =
    match ks with
    | [] -> KStar
    | (Some _, _) :: rest -> loop rest
    | (None, k) :: rest -> KArrow (k, loop rest)
  in 
  loop ks

(* Pretty printing *)
let rec kind_to_string (k: kind) : string =
  kind_to_string_prec false k

and kind_to_string_prec (needs_parens: bool) (k: kind) : string =
  match k with
  | KStar -> "type"
  | KArrow (k1, k2) ->
    let s = kind_to_string_prec true k1 ^ " -> " ^ kind_to_string_prec false k2 in
    if needs_parens then "(" ^ s ^ ")" else s

let rec typ_to_string (nested: bool) (t: typ) : string =
  match t with
  | TySym s -> Path.name s
  | TyVar x -> Ident.name x
  | TyApp (t1, t2) -> typ_to_string nested t1 ^ "(" ^ typ_to_string nested t2 ^ ")"
  (*
  | TyFun (t1, t2) -> typ_to_string_atom nested t1 ^ " -> " ^ typ_to_string nested t2
  | TyAll ((x, k), t) -> 
    "{" ^ Ident.name x ^ ": " ^ kind_to_string k ^ "} " ^ typ_to_string nested t
  *)
  | TyDef (Data td) -> data_to_string nested td
  | TyDef (Code td) -> code_to_string nested td
  | TyDef (Prim (s, _)) -> Path.name s

and typ_to_string_atom (nested: bool) (t: typ) : string =
  match t with
  (*
  | TyFun _ | TyAll _ -> "(" ^ typ_to_string nested t ^ ")"
  *)
  | _ -> typ_to_string nested t

and data_to_string (nested: bool) (td: ty_dec) : string =
  if nested then
    let args_str =
      td.arguments
      |> List.take_while (fun (t_opt, _) -> Option.is_some t_opt)
      |> List.map (fun (t_opt, _) ->
        match t_opt with
        | Some t -> "(" ^ typ_to_string true t ^ ")"
        | None -> failwith "impossible!")
      |> String.concat "" 
    in
    Path.name td.symbol ^ args_str
  else
    let arg_to_string ((t_opt, _): typ option * kind) : string =
      match t_opt with
      | Some t -> "(" ^ typ_to_string true t ^ ")"
      | None -> ""
    in
    let args_str =
      String.concat "" (List.map arg_to_string td.arguments)
    in
    let ctors_str =
      String.concat "\n  " (List.map ctor_to_string td.xtors)
    in
    "data " ^ Path.name td.symbol ^ args_str ^ ": " ^
    kind_to_string (get_kind td.arguments) ^ " where\n  " ^
    ctors_str

and ctor_to_string (ctor: ty_xtor) : string =
  let quant_str = 
    if ctor.quantified = [] then ""
    else
      let s =
        ctor.quantified
        |> List.map (fun (x, k) -> Ident.name x ^ ": " ^ kind_to_string k)
        |> String.concat ", "
      in "{" ^ s ^ "}"
  in
  let producers_str =
    "(" ^ String.concat ", " (List.map (typ_to_string true) ctor.producers) ^ ")"
  in
  let consumers_str =
    "(" ^ String.concat ", " (List.map (typ_to_string true) ctor.consumers) ^ ")"
  in
  let result_str =
    if ctor.arguments = [] then
      Path.name ctor.parent
    else
      Path.name ctor.parent ^
      (ctor.arguments
      |> List.map (fun arg -> "(" ^ typ_to_string true arg ^ ")")
      |> String.concat "")
  in
  (* display constraints as a separate list *)
  let constraints_str = match ctor.constraints with
    | None | Some [] -> ""
    | Some constraints ->
      let bindings = List.map (fun (x, ty) ->
        Ident.name x ^ " = " ^ typ_to_string true ty
      ) constraints in
      "[" ^ String.concat ", " bindings ^ "]"
  in
  Path.name ctor.symbol ^ ": " ^
  quant_str ^ " " ^
  producers_str ^ " |- " ^
  result_str ^ " || " ^
  consumers_str ^ " " ^
  constraints_str

and code_to_string (nested: bool) (td: ty_dec) : string =
  if nested then
    let args_str =
      td.arguments
      |> List.take_while (fun (t_opt, _) -> Option.is_some t_opt)
      |> List.map (fun (t_opt, _) ->
        match t_opt with
        | Some t -> "(" ^ typ_to_string true t ^ ")"
        | None -> failwith "impossible!")
      |> String.concat "" 
    in
    Path.name td.symbol ^ args_str
  else
    let arg_to_string ((t_opt, _): typ option * kind) : string =
      match t_opt with
      | Some t -> "(" ^ typ_to_string true t ^ ")"
      | None -> ""
    in
    let args_str =
      String.concat "" (List.map arg_to_string td.arguments)
    in
    let dtors_str =
      String.concat "\n  " (List.map dtor_to_string td.xtors)
    in
    "code " ^ Path.name td.symbol ^ args_str ^ ": " ^
    kind_to_string (get_kind td.arguments) ^  " where\n  " ^
    dtors_str

and dtor_to_string (dtor: ty_xtor) : string =
  let quant_str = 
    if dtor.quantified = [] then ""
    else
      let s =
        dtor.quantified
        |> List.map (fun (x, k) -> Ident.name x ^ ": " ^ kind_to_string k)
        |> String.concat ", "
      in "{" ^ s ^ "}"
  in
  let producers_str =
    "(" ^ String.concat ", " (List.map (typ_to_string true) dtor.producers) ^ ")"
  in
  let consumers_str =
    "(" ^ String.concat ", " (List.map (typ_to_string true) dtor.consumers) ^ ")"
  in
  let main_str =
    if dtor.arguments = [] then
      Path.name dtor.parent
    else
      Path.name dtor.parent ^
      (dtor.arguments
      |> List.map (fun arg -> "(" ^ typ_to_string true arg ^ ")")
      |> String.concat "")
  in
  (* display constraints as a separate list *)
  let constraints_str = match dtor.constraints with
    | None | Some [] -> ""
    | Some constraints ->
      let bindings = List.map (fun (x, ty) ->
        Ident.name x ^ " = " ^ typ_to_string true ty
      ) constraints in
      "[" ^ String.concat ", " bindings ^ "]"
  in
  Path.name dtor.symbol ^ ": " ^
  quant_str ^ " " ^
  producers_str ^ " || " ^
  main_str ^ " |- " ^
  consumers_str ^ " " ^
  constraints_str

(* Kind inference and checking *)

let rec infer_kind (defs: ty_defs) (ctx: kind Ident.tbl) (t: typ) =
  match t with
  | TySym s -> let _, k = get_def defs s in k
  | TyVar x ->
    (match Ident.find_opt x ctx with
    | Some k -> k
    | None -> failwith ("unbound type variable " ^ Ident.name x))
  | TyApp (t1, t2) ->
    (match infer_kind defs ctx t1 with
    | KArrow (k_arg, k_res) -> check_kind defs ctx t2 k_arg; k_res
    | _ -> failwith "expected a type constructor in type application")
  (*
  | TyFun (t1, t2) ->
    check_kind defs ctx t1 KStar;
    check_kind defs ctx t2 KStar;
    KStar
  | TyAll ((x, k), t) ->
    let ctx' = Ident.add x k ctx in
    check_kind defs ctx' t KStar;
    KStar
  *)
  | TyDef (Prim (_, k)) -> k
  | TyDef (Code td) | TyDef (Data td) ->
    (* verify all constructors are well-formed *)
    let arg_kinds = List.map snd td.arguments in
    List.iter (fun ctor ->
      let ctx' = List.fold_left (fun acc (x, k) ->
        Ident.add x k acc
      ) ctx ctor.quantified
      in
      List.iter2 (check_kind defs ctx') ctor.arguments arg_kinds
    ) td.xtors;
    let rec build_kind ks =
      match ks with
      | [] -> KStar
      | k :: ks -> KArrow (k, build_kind ks)
    in
    build_kind arg_kinds

and check_kind (defs: ty_defs) (ctx: kind Ident.tbl) (t: typ) (expected: kind) =
  let inferred = infer_kind defs ctx t in
  if inferred <> expected then failwith "kind mismatch"

let add_def (defs: ty_defs) (def: ty_def) =
  match def with
  | Prim (sym, k) -> (sym, (def, k)) :: defs
  | Data td | Code td ->
    let k = infer_kind defs Ident.emptytbl (TyDef def) in
    (td.symbol, (def, k)) :: defs

(* substitution: replace type variables with their definitions *)
let rec subst (env: typ Ident.tbl) (t: typ) : typ =
  match t with
  | TySym _ -> t
  | TyVar x ->
    (match Ident.find_opt x env with
    | Some t' -> t'
    | None -> t)
  | TyApp (t1, t2) -> TyApp (subst env t1, subst env t2)
  (*
  | TyFun (t1, t2) -> TyFun (subst env t1, subst env t2)
  | TyAll ((x, k), t) ->
    (* remove x from env to avoid capture *)
    let env' = Ident.filter (fun y _ -> not (Ident.equal x y)) env in
    TyAll ((x, k), subst env' t)
  *)
  | TyDef (Prim _) -> t
  | TyDef (Data td) -> TyDef (Data (subst_dec env td))
  | TyDef (Code td) -> TyDef (Code (subst_dec env td))

and subst_dec (env: typ Ident.tbl) (td: ty_dec) : ty_dec =
  { td with
    arguments = List.map (fun (t_opt, k) ->
      (Option.map (subst env) t_opt, k)) td.arguments
  ; xtors = List.map (subst_xtor env) td.xtors
  }

and subst_xtor (env: typ Ident.tbl) (xtor: ty_xtor) : ty_xtor =
  (* filter out quantified variables from the environment *)
  let env' = Ident.filter (fun x _ ->
    not (List.exists (fun (y, _) -> Ident.equal x y) xtor.quantified)
  ) env in
  { xtor with
    producers = List.map (subst env') xtor.producers
  ; consumers = List.map (subst env') xtor.consumers
  ; arguments = List.map (subst env') xtor.arguments
  }

(* weak head normal form *)
let rec whnf (seen: Path.t list) (defs: ty_defs) (ty: typ) =
  let result = 
    match ty with
  | TyApp (f, a) ->
    (match whnf seen defs f with
    | seen, TyDef (Data td) -> seen, TyDef (Data (inst1 seen defs td a))
    | seen, TyDef (Code td) -> seen, TyDef (Code (inst1 seen defs td a))
    | seen, TyDef (Prim (sym, _kind)) ->
      (* Primitive types - look them up in definitions *)
      if List.exists (Path.equal sym) seen then
        seen, ty
      else
        let seen' = sym :: seen in
        (match List.assoc_opt sym defs with
        | Some (Code td, _) -> seen', TyDef (Code (inst1 seen' defs td a))
        | Some (Data td, _) -> seen', TyDef (Data (inst1 seen' defs td a))
        | Some (Prim _, _) -> seen', ty
        | None -> seen', ty)
    | seen, f' when f' == f -> seen, ty (* optimization *)
    | seen, f' -> seen, TyApp (f', a))
  | TySym s ->
    if List.exists (Path.equal s) seen then
      seen, ty (* prevent infinite loops *)
    else
      let seen' = s :: seen in
      let def, _ = get_def defs s in
      seen', TyDef def
  (*
  | TyAll ((x, k), t) ->
    let seen', t' = whnf seen defs t in
    seen', TyAll ((x, k), t')
  *)
  | _ -> seen, ty
  in
  result

and reduce (defs: ty_defs) (ty: typ) : typ =
  snd (whnf [] defs ty)

and reduce_seen (seen: Path.t list) (defs: ty_defs) (ty: typ) : typ =
  snd (whnf seen defs ty)

and inst1 (seen: Path.t list) (defs: ty_defs) (td: ty_dec) (arg: typ) : ty_dec =
  let rec apply seen left arg =
    match left with
    | [] -> failwith "no argument to instantiate"
    | (None, k) :: rest -> seen @ (Some arg, k) :: rest
    | arg' :: rest -> apply (seen @ [arg']) rest arg
  in
  let td = { td with arguments = apply [] td.arguments arg }
  in
  let result (xtor: ty_xtor) =
    (* build the result type using constructor's type arguments *)
    let instantiated_args =
      List.map2 (fun result_arg (_, k) -> (Some result_arg, k))
        xtor.arguments td.arguments
    in
    { td with arguments = instantiated_args }
  in
  let xtor_match xtor =
    match unify_tdec seen defs td (result xtor) with
    | None -> None
    | Some sub ->
      (* extract constraints for quantified variables *)
      let constraints_for_orig = 
        List.filter_map (fun (x, _k) ->
          match Ident.find_opt x sub with
          | Some ty -> Some (x, ty)
          | None -> None
        ) xtor.quantified
      in
      let combined_constraints = 
        match xtor.constraints with
        | None -> Some constraints_for_orig
        | Some prev -> Some (prev @ constraints_for_orig)
      in
      Some { xtor with constraints = combined_constraints }
  in
  { td with xtors = List.filter_map xtor_match td.xtors }

and unify_tdec (seen: Path.t list) (defs: ty_defs) (td1: ty_dec) (td2: ty_dec) : (typ Ident.tbl) option =
  let rec unify_args args1 args2 sub =
    match args1, args2 with
    | [], [] -> Some sub
    | (Some t1, _) :: rest1, (Some t2, _) :: rest2 ->
      let t1' = subst sub t1 in
      let t2' = subst sub t2 in
      (match unify seen defs t1' t2' with
      | None -> None
      | Some sub' -> unify_args rest1 rest2 (Ident.join sub' sub))
    | (None, _) :: rest1, (None, _) :: rest2 ->
      unify_args rest1 rest2 sub
    (* allow instantiated to unify with uninstantiated (for partial application) *)
    | (Some _, _) :: rest1, (None, _) :: rest2
    | (None, _) :: rest1, (Some _, _) :: rest2 ->
      unify_args rest1 rest2 sub
    | _ -> None
  in
  unify_args td1.arguments td2.arguments Ident.emptytbl

(* unification: returns Some substitution if types unify, None otherwise *)

and unify (seen: Path.t list) (defs: ty_defs) (t1: typ) (t2: typ) : (typ Ident.tbl) option =
  let res = ref None in
  begin
    (match t1, t2 with
    | TySym s, TySym s' ->
      if Path.equal s s' then res := Some Ident.emptytbl
    | TyVar x, TyVar y when Ident.equal x y ->
      res := Some Ident.emptytbl
    | TyVar x, t | t, TyVar x ->
      (* occurs check: don't allow x = ... x ... *)
      if not (occurs x t) then res := Some (Ident.add x t Ident.emptytbl)
    | TyApp (f1, a1), TyApp (f2, a2) ->
      (match unify seen defs f1 f2 with
      | None -> ()
      | Some sub1 ->
        (match unify seen defs (subst sub1 a1) (subst sub1 a2) with
        | None -> ()
        | Some sub2 -> res := Some (Ident.join sub2 sub1)))
    (*
    | TyFun (a1, b1), TyFun (a2, b2) ->
      (match unify seen defs a1 a2 with
      | None -> ()
      | Some sub1 ->
        (match unify seen defs (subst sub1 b1) (subst sub1 b2) with
        | None -> ()
        | Some sub2 ->  res := Some (Ident.join sub2 sub1)))
    | TyAll ((x1, k1), t1), TyAll ((x2, k2), t2) when k1 = k2 ->
      (* unify bodies after renaming x2 to x1 *)
      let sub_x2_to_x1 = Ident.add x2 (TyVar x1) Ident.emptytbl in
      let t2' = subst sub_x2_to_x1 t2 in
      (match unify seen defs t1 t2' with
      | None -> ()
      | Some sub ->
        (* remove x1 from result substitution as it's bound *)
        res := Some (Ident.filter (fun y _ -> not (Ident.equal x1 y)) sub))
    *)
    | TyDef (Data td1), TyDef (Data td2)
    | TyDef (Code td1), TyDef (Code td2) when Path.equal td1.symbol td2.symbol ->
      res := unify_tdec seen defs td1 td2
    | TyDef (Prim (s1, _)), TyDef (Prim (s2, _)) when Path.equal s1 s2 ->
      res := Some Ident.emptytbl
    (* allow type symbols to unify with primitives *)
    | TySym s, TyDef (Prim (s', _))
    | TyDef (Prim (s', _)), TySym s when Path.equal s s' ->
      res := Some Ident.emptytbl
    | _ -> ());

    if Option.is_none !res then
      let t1' = reduce_seen seen defs t1 in
      if not (t1' == t1) then
        res := unify seen defs t1' t2
      else
        let t2' = reduce_seen seen defs t2 in
        if not (t2' == t2) then
          res := unify seen defs t1 t2'
  end;
  !res

and occurs (x: Ident.t) (t: typ) : bool =
  match t with
  | TySym _ -> false
  | TyVar y -> Ident.equal x y
  | TyApp (t1, t2) -> occurs x t1 || occurs x t2
  (*
  | TyFun (t1, t2) -> occurs x t1 || occurs x t2
  | TyAll ((y, _), t) ->
    (* x occurs in TyAll if it occurs free in the body *)
    if Ident.equal x y then false else occurs x t
  *)
  | TyDef (Prim _) -> false
  | TyDef (Data td) | TyDef (Code td) ->
    List.exists (fun (t_opt, _) ->
      match t_opt with
      | Some t -> occurs x t
      | None -> false
    ) td.arguments

let equivalent (defs: ty_defs) (t1: typ) (t2: typ) : bool =
  match unify [] defs t1 t2 with
  | Some subs -> Ident.is_empty subs
  | None -> false

let norm (defs: ty_defs) (ty: typ) : typ =
  let rec go (seen: Path.t list) (t: typ) : typ =
    match whnf seen defs t with
    | _, (TyVar _ as v) -> v
    | _, (TySym _ as s) -> s
    (*
    | _, TyFun (t1, t2) -> TyFun (go seen t1, go seen t2)
    | _, TyAll ((x, k), t) -> TyAll ((x, k), go seen t)
    *)
    | _, (TyDef (Prim _) as p) -> p
    | seen, TyApp (t1, t2) -> TyApp (go seen t1, go seen t2)
    | seen, TyDef (Data td) -> TyDef (Data (go_dec seen td))
    | seen, TyDef (Code td) -> TyDef (Code (go_dec seen td))
  and go_dec (seen: Path.t list) (td: ty_dec) =
    let seen' = td.symbol :: seen in
    let normalized_ctors = List.map (fun xtor ->
      { xtor with
        producers = List.map (go seen') xtor.producers
      ; consumers = List.map (go seen') xtor.consumers
      ; arguments = List.map (go seen') xtor.arguments
      }) td.xtors
    in { td with xtors = normalized_ctors }
  in
  go [] ty


module Type = struct
  type t = typ
  let to_string = typ_to_string false
  let infer = infer_kind
  let check = check_kind
  let subst = subst
  let reduce = reduce
  let unify = unify
  let equivalent = equivalent
  let norm = norm
end

module Kind = struct
  type t = kind
  let to_string = kind_to_string
end


(*
{X: k} T

if T has kind k' in the context extended with X: k,
then the whole expression has kind k -> k'
code All_k[T] where
{ instantiate: {X: k} All_k[T] -> T
  }
*)