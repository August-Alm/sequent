(**
  Inspired by Leroy's modular module system.
*)


module Ident = struct
  type t = {name: string; stamp: int}
  let currstamp = ref 0
  let mk s =
    if String.contains s '.' then
      failwith "identifiers can not contain dots";
    currstamp := !currstamp + 1;
    {name = s; stamp = !currstamp}
  
  let fresh () =
    currstamp := !currstamp + 1;
    {name = "u$" ^ string_of_int !currstamp; stamp = !currstamp}

  let mk_primitive n x =
    {name = x; stamp = -n}

  let name id = id.name
  let stamp id = id.stamp
  let equal id1 id2 = (id1.stamp = id2.stamp)
  let compare id1 id2 =
    let k = String.compare id1.name id2.name in
    if k <> 0 then k else Int.compare id1.stamp id2.stamp

  type 'a tbl = (t * 'a) list
  let emptytbl = []
  let is_empty tbl = (tbl = [])
  let add id data tbl = (id, data) :: tbl
  let rec find x tb =
    match tb with
    | [] -> raise Not_found
    | (y, v) :: rest -> if equal x y then v else find x rest
  let rec find_opt x tb =
    match tb with
    | [] -> None
    | (y, v) :: rest -> if equal x y then Some v else find_opt x rest
  let filter f tbl = List.filter (fun (k, v) -> f k v) tbl
  let join tbl1 tbl2 = tbl1 @ tbl2
  let of_list lst = lst
  let to_list lst = lst
  let contains_key x tbl = List.exists (fun (k, _) -> equal x k) tbl
end

module Path = struct
  type t =
    | Pident of Ident.t     (* identifier *)
    | Pdot of t * string    (* access to a module component *)
  
  module Id = Ident

  let of_ident id = Pident id
  let of_primitive n x = Pident (Ident.mk_primitive n x)

  let stamp_unsafe = function
    | Pident id -> Ident.stamp id
    | Pdot (_, _) -> failwith "stamp_unsafe: not an ident"

  let of_string s =
    let ss = String.split_on_char '.' s in
    match ss with
    | [] -> failwith "impossible"
    | s :: ss ->
      List.fold_left (fun p s -> Pdot (p, s)) (Pident (Ident.mk s)) ss

  let as_ident = function Pident i -> Some i | _ -> None
  let access p field = Pdot (p, field)

  let rec equal p1 p2 =
    match (p1, p2) with
    | (Pident id1, Pident id2) -> Ident.equal id1 id2
    | (Pdot (r1, f1), Pdot (r2, f2)) -> equal r1 r2 && f1 = f2
    | (_, _) -> false
  
  let rec compare p1 p2 =
    match (p1, p2) with
    | (Pident id1, Pident id2) -> Ident.compare id1 id2
    | (Pident _, Pdot _) -> -1
    | (Pdot _, Pident _) -> 1
    | (Pdot (r1, f1), Pdot (r2, f2)) ->
      let k = compare r1 r2 in
      if k <> 0 then k else String.compare f1 f2
  
  let rec is_rooted_at id p =
    match p with
    | Pident id' -> Ident.equal id id'
    | Pdot (root, _) -> is_rooted_at id root
  
  let rec name p =
    match p with
    | Pident id -> Ident.name id
    | Pdot (p, field) -> (name p) ^ "." ^ field

  type 'a tbl = (t * 'a) list
  let emptytbl = []
  let is_empty tbl = (tbl = [])
  let add id data tbl = (id, data) :: tbl
  let rec find x tb =
    match tb with
    | [] -> raise Not_found
    | (y, v) :: rest -> if equal x y then v else find x rest
  let rec find_opt x tb =
    match tb with
    | [] -> None
    | (y, v) :: rest -> if equal x y then Some v else find_opt x rest
  let filter f tbl = List.filter (fun (k, v) -> f k v) tbl
  let join tbl1 tbl2 = tbl1 @ tbl2
  let of_list lst = lst
  let to_list lst = lst
  let contains_key x tbl = List.exists (fun (k, _) -> equal x k) tbl

  type subst = t Ident.tbl

  let rec path p sub =
    match p with
    | Pident id -> (try Ident.find id sub with Not_found -> p)
    | Pdot (root, field) -> Pdot (path root sub, field)
  
  let add_subst = Ident.add
  let find_subst = Ident.find
  let none = Ident.emptytbl
end
