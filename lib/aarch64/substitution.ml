(**
  module: Aarch64.Substitution
  description: Substitution encoding helpers.
*)

open Code

module Tree = struct

  type t = Back | Node of Register.t * (t list)

  type root = Start of Register.t * (t list)

  let rec nodes = function
      Back -> [] | Node (x, ts) -> x :: List.concat_map nodes ts

  let rec refers_back = function
      Back -> true | Node (_, ts) -> List.exists refers_back ts

  let visited_by (Start (x, ts)) =
    if List.exists refers_back ts
    then x :: List.concat_map nodes ts
    else List.concat_map nodes ts
  
  let delete_targets visited graph =
    List.map (
      List.filter (fun y -> List.for_all (fun x -> not (Register.equal x y)) visited)
    ) graph

  let delete_all x ys = List.filter (fun y -> not (Register.equal x y)) ys

  let get_nth graph nd = List.nth graph (Register.to_int nd)

  let rec spanning_tree graph r nd =
    if r = nd then Back
    else Node (nd, List.map (spanning_tree graph r) (get_nth graph nd))
  
  let rec spanning_forest graph xs =
    match xs with
      [] -> []
    | x :: xs ->
        let ts = List.map (spanning_tree graph x) (delete_all x (get_nth graph x)) in
        let r = Start (x, ts) in
        r :: spanning_forest (delete_targets (visited_by r) graph) xs
  
  let rec tree_moves x = function
      Back -> MOVR (Register.temp, x) :: []
    | Node (y, ts) -> MOVR (y, x) :: List.concat_map (tree_moves y) ts

  let root_moves (Start (x, xs)) =
    if List.exists refers_back xs
    then List.rev (MOVR (x, Register.temp) :: List.concat_map (tree_moves x) xs)
    else List.rev (List.concat_map (tree_moves x) xs)
end

let code_exhange (graph: Register.t list list) : code list =
  List.concat_map Tree.root_moves (Tree.spanning_forest graph Register.range)