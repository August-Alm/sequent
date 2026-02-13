let (<<) f g x = f (g x)

let (>>) f g x = g (f x)

let (||>) (x, y) f = f x y

module StringMap = Map.Make(String)

(* List utilities *)

(* Take first n elements from a list *)
let rec take n lst =
  if n <= 0 then []
  else match lst with
    [] -> []
  | x :: xs -> x :: take (n - 1) xs

(* Drop first n elements from a list *)
let rec drop n lst =
  if n <= 0 then lst
  else match lst with
    [] -> []
  | _ :: xs -> drop (n - 1) xs

let split_at_last lst =
  match List.rev lst with
    [] -> failwith "split_at_last: empty list"
  | last :: rev_init -> (List.rev rev_init, last)


let ( let* ) o f =
  match o with
  | Error e -> Error e
  | Ok x -> f x
