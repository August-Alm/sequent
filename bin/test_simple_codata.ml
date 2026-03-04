(* Minimal test: codata with captured context *)
let source = {|
data result: type where
  { ok: int -> result }

let apply_id(f: {a} a -> a)(x: int): int = f{int}(x)

let id{a}(y: a): a = y

let main: int = apply_id(id)(42)
|}

let () =
  match Pipeline.run_pipeline_with_result source with
  | Ok result -> Printf.printf "Result: %d (expected: 42)\n" result
  | Error msg -> Printf.printf "Error: %s\n" msg
