(**
  Test suite for the full compilation pipeline.
  
  This test file:
  1. Parses surface syntax strings using Lang.Parse
  2. Desugars to Melcore using Desugar
  3. Type-checks in Melcore using Melcore.Terms
  4. Encodes to Core using Encode
  5. Type-checks in Core using Core.Terms
  6. Runs Monomorphize to generate monomorphic definitions
  7. Focuses to Focused IR
  8. Type-checks in Focused using Focused.Terms
  9. Linearizes to Axil using Linearize
  10. Type-checks in Axil using Axil.Terms
  11. Compiles to Aarch64 assembly
  12. Evaluates using the Aarch64 abstract machine
  
  All test inputs contain a monomorphic "main" function that returns an int.
*)

open Common.Identifiers

module Pipe = Sequent.Pipeline
module MPrint = Melcore.Printing
module CPrint = Core.Printing
module FPrint = Focused.Printing
module APrint = Axil.Printing
module FTerms = Focused.Terms
module ATerms = Axil.Terms
module ACode = Aarch64.Code

(* Test harness *)
let test_count = ref 0
let pass_count = ref 0

(* ========================================================================= *)
(* Test Runner                                                               *)
(* ========================================================================= *)

let ( let* ) = Result.bind

let run_test ?(trace=false) ~name ~expected (source: string) =
  incr test_count;
  print_endline "════════════════════════════════════════════════════════════════";
  Printf.printf "Test %d: %s\n" !test_count name;
  print_endline "────────────────────────────────────────────────────────────────";
  
  print_endline "Source:";
  Printf.printf "%s\n\n" source;
  
  let result =
    (* Stage 1: Parse and desugar *)
    let* (decs, defs) = Pipe.LangStage.to_melcore source in
    print_endline "1. Parse + Desugar: OK";
    
    (* Stage 2: Melcore type-check *)
    let* (decs, typed_defs) = Pipe.MelcoreStage.type_check decs defs in
    print_endline "2. Melcore type-check: OK";
    
    (* Stage 3: Normalize *)
    let norm_defs = Pipe.MelcoreStage.normalize typed_defs in
    print_endline "3. Normalize: OK";
    (* Debug: print normalized Melcore for main *)
    (match Path.find_opt (Path.of_string "main") norm_defs with
      Some main_def -> 
        Printf.printf "   Normalized main body: %s\n" (MPrint.typed_term_to_string main_def.Melcore.Terms.body)
    | None -> ());
    
    (* Stage 4: Encode to Core *)
    let* (types_ctx, core_defs) = Pipe.MelcoreStage.encode decs norm_defs in
    print_endline "4. Encode to Core: OK";
    (* Debug: print Core defs *)
    Path.to_list core_defs |> List.iter (fun (p, (def: Core.Terms.definition)) ->
      Printf.printf "   %s: %s\n" (Path.name p) (Core.Printing.command_to_string def.body)
    );
    
    (* Stage 5: Core type-check *)
    let* (types_ctx, core_defs) = Pipe.CoreStage.type_check types_ctx core_defs in
    print_endline "5. Core type-check: OK";
    
    (* Stage 6: Monomorphize *)
    let* mono_result = Pipe.CoreStage.monomorphize types_ctx core_defs in
    print_endline "6. Monomorphize: OK";
    Printf.printf "   Generated %d new declarations, %d definitions\n"
      (List.length mono_result.new_declarations)
      (List.length mono_result.definitions);
    (* Debug: print new declarations *)
    List.iter (fun dec ->
      Printf.printf "   New dec: %s\n" (Core.Printing.dec_to_string dec)
    ) mono_result.new_declarations;
    (* Debug: print mono main term_params *)
    Printf.printf "   Mono main term_params: [%s]\n"
      (String.concat "; " (List.map (fun (v, _ct) -> Ident.name v) mono_result.main.term_params));
    (* Debug: print mono main *)
    Printf.printf "   Mono main: %s\n" (Core.Printing.command_to_string mono_result.main.body);
    (* Debug: print mono definitions *)
    List.iter (fun (def: Core.Terms.definition) ->
      Printf.printf "   Mono %s: %s\n" (Path.name def.path) (Core.Printing.command_to_string def.body)
    ) mono_result.definitions;
    
    (* Stage 7: Focus *)
    let* (focused_decs, focused_main, focused_defs) = 
      Pipe.CoreStage.focus types_ctx mono_result in
    print_endline "7. Focus: OK";
    
    (* Print focused main *)
    print_endline "\nFocused main (before reduce):";
    Printf.printf "%s\n\n" (FPrint.command_to_string focused_main.body);

    (* Print focused defs for debugging *)
    let def_list = Path.to_list focused_defs in
    if List.length def_list > 0 then begin
      print_endline "Focused definitions (before reduce):";
      List.iter (fun (_, (def: FTerms.definition)) ->
        Printf.printf "  %s:\n%s\n\n" (Path.name def.path) (FPrint.command_to_string def.body)
      ) def_list
    end;

    (* Stage 7b: Reduce - inline single-use continuations *)
    let (reduced_main, reduced_defs) = 
      Pipe.FocusedStage.reduce focused_main focused_defs in
    print_endline "7b. Reduce: OK";

    (* Print reduced main *)
    print_endline "\nFocused main (after reduce):";
    Printf.printf "%s\n\n" (FPrint.command_to_string reduced_main.body);

    (* Print reduced defs for debugging *)
    let reduced_def_list = Path.to_list reduced_defs in
    if List.length reduced_def_list > 0 then begin
      print_endline "Focused definitions (after reduce):";
      List.iter (fun (_, (def: FTerms.definition)) ->
        Printf.printf "  %s:\n%s\n\n" (Path.name def.path) (FPrint.command_to_string def.body)
      ) reduced_def_list
    end;
    
    let* _ = Pipe.FocusedStage.type_check focused_decs reduced_defs in
    print_endline "8. Focused type-check: OK";
    
    (* Stage 9: Linearize to Axil *)
    let* (axil_decs, axil_main, axil_defs) = 
      Pipe.AxilStage.linearize focused_decs reduced_main reduced_defs in
    print_endline "9. Linearize to Axil: OK";
    
    (* Print axil main *)
    print_endline "\nAxil main:";
    Printf.printf "%s\n\n" (APrint.command_to_string axil_main.body);

    (* Print axil defs for debugging *)
    let axil_def_list = Path.to_list axil_defs in
    if List.length axil_def_list > 0 then begin
      print_endline "Axil definitions:";
      List.iter (fun (_, (def: ATerms.definition)) ->
        Printf.printf "  %s:\n%s\n\n" (Path.name def.path) (APrint.command_to_string def.body)
      ) axil_def_list
    end;
    
    let* _ = Pipe.AxilStage.type_check axil_decs axil_defs in
    print_endline "10. Axil type-check: OK";
    
    (* Stage 11: Compile to Aarch64 *)
    let* (asm_code, _arg_count) = 
      Pipe.EmitStage.compile Pipe.EmitStage.AARCH64 axil_main axil_defs in
    print_endline "11. Compile to Aarch64: OK";
    
    (* Print generated Aarch64 code *)
    print_endline "\nAarch64 code:";
    Printf.printf "%s\n\n" (ACode.Code.emit_all asm_code);
    
    (* Stage 12: Evaluate using Aarch64 semantics *)
    let* result = Pipe.EmitStage.eval ~trace ~max_steps:50000 asm_code in
    print_endline "12. Aarch64 eval: OK";
    
    Ok result
  in
  
  print_newline ();
  (match result with
    Ok actual ->
      Printf.printf "Result: %d\n" actual;
      if actual = expected then begin
        Printf.printf "PASS ✓ (expected %d)\n" expected;
        incr pass_count
      end else
        Printf.printf "FAIL ✗ (expected %d, got %d)\n" expected actual;
      
  | Error msg -> Printf.printf "FAIL ✗: %s\n" msg);
  print_newline ()

(* ========================================================================= *)
(* Test Cases                                                                *)
(* ========================================================================= *)

let () =
  print_endline "\n╔══════════════════════════════════════════════════════════════╗";
  print_endline "║              FULL PIPELINE TEST SUITE                        ║";
  print_endline "╚══════════════════════════════════════════════════════════════╝\n";

  (* Test 1: Simple literal return *)
  run_test
    ~name:"Simple literal return"
    ~expected:42
    {|
let main: int = 42
    |};

  (* Test 2: Simple arithmetic *)
  run_test
    ~name:"Simple addition"
    ~expected:7
    {|
let main: int = 3 + 4
    |};

  (* Test 3: Nested arithmetic *)
  run_test
    ~name:"Nested arithmetic"
    ~expected:10
    {|
let main: int = (2 + 3) + (1 + 4)
    |};

  (* Test 4: Subtraction *)
  run_test
    ~name:"Subtraction"
    ~expected:5
    {|
let main: int = 10 - 5
    |};

  (* Test 5: Mixed arithmetic *)
  run_test
    ~name:"Mixed arithmetic"
    ~expected:8
    {|
let main: int = (10 + 5) - 7
    |};

  (* Test 6: Ifz - zero case *)
  run_test
    ~name:"Ifz zero case"
    ~expected:1
    {|
let main: int = ifz(0) then 1 else 2
    |};

  (* Test 7: Ifz - nonzero case *)
  run_test
    ~name:"Ifz nonzero case"
    ~expected:2
    {|
let main: int = ifz(5) then 1 else 2
    |};

  (* Test 8: Let binding *)
  run_test
    ~name:"Let binding"
    ~expected:10
    {|
let main: int =
  let x = 4 in
  let y = 6 in
  x + y
    |};

  (* Test 9: Function application *)
  run_test
    ~name:"Function application"
    ~expected:15
    {|
let double(x: int): int = x + x

let main: int = double(7) + 1
    |};

  (* Test 10: Recursive function - simple countdown *)
  run_test
    ~name:"Recursive countdown"
    ~expected:0
    {|
let countdown(n: int): int =
  ifz(n) then 0 else countdown(n - 1)

let main: int = countdown(5)
    |};

  (* Test 11: Recursive sum *)
  run_test
    ~name:"Recursive sum"
    ~expected:15
    {|
let sum(n: int): int =
  ifz(n) then 0 else n + sum(n - 1)

let main: int = sum(5)
    |};

  (* Test 12: Simple data type - bool *)
  run_test
    ~name:"Bool data type"
    ~expected:1
    {|
data bool: type where
  { true: bool
  ; false: bool
  }

let bool_to_int(b: bool): int =
  match b with
  { true => 1
  ; false => 0
  }

let main: int = bool_to_int(true)
    |};

  (* Test 13: Bool negation *)
  run_test
    ~name:"Bool negation"
    ~expected:0
    {|
data bool: type where
  { true: bool
  ; false: bool
  }

let not(b: bool): bool =
  match b with
  { true => false
  ; false => true
  }

let bool_to_int(b: bool): int =
  match b with
  { true => 1
  ; false => 0
  }

let main: int = bool_to_int(not(true))
    |};

  (* Test 14: Option type - none case *)
  run_test
    ~name:"Option none"
    ~expected:0
    {|
data option: type -> type where
  { none: {a: type} option(a)
  ; some: {a: type} a -> option(a)
  }

let get_or_zero(opt: option(int)): int =
  match opt with
  { none{_} => 0
  ; some{_}(x) => x
  }

let main: int = get_or_zero(none{int})
    |};

  (* Test 15: Option type - some case *)
  run_test
    ~name:"Option some"
    ~expected:42
    {|
data option: type -> type where
  { none: {a: type} option(a)
  ; some: {a: type} a -> option(a)
  }

let get_or_zero(opt: option(int)): int =
  match opt with
  { none{_} => 0
  ; some{_}(x) => x
  }

let main: int = get_or_zero(some{int}(42))
    |};

  (* Test 16: Pair type *)
  run_test
    ~name:"Pair type"
    ~expected:6
    {|
data pair: type -> type -> type where
  { mk_pair: {a}{b} a -> b -> pair(a)(b)
  }

let fst{a}{b}(p: pair(a)(b)): a =
  match p with
  { mk_pair{_}{_}(x)(y) => x
  }

let snd{a}{b}(p: pair(a)(b)): b =
  match p with
  { mk_pair{_}{_}(x)(y) => y
  }

let main: int =
  let p = mk_pair{int}{int}(1)(2) in
  let q = mk_pair{int}{int}(3)(5) in
  fst{int}{int}(p) + snd{int}{int}(q)
    |};
  
  (* Test 17: Fibonacci *)
  run_test
    ~name:"Fibonacci"
    ~expected:5
    {|
let fib(n: int): int =
  ifz(n) then 0 else ifz(n - 1) then 1
  else fib(n - 1) + fib(n - 2)

let main: int = fib(5)
    |};


  (* Test 18: Optimized closures *)
  run_test
    ~name:"Optimized closures"
    ~expected:42
    {|
let main: int =
  let a = 41 in
  let f = fun(x: int) => x + 1 in
  f(a)
    |};

  (* Test 19: Higher rank polymorphism *)
  run_test
    ~name:"Higher-rank polymorphism"
    ~expected:5
    {|
data tuple: type -> type -> type where
  { mk_tuple: {a}{b} a -> b -> tuple(a)(b)
  }

data enum: type where
  { A: enum
  ; B: enum
  }

let map_mk_tuple{a}{b}(f: {c} c -> c)(x: a)(y: b): tuple(a)(b) =
  mk_tuple{a}{b}(f{a}(x))(f{b}(y))

let id{a}(x: a): a = x

let main: int =
  let t = map_mk_tuple{int}{enum}(id)(5)(B) in
  match t with
  { mk_tuple{_}{_}(x)(y) =>
      match y with
      { A => 0
      ; B => x
      }
  }
    |};

  (* Test 20: Higher rank polymorphism with anonymous *)
  run_test
    ~name:"Higher-rank polymorphism with anonymous"
    ~expected:5
    {|
data tuple: type -> type -> type where
  { mk_tuple: {a}{b} a -> b -> tuple(a)(b)
  }

data enum: type where
  { A: enum
  ; B: enum
  }

let map_mk_tuple{a}{b}(f: {c} c -> c)(x: a)(y: b): tuple(a)(b) =
  mk_tuple{a}{b}(f{a}(x))(f{b}(y))

let main: int =
  let f = fun{c}(z: c) => z in
  let t = map_mk_tuple{int}{enum}(f)(5)(B) in
  match t with
  { mk_tuple{_}{_}(x)(y) =>
      match y with
      { A => 0
      ; B => x
      }
  }
    |};

  (* Test 21: Complex types *)
  run_test
    ~name:"Complex types with multiple features"
    ~expected:10
    {|
data option: type -> type where
  { none: {a} option(a)
  ; some: {a} a -> option(a)
  }

code stream: type -> type where
  { state: {a} stream(a) -> a
  ; next: {a} stream(a) -> option(stream(a))
  }

code algebra: type -> type -> type where
  { nil: {b}{c} algebra(b)(c) -> c
  ; cons: {b}{c} algebra(b)(c) -> b -> c -> c
  }

code foldable: type -> type where
  { fold: {d}{r} foldable(d) -> algebra(d)(r) -> r
  }

let ints_from(i: int): stream(int) =
  new { state => i
      ; next => some{stream(int)}(ints_from(i + 1))
      }

let nats: stream(int) = ints_from(0)

let take{e}(s: stream(e))(n: int): foldable(e) =
  new foldable(e)
  { fold{e}{t}(alg) =>
      ifz(n) then
        nil{e}{t}(alg)
      else
        match next{e}(s) with
        { none{_} => nil{e}{t}(alg)
        ; some{_}(s') =>
            let rest = take{e}(s')(n - 1) in
            let folded_rest = fold{e}{t}(rest)(alg) in
            cons{e}{t}(alg)(state{e}(s))(folded_rest)
        }
  }

let sum(l: foldable(int)): int =
  let alg =
    new algebra(int)(int)
    { nil => 0
    ; cons(h)(t) => h + t
    } in
  fold{int}{int}(l)(alg)

let main: int =
  let tetractys = take{int}(nats)(5) in
  sum(tetractys)
    |};

  (* Test 22: Data kind (vectors) *)
  run_test
    ~name:"Data kind (vectors)"
    ~expected:3
    {|
data nat: type where
  { zero: nat
  ; succ: nat -> nat
  }

data vec: type -> nat -> type where
  { nil: {a} vec(a)(zero)
  ; cons: {a}{n: nat} a -> vec(a)(n) -> vec(a)(succ(n))
  }

let length{a}{k: nat}(v: vec(a)(k)): int =
  match v with
  { nil{_} => 0
  ; cons{_}{n}(x)(xs) => 1 + length{a}{n}(xs)
  }

let main: int =
  let v0 = cons{int}{zero}(0)(nil{int}) in
  let v1 = cons{int}{succ(zero)}(1)(v0) in
  let v2 = cons{int}{succ(succ(zero))}(2)(v1) in
  length{int}{succ(succ(succ(zero)))}(v2)
    |};

  (* Test 23: List length *)
  run_test
    ~name:"List length (for comparison with vectors)"
    ~expected:3
    {|
data list: type -> type where
  { nil: {a} list(a)
  ; cons: {a} a -> list(a) -> list(a)
  }

let length{a}(xs: list(a)): int =
  match xs with
  { nil{_} => 0
  ; cons{_}(x)(xs) => 1 + length{a}(xs)
  }

let main: int =
  let l0 = cons{int}(0)(nil{int}) in
  let l1 = cons{int}(1)(l0) in
  let l2 = cons{int}(2)(l1) in
  length{int}(l2)
  |};

  (* Test 24: GADT codata *)
  run_test
    ~name:"GADT codata (streams of even/odd numbers)"
    ~expected:8
    {|
data message: type where
  { hello: message
  ; this_is_your_key: int -> message
  }

data socket_state: type where
  { raw: socket_state
  ; bound: socket_state
  ; live: socket_state
  }

code socket: socket_state -> type where
  { bind: socket(raw) -> int -> socket(bound)
  ; connect: socket(bound) -> socket(live)
  ; send: socket(live) -> message -> unit
  ; receive: socket(live) -> message
  ; close: socket(live) -> unit
  }

let main: int =
  let s =
    new socket(raw)
    { bind(port) =>
        new
        { connect =>
            new
            { send(msg) => ()
            ; receive => this_is_your_key(8)
            ; close => ()
            }
        }
    }
  in
  let answer = receive(connect(bind(s)(8080))) in
  match answer with
  { hello => 0
  ; this_is_your_key(k) => k
  }
    |};

  (* Test 25: Singleton types *)
  run_test
    ~name:"Singleton types"
    ~expected:3
    {|
data nat: type where
  { zero: nat
  ; succ: nat -> nat
  }

data single_nat: nat -> type where
  { single_zero: single_nat(zero)
  ; single_succ: {n: nat} single_nat(n) -> single_nat(succ(n))
  }

let to_nat{n: nat}(k: single_nat(n)): nat =
  match k with
  { single_zero => zero
  ; single_succ{m}(k') => succ(to_nat{m}(k'))
  }

let to_int{n: nat}(k: single_nat(n)): int =
  match k with
  { single_zero => 0
  ; single_succ{m}(k') => 1 + to_int{m}(k')
  }

data vec: type -> nat -> type where
  { nil: {a} vec(a)(zero)
  ; cons: {a}{n: nat} a -> vec(a)(n) -> vec(a)(succ(n))
  }

let replicate{a}{n: nat}(x: a)(k: single_nat(n)): vec(a)(n) =
  match k with
  { single_zero => nil{a}
  ; single_succ{m}(k') => cons{a}{m}(x)(replicate{a}{m}(x)(k'))
  }

let length{a}{n: nat}(v: vec(a)(n)): single_nat(n) =
  match v with
  { nil{_} => single_zero
  ; cons{_}{m}(x)(xs) => single_succ{m}(length{a}{m}(xs))
  }

let main: int =
  let n3_single =
    single_succ{succ(succ(zero))}
      (single_succ{succ(zero)}
        (single_succ{zero}(single_zero))) in
  let v = replicate{int}{succ(succ(succ(zero)))}(42)(n3_single) in
  let l = length{int}{succ(succ(succ(zero)))}(v) in
  to_int{succ(succ(succ(zero)))}(l)
  |};

  (* Test 26: Tree lookup *)
  run_test
    ~name:"Tree lookup with optimized closures"
    ~expected:10
    {|
data tree: type where
  { leaf: int -> tree
  ; node: tree -> tree -> tree
  }

let create(i: int)(n: int): tree =
  ifz(i / n) then
    let t = create(i + 1)(n) in
    node(t)(t)
  else
    leaf(n)

let lookup(t: tree): int =
  match t with
  { leaf(v) => v
  ; node(l)(_) => lookup(l)
  }

let main: int =
  lookup(create(0)(10))
    |};

  (* Test 27: Recursively defined stream *)
  run_test
    ~name:"Recursively defined stream"
    ~expected:10
    {|
data option: type -> type where
  { none: {a} option(a)
  ; some: {a} a -> option(a)
  }

code stream: type -> type where
  { state: {a} stream(a) -> a
  ; next: {a} stream(a) -> option(stream(a))
  }

let repeat(x: int): stream(int) =
  new stream(int)
  { state => x
  ; next => some{stream(int)}(repeat(x))
  }

let item{a}(n: int)(s: stream(a)): option(a) =
  ifz(n) then
    some{a}(state{a}(s))
  else
    match next{a}(s) with
    { none{_} => none{a}
    ; some{_}(s') => item{a}(n - 1)(s')
    }

let main: int =
  let tens = repeat(10) in
  match item{int}(13)(tens) with
  { none{_} => 0
  ; some{_}(x) => x
  }
    |};

  (* Test 28: Destinations parsing *)
  run_test
    ~name: "Destinations parsing"
    ~expected: 3
    {|
let test_alloc{a}(): lack(a)(dest(a)) =
  alloc{a}()

let test_fill(d: dest(int))(v: int): unit =
  fill(d)(v)

let test_finalize(x: lack(int)(unit)): int =
  finalize(x)

let main: int =
  3
    |};

  (* Test 29: Destination-passing list map *)
  run_test
    ~name: "Destination-passing list map"
    ~expected: 9
    {|
data list: type -> type where
  { nil: {a} list(a)
  ; cons: {a} a -> list(a) -> list(a)
  }

let map_dsp{a}{b}(f: a -> b)(xs: list(a))(ds: dest(list(b))): unit =
  match xs with
  { nil{_} => fill(ds)(nil{b})
  ; cons{_}(x)(xs) =>
      let (d, ds) = ds @ cons{b} in
      let _ = fill(d)(f(x)) in
      map_dsp{a}{b}(f)(xs)(ds)
  }

let map{a}{b}(f: a -> b)(xs: list(a)): list(b) =
  let init = alloc{list(b)}() in
  let r = update init with { (ds) => map_dsp{a}{b}(f)(xs)(ds) } in
  finalize(r)

let foldl{a}{b}(f: b -> a -> a)(init: a)(ys: list(b)): a =
  match ys with
  { nil{b} => init
  ; cons{b}(y)(ys) => foldl{a}{b}(f)(f(y)(init))(ys)
  }

let xs(n: int): list(int) =
  cons{int}(n)(cons{int}(n)(nil{int}))

let main: int =
  let xs = xs(2) in
  let f = fun(x: int) => x + 1 in
  let ys = map{int}{int}(f)(xs) in
  let g = fun(i: int)(y: int) => i * y in
  foldl{int}{int}(g)(1)(ys)
|};

  (* Test 30: Simple DSP test - check list structure *)
  run_test
    ~name: "DSP list second element"
    ~expected: 3
    {|
data list: type -> type where
  { nil: {a} list(a)
  ; cons: {a} a -> list(a) -> list(a)
  }

let map_dsp{a}{b}(f: a -> b)(xs: list(a))(ds: dest(list(b))): unit =
  match xs with
  { nil{_} => fill(ds)(nil{b})
  ; cons{_}(x)(xs) =>
      let (d, ds) = ds @ cons{b} in
      let _ = fill(d)(f(x)) in
      map_dsp{a}{b}(f)(xs)(ds)
  }

let map{a}{b}(f: a -> b)(xs: list(a)): list(b) =
  let init = alloc{list(b)}() in
  let r = update init with { (ds) => map_dsp{a}{b}(f)(xs)(ds) } in
  finalize(r)

let xs(n: int): list(int) =
  cons{int}(n)(cons{int}(n)(nil{int}))

let main: int =
  let xs = xs(2) in
  let f = fun(x: int) => x + 1 in
  let ys = map{int}{int}(f)(xs) in
  match ys with
  { nil{_} => 0
  ; cons{_}(x)(xs) =>
      match xs with
      { nil{_} => 100
      ; cons{_}(y)(ys) => y
      }
  }
|};

  (* Test 31: DSP build two-element list directly *)
  run_test
    ~name: "DSP direct two-element list"
    ~expected: 2
    {|
data list: type -> type where
  { nil: {a} list(a)
  ; cons: {a} a -> list(a) -> list(a)
  }

let build_two{a}(x: a)(y: a)(ds: dest(list(a))): unit =
  let (d1, ds1) = ds @ cons{a} in
  let _ = fill(d1)(x) in
  let (d2, ds2) = ds1 @ cons{a} in
  let _ = fill(d2)(y) in
  fill(ds2)(nil{a})

let make_two{a}(x: a)(y: a): list(a) =
  let init = alloc{list(a)}() in
  let r = update init with { (ds) => build_two{a}(x)(y)(ds) } in
  finalize(r)

let main: int =
  let xs = make_two{int}(1)(2) in
  match xs with
  { nil{_} => 0
  ; cons{_}(x)(xs) =>
      match xs with
      { nil{_} => 100
      ; cons{_}(y)(ys) => y
      }
  }
|};

  (* Final Summary *)
  print_endline "════════════════════════════════════════════════════════════════";
  Printf.printf "Results: %d/%d tests passed\n" !pass_count !test_count;
  print_endline "════════════════════════════════════════════════════════════════"
