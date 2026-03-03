(* Test 24: GADT codata - socket with state indexing *)
module Pipe = Sequent.Pipeline

let source = {|
data unit: type where
  { U: unit
  }

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
            { send(msg) => U
            ; receive => this_is_your_key(8)
            ; close => U
            }
        }
    }
  in
  let answer = receive(connect(bind(s)(8080))) in
  match answer with
  { hello => 0
  ; this_is_your_key(k) => k
  }
|}

let ( let* ) = Result.bind

let () =
  let result =
    let* (decs, defs) = Pipe.LangStage.to_melcore source in
    let* (decs, typed_defs) = Pipe.MelcoreStage.type_check decs defs in
    let norm_defs = Pipe.MelcoreStage.normalize typed_defs in
    let* (types_ctx, core_defs) = Pipe.MelcoreStage.encode decs norm_defs in
    let* (types_ctx, core_defs) = Pipe.CoreStage.type_check types_ctx core_defs in
    let* mono_result = Pipe.CoreStage.monomorphize types_ctx core_defs in
    let* (focused_decs, focused_main, focused_defs) = 
      Pipe.CoreStage.focus types_ctx mono_result in
    let* _ = Pipe.FocusedStage.type_check focused_decs focused_defs in
    let* (axil_decs, axil_main, axil_defs) = 
      Pipe.AxilStage.linearize focused_decs focused_main focused_defs in
    let* _ = Pipe.AxilStage.type_check axil_decs axil_defs in
    let (code, _arg_count) = Sequent.Compile_checked.compile axil_main axil_defs in
    Printf.printf "%d instructions generated\n" (List.length code);
    (* Count actual instructions vs labels *)
    let labels = List.filter (fun i -> match i with Sequent.Aarch64.Code.LAB _ -> true | _ -> false) code in
    let non_labels = List.length code - List.length labels in
    Printf.printf "Labels: %d, Non-labels: %d\n" (List.length labels) non_labels;
    Printf.printf "Max valid PC (raw): %d\n" ((List.length code - 1) * 4);
    Printf.printf "Max valid PC (actual): %d\n" ((non_labels - 1) * 4);
    (* Print instructions around PC 4012 *)
    Printf.printf "\nInstructions around PC 4000-4100:\n";
    let pc = ref 0 in
    List.iter (fun instr ->
      match instr with
      | Sequent.Aarch64.Code.LAB l -> 
        if !pc >= 4000 && !pc <= 4100 then
          Printf.printf "%4d: [%s]\n" !pc l
      | _ ->
        if !pc >= 4000 && !pc <= 4100 then
          Printf.printf "%4d: %s\n" !pc (Sequent.Aarch64.Code.Code.to_string instr);
        pc := !pc + 4
    ) code;
    Printf.printf "\nFinal PC: %d\n" !pc;
    (* Print instructions around PC 1400-1420 *)
    Printf.printf "\nInstructions around PC 1400-1420:\n";
    let pc_ref = ref 0 in
    List.iter (fun instr ->
      match instr with
      | Sequent.Aarch64.Code.LAB l -> 
        if !pc_ref >= 1350 && !pc_ref <= 1430 then
          Printf.printf "%4d: [%s]\n" !pc_ref l
      | _ ->
        if !pc_ref >= 1350 && !pc_ref <= 1430 then
          Printf.printf "%4d: %s\n" !pc_ref (Sequent.Aarch64.Code.Code.to_string instr);
        pc_ref := !pc_ref + 4
    ) code;
    (* Run without trace, let it crash *)
    let* result = Pipe.EmitStage.eval ~trace:false ~max_steps:50000 code in
    Printf.printf "Result: %d (expected: 8)\n" result;
    Ok ()
  in
  match result with
  | Ok () -> ()
  | Error msg -> Printf.printf "Error: %s\n" msg
