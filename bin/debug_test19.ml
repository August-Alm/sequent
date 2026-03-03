open Sequent
open Common.Identifiers

module Pipe = Pipeline

(* Test 19: Higher-rank polymorphism *)
let source = {|
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
|}

let () = 
  print_endline "Test 19: Higher-rank polymorphism with named function";
  Compile_checked.debug_subst := true;
  Compile_checked.debug_conn := true;
  
  let (decs, defs) = match Pipe.LangStage.to_melcore source with Ok x -> x | Error e -> failwith e in
  let (decs, typed_defs) = match Pipe.MelcoreStage.type_check decs defs with Ok x -> x | Error e -> failwith e in
  let norm_defs = Pipe.MelcoreStage.normalize typed_defs in
  let (types_ctx, core_defs) = match Pipe.MelcoreStage.encode decs norm_defs with Ok x -> x | Error e -> failwith e in
  let mono_result = match Pipe.CoreStage.monomorphize types_ctx core_defs with Ok x -> x | Error e -> failwith e in
  
  let module CTypes = Core.Types.CoreTypes in
  let decs_with_new =
    List.fold_left (fun acc (dec: CTypes.dec) ->
      Path.add dec.name dec acc
    ) types_ctx.decs mono_result.new_declarations
  in
  
  let _focused_decs = Focus.focus_decs decs_with_new in
  let focused_main_unclosed = Focus.focus_def decs_with_new mono_result.main in
  
  let _closed_main = 
    match List.rev focused_main_unclosed.term_params with
    | (ret_k, Focused.Types.FocusedBase.Cns ret_ty) :: _ ->
        let closed_body = Focused.Return.close_ret_var ret_ty ret_k focused_main_unclosed.body in
        { focused_main_unclosed with Focused.Terms.body = closed_body }
    | _ -> focused_main_unclosed
  in
  
  let ( let* ) = Result.bind in
  let result =
    let* (focused_decs, focused_main, focused_defs) = 
      Pipe.CoreStage.focus types_ctx mono_result in
    
    let* (_, axil_main, axil_defs) = 
      Pipe.AxilStage.linearize focused_decs focused_main focused_defs in
    
    print_endline "\n=== Axil main ===";
    print_endline (Axil.Printing.pp_command axil_main.Axil.Terms.body);
    
    print_endline "\n=== Axil definitions ===";
    List.iter (fun (p, def) -> 
      Printf.printf "%s:\n%s\n\n" (Path.name p) (Axil.Printing.pp_command def.Axil.Terms.body)
    ) (Path.to_list axil_defs);
    
    let* (asm_code, _) = 
      Pipe.EmitStage.compile Pipe.EmitStage.AARCH64 axil_main axil_defs in
    
    let* result = Pipe.EmitStage.eval ~trace:false ~max_steps:500 asm_code in
    Ok result
  in
  match result with
  | Ok n -> Printf.printf "\nResult: %d (expected 5)\n" n
  | Error e -> Printf.printf "\nError: %s\n" e
