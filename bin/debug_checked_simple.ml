open Sequent
open Common.Identifiers

module Pipe = Pipeline

(* Same as Test 20 *)
let source = {|data tuple: type -> type -> type where
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
|}

let () = 
  print_endline "Test: closure capture";
  let (decs, defs) = match Pipe.LangStage.to_melcore source with Ok x -> x | Error e -> failwith e in
  let (decs, typed_defs) = match Pipe.MelcoreStage.type_check decs defs with Ok x -> x | Error e -> failwith e in
  let norm_defs = Pipe.MelcoreStage.normalize typed_defs in
  let (types_ctx, core_defs) = match Pipe.MelcoreStage.encode decs norm_defs with Ok x -> x | Error e -> failwith e in
  let mono_result = match Pipe.CoreStage.monomorphize types_ctx core_defs with Ok x -> x | Error e -> failwith e in
  
  (* Focus *)
  let module CTypes = Core.Types.CoreTypes in
  let decs_with_new =
    List.fold_left (fun acc (dec: CTypes.dec) ->
      Path.add dec.name dec acc
    ) types_ctx.decs mono_result.new_declarations
  in
  
  let focused_decs = Focus.focus_decs decs_with_new in
  let focused_main_unclosed = Focus.focus_def decs_with_new mono_result.main in
  
  (* Close it (same as pipeline) *)
  let closed_main = 
    match List.rev focused_main_unclosed.term_params with
    | (ret_k, Focused.Types.FocusedBase.Cns ret_ty) :: _ ->
        let closed_body = Focused.Return.close_ret_var ret_ty ret_k focused_main_unclosed.body in
        { focused_main_unclosed with Focused.Terms.body = closed_body }
    | _ -> focused_main_unclosed
  in
  
  print_endline "\n=== closed_main.term_params ===";
  List.iter (fun (v, ct) -> 
    Printf.printf "  %s : %s\n" (Ident.name v) (Focused.Printing.pp_chiral_typ ct)
  ) closed_main.term_params;
  
  print_endline "\n=== closed_main body ===";
  print_endline (Focused.Printing.pp_command closed_main.body);
  
  (* Linearize using pipeline *)
  let (_axil_decs, axil_main, _) = match Pipe.AxilStage.linearize focused_decs closed_main Path.emptytbl with
    | Ok x -> x
    | Error e -> failwith e
  in
  
  print_endline "\n=== AXIL main.term_params ===";
  List.iter (fun (v, ct) -> 
    Printf.printf "  %s : %s\n" (Ident.name v) (Axil.Printing.pp_chiral_typ ct)
  ) axil_main.Axil.Terms.term_params;
  
  print_endline "\n=== AXIL main body ===";
  print_endline (Axil.Printing.pp_command axil_main.Axil.Terms.body);
  
  (* Check AXIL definitions *)
  let all_defs = Path.add axil_main.Axil.Terms.path axil_main Path.emptytbl in
  let checked_defs = Axil.Checked.check_definitions all_defs in
  
  print_endline "\n=== Checked main ===";
  
  (* Print all paths in checked_defs *)
  print_endline "Checked defs paths:";
  List.iter (fun (p, _) -> print_endline ("  " ^ Path.name p)) (Path.to_list checked_defs);
  
  let checked_main = Path.find axil_main.Axil.Terms.path checked_defs in
  
  (* Print the checked command structure recursively to see ctx *)
  let rec print_checked_cmd indent cmd = 
    let ind = String.make indent ' ' in
    match cmd with
    | Axil.Checked.CNew { ctx; k; branches; body; _ } ->
        Printf.printf "%sCNew { k=%s; ctx=[%s] }\n" ind (Ident.name k)
          (String.concat ", " (List.map (fun (v, _) -> Ident.name v) ctx));
        List.iter (fun br ->
          Printf.printf "%s  branch %s: ctx=[%s]\n" ind 
            (Path.name br.Axil.Checked.xtor)
            (String.concat ", " (List.map (fun (v, _) -> Ident.name v) br.branch_ctx));
          print_checked_cmd (indent+4) br.body
        ) branches;
        print_checked_cmd (indent+2) body
    | Axil.Checked.CLet { v; body; _ } ->
        Printf.printf "%sCLet { v=%s }\n" ind (Ident.name v);
        print_checked_cmd (indent+2) body
    | Axil.Checked.CSwitch { v; branches; _ } ->
        Printf.printf "%sCSwitch { v=%s }\n" ind (Ident.name v);
        List.iter (fun br ->
          Printf.printf "%s  branch %s:\n" ind (Path.name br.Axil.Checked.xtor);
          print_checked_cmd (indent+4) br.body
        ) branches
    | Axil.Checked.CJump { label; _ } ->
        Printf.printf "%sCJump { label=%s }\n" ind (Path.name label)
    | Axil.Checked.CSubstitute { src_ctx; tgt_ctx; body; _ } ->
        Printf.printf "%sCSubstitute { src=[%s]; tgt=[%s] }\n" ind
          (String.concat ", " (List.map (fun (v, _) -> Ident.name v) src_ctx))
          (String.concat ", " (List.map (fun (v, _) -> Ident.name v) tgt_ctx));
        print_checked_cmd (indent+2) body
    | Axil.Checked.CInvoke { v; xtor; _ } ->
        Printf.printf "%sCInvoke { v=%s.%s }\n" ind (Ident.name v) (Path.name xtor)
    | Axil.Checked.CAxiom { v; k; _ } ->
        Printf.printf "%sCAxiom { v=%s, k=%s }\n" ind (Ident.name v) (Ident.name k)
    | Axil.Checked.CRet { v; _ } ->
        Printf.printf "%sCRet { v=%s }\n" ind (Ident.name v)
    | Axil.Checked.CLit { n; v; _ } ->
        Printf.printf "%sCLit { n=%d, v=%s }\n" ind n (Ident.name v)
    | _ -> Printf.printf "%s<other>\n" ind
  in
  print_checked_cmd 0 checked_main.body;
  
  (* Run through full pipeline stages to test *)
  print_endline "\n=== Running test through pipeline ===";
  let ( let* ) = Result.bind in
  let result =
    let* (focused_decs, focused_main, focused_defs) = 
      Pipe.CoreStage.focus types_ctx mono_result in
    
    (* Print all focused definitions *)
    print_endline "\n=== Focused definitions ===";
    List.iter (fun (p, (def: Focused.Terms.definition)) ->
      Printf.printf "%s:\n%s\n\n" (Path.name p) (Focused.Printing.pp_command def.body)
    ) (Path.to_list focused_defs);
    
    let* (_, axil_main, axil_defs) = 
      Pipe.AxilStage.linearize focused_decs focused_main focused_defs in
    
    (* Print all Axil definitions *)
    print_endline "\n=== Axil definitions ===";
    List.iter (fun (p, (def: Axil.Terms.definition)) ->
      Printf.printf "%s:\n%s\n\n" (Path.name p) (Axil.Printing.pp_command def.body)
    ) (Path.to_list axil_defs);
    
    (* Also check and print main *)
    print_endline "\n=== Axil main for compilation ===";
    Printf.printf "main:\n%s\n\n" (Axil.Printing.pp_command axil_main.Axil.Terms.body);
    
    let* (asm_code, _arg_count) = 
      Pipe.EmitStage.compile Pipe.EmitStage.AARCH64 axil_main axil_defs in
    
    (* Print the generated assembly *)
    print_endline "\n=== Generated Assembly (first 100 lines) ===";
    let asm_lines = List.mapi (fun i c -> Printf.sprintf "%d: %s" (i*4) (Aarch64.Code.Code.to_string c)) asm_code in
    List.iter print_endline (List.filteri (fun i _ -> i < 100) asm_lines);
    
    (* Enable trace to see step-by-step execution *)
    print_endline "\n=== Execution Trace ===";
    let* result = Pipe.EmitStage.eval ~trace:true ~max_steps:1000 asm_code in
    Ok result
  in
  match result with
  | Ok n -> Printf.printf "Result: %d (expected 5)\n" n
  | Error e -> Printf.printf "Error: %s\n" e
