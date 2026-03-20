(**
  module: Checked
  description: Checked commands - commands annotated with typing contexts.
  
  This module defines an intrinsically-typed representation of AXIL commands
  where each node carries its typing context. This eliminates the error-prone
  manual context threading in the compiler.
  
  The transformation from `command` to `checked_command` is performed after
  type checking, ensuring that context information is correct.
*)

open Common.Identifiers
open Common.External
open Terms
open Types.AxilTypes
open Types.AxilBase

(** Context: ordered list of bindings (head = first to consume) *)
type ctx = (var * chiral_typ) list

(** Checked branch for switch/new *)
type checked_branch =
  { xtor: Path.t
  ; type_vars: var list
  ; args: (var * chiral_typ) list
  ; branch_ctx: ctx
  ; body: checked_command
  }

(** Checked command: command annotated with typing contexts.
    Each constructor carries all context information needed for compilation.
    
    - CLet: let v = xtor(args); body
    - CSwitch: switch v {...}
    - CNew: new k = (captured){...}; body
    - CInvoke: invoke v.xtor(args)
    - CSubstitute: substitute [mapping]; body
    - CJump: jump label(args)
    - CAxiom: <v | k>
    - CLit, CNewInt, CAdd, CSub, CIfz: primitive operations
    - CRet, CEnd: terminals *)
and checked_command =
  (* let v = xtor(args); body *)
  | CLet of
      { ctx: ctx                        (* input context *)
      ; v: var                          (* bound variable *)
      ; v_typ: chiral_typ               (* type of v *)
      ; dec: dec
      ; xtor: Path.t
      ; args: (var * chiral_typ) list   (* consumed prefix with types *)
      ; tail_ctx: ctx                   (* ctx after removing args prefix *)
      ; body: checked_command           (* body in (v,v_typ)::tail_ctx *)
      } 
  (* switch v { branches } *)
  | CSwitch of
      { ctx: ctx                        (* input context, v at head *)
      ; v: var                          (* scrutinee at head *)
      ; v_typ: chiral_typ
      ; dec: dec
      ; tail_ctx: ctx                  (* ctx without v *)
      ; branches: checked_branch list
      }
  (* new k = (captured){ branches }; body *)
  | CNew of
      { ctx: ctx                        (* captured context for branches *)
      ; k: var                          (* continuation variable *)
      ; k_typ: chiral_typ               (* type of k *)
      ; dec: dec
      ; branches: checked_branch list
      ; body: checked_command           (* body in (k,k_typ)::ctx *)
      }
  (* invoke v.xtor(args) *)
  | CInvoke of
      { ctx: ctx                        (* input context *)
      ;  v: var                         (* continuation to invoke *)
      ;  v_typ: chiral_typ
      ;  dec: dec
      ;  xtor: Path.t
      ;  args: (var * chiral_typ) list  (* method args *)
      }
  (* substitute [mapping]; body *)
  | CSubstitute of
      { src_ctx: ctx                    (* input context *)
      ;  mapping: (var * var) list      (* v' -> v mapping *)
      ;  tgt_ctx: ctx                   (* output context (reordered) *)
      ;  body: checked_command
      }
  (* jump label(args) *)
  | CJump of
      { ctx: ctx                        (* input context *)
      ; label: Path.t
      ; args: (var * chiral_typ) list
      }
  (* <v | k> : axiom *)
  | CAxiom of
      { ctx: ctx
      ; typ: ext_type
      ; v: var
      ; k: var
      }
  (* lit n { v => body } *)
  | CLit of
      { ctx: ctx
      ; n: int64
      ; v: var
      ; body: checked_command         (* body in (v, Prd Int)::ctx *)
      }
  (* new_int k = { param => branch }; cont *)
  | CNewInt of
      { ctx: ctx
      ; k: var
      ; param: var
      ; branch_body: checked_command   (* in ctx @ [(param, Prd Int)] *)
      ; cont_body: checked_command     (* in (k, Cns Int)::ctx *)
      }
  (* add(x, y) { v => body } *)
  | CAdd of
      { ctx: ctx
      ; x: var
      ; y: var
      ; v: var
      ; body: checked_command          (* in (v, Prd Int)::ctx *)
      }
  (* sub(x, y) { v => body } *)
  | CSub of
      { ctx: ctx
      ; x: var
      ; y: var
      ; v: var
      ; body: checked_command
      }
  (* mul(x, y) { v => body } *)
  | CMul of
      { ctx: ctx
      ; x: var
      ; y: var
      ; v: var
      ; body: checked_command
      }
  (* div(x, y) { v => body } *)
  | CDiv of
      { ctx: ctx
      ; x: var
      ; y: var
      ; v: var
      ; body: checked_command
      }
  (* rem(x, y) { v => body } *)
  | CRem of
      { ctx: ctx
      ; x: var
      ; y: var
      ; v: var
      ; body: checked_command
      }
  (* ifz(v) { then; else } *)
  | CIfz of
      { ctx: ctx
      ; v: var
      ; then_cmd: checked_command
      ; else_cmd: checked_command
      }
  (* ret ty v *)
  | CRet of
      { ctx: ctx
      ; typ: typ
      ; v: var
      }
  (* end *)
  | CEnd of
      { ctx: ctx
      }

(** Checked definition *)
type checked_definition = {
  path: Path.t;
  (** Parameters with types = initial context *)
  params: ctx;
  body: checked_command;
}

(* ========================================================================= *)
(* Context Helpers                                                           *)
(* ========================================================================= *)

(** Extract n elements from head of context *)
let take_ctx (n: int) (ctx: ctx) : ctx =
  let rec aux n acc = function
      _ when n = 0 -> List.rev acc
    | [] -> List.rev acc
    | x :: xs -> aux (n - 1) (x :: acc) xs
  in
  aux n [] ctx

(** Drop n elements from head of context *)
let drop_ctx (n: int) (ctx: ctx) : ctx =
  let rec aux n = function
      lst when n = 0 -> lst
    | [] -> []
    | _ :: xs -> aux (n - 1) xs
  in
  aux n ctx

(** Look up variable in context *)
let lookup_ctx (ctx: ctx) (v: var) : chiral_typ option =
  List.find_map (fun (x, ct) -> if Ident.equal x v then Some ct else None) ctx

(** Look up variable in context (must exist) *)
let lookup_ctx_exn (ctx: ctx) (v: var) : chiral_typ =
  match lookup_ctx ctx v with
    Some ct -> ct
  | None -> failwith ("variable not in context: " ^ Ident.name v)

(** Extract specific variables from context (preserving order) *)
let extract_vars (ctx: ctx) (vars: var list) : ctx =
  List.map (fun v -> (v, lookup_ctx_exn ctx v)) vars

(** Remove a specific variable from context *)
let remove_var (ctx: ctx) (v: var) : ctx =
  List.filter (fun (x, _) -> not (Ident.equal x v)) ctx

(* ========================================================================= *)
(* Transformation from command to checked_command                            *)
(* ========================================================================= *)

(** Transform a command into a checked_command.
    ctx: the typing context at this point (from type checker flow) *)
let rec check_cmd (defs: definition Path.tbl) (ctx: ctx) (cmd: command) 
    : checked_command =
  match cmd with
    Let (v, dec, xtor_name, args, body) ->
      (* Find xtor to get argument types - must match what Switch uses *)
      let xtor = match List.find_opt (fun (x: xtor) -> 
          Path.equal x.name xtor_name
        ) dec.xtors
        with
          Some x -> x
        | None -> failwith ("xtor not found in Let: " ^ Path.name xtor_name)
      in
      (* Use xtor.argument_types for consistency with Switch loading *)
      let args_bindings = List.map2 (fun v ct -> (v, ct)) args xtor.argument_types in
      let tail_ctx = drop_ctx (List.length args) ctx in
      let v_typ = Prd (Lin, Sgn (dec.name, dec.type_args)) in
      let new_ctx = (v, v_typ) :: tail_ctx in
      CLet
        { ctx
        ; v
        ; v_typ
        ; dec
        ; xtor = xtor_name
        ; args = args_bindings
        ; tail_ctx
        ; body = check_cmd defs new_ctx body
        }

  | Switch (v, dec, branches) ->
    let v_typ = lookup_ctx_exn ctx v in
      let tail_ctx = drop_ctx 1 ctx in  (* v is at head *)
      let checked_branches = List.map (fun (xtor_name, type_vars, term_vars, body) ->
        check_clause defs dec tail_ctx xtor_name type_vars term_vars body
      ) branches in
      CSwitch
        { ctx
        ; v
        ; v_typ
        ; dec
        ; tail_ctx
        ; branches = checked_branches
        }

  | New (k, dec, branches, body) ->
      let k_typ = Cns (Lin, Sgn (dec.name, dec.type_args)) in
      let new_ctx = (k, k_typ) :: ctx in
      let checked_branches = List.map (fun (xtor_name, type_vars, term_vars, inner_body) ->
        check_method defs dec ctx xtor_name type_vars term_vars inner_body
      ) branches in
      CNew
        { ctx
        ; k
        ; k_typ
        ; dec
        ; branches = checked_branches
        ; body = check_cmd defs new_ctx body
        }

  | Invoke (v, dec, xtor_name, args) ->
      (* Find xtor to get argument types - must match what the method expects *)
      let xtor = match List.find_opt (fun (x: xtor) -> 
          Path.equal x.name xtor_name
        ) dec.xtors
        with
          Some x -> x
        | None -> failwith ("xtor not found in Invoke: " ^ Path.name xtor_name)
      in
      (* Use xtor.argument_types for consistency with method loading *)
      let args_bindings = List.map2 (fun v ct -> (v, ct)) args xtor.argument_types in
      let v_typ = lookup_ctx_exn ctx v in
      CInvoke
        { ctx
        ; v
        ; v_typ
        ; dec
        ; xtor = xtor_name
        ; args = args_bindings
        }

  | Substitute (mapping, body) ->
      let tgt_ctx = List.map (fun (v', v) -> (v', lookup_ctx_exn ctx v)) mapping in
      CSubstitute
        { src_ctx = ctx
        ; mapping
        ; tgt_ctx
        ; body = check_cmd defs tgt_ctx body
        }

  | Jump (label, args) ->
      (* Look up definition to get param types - must match what the definition expects *)
      let def = match Path.find_opt label defs with
          Some d -> d
        | None -> failwith ("definition not found for Jump: " ^ Path.name label)
      in
      (* Use definition's param types for consistency *)
      let args_bindings = List.map2 (fun arg (_, param_typ) -> (arg, param_typ)) 
          args def.term_params in
      CJump { ctx; label; args = args_bindings }

  | Axiom (typ, v, k) ->
      CAxiom { ctx; typ; v; k }

  | Lit (n, v, body) ->
      let new_ctx = (v, Prd (Unr, Ext Int)) :: ctx in
      CLit { ctx; n; v; body = check_cmd defs new_ctx body }

  | NewInt (k, param, branch_body, cont_body) ->
      let k_ctx = (k, Cns (Lin, Ext Int)) :: ctx in
      (* Captured at HEAD (high registers), args at TAIL (low registers). *)
      let param_ctx = ctx @ [(param, Prd (Unr, Ext Int))] in
      CNewInt
        { ctx
        ; k
        ; param
        ; branch_body = check_cmd defs param_ctx branch_body
        ; cont_body = check_cmd defs k_ctx cont_body
        }

  | Add (x, y, v, body) ->
      let new_ctx = (v, Prd (Unr, Ext Int)) :: ctx in
      CAdd { ctx; x; y; v; body = check_cmd defs new_ctx body }

  | Sub (x, y, v, body) ->
      let new_ctx = (v, Prd (Unr, Ext Int)) :: ctx in
      CSub { ctx; x; y; v; body = check_cmd defs new_ctx body }

  | Mul (x, y, v, body) ->
      let new_ctx = (v, Prd (Unr, Ext Int)) :: ctx in
      CMul { ctx; x; y; v; body = check_cmd defs new_ctx body }

  | Div (x, y, v, body) ->
      let new_ctx = (v, Prd (Unr, Ext Int)) :: ctx in
      CDiv { ctx; x; y; v; body = check_cmd defs new_ctx body }

  | Rem (x, y, v, body) ->
      let new_ctx = (v, Prd (Unr, Ext Int)) :: ctx in
      CRem { ctx; x; y; v; body = check_cmd defs new_ctx body }

  | Ifz (v, then_cmd, else_cmd) ->
      CIfz
        { ctx
        ; v
        ; then_cmd = check_cmd defs ctx then_cmd
        ; else_cmd = check_cmd defs ctx else_cmd
        }

  | Ret (typ, v) ->
      CRet { ctx; typ; v }

  | End ->
      CEnd { ctx }

(** Check branch for Switch (clause): body runs in args @ tail_ctx *)
and check_clause (defs: definition Path.tbl) (dec: dec) (tail_ctx: ctx)
    (xtor_name: Path.t) (type_vars: var list) (term_vars: var list) 
    (body: command) : checked_branch =
  let xtor = match List.find_opt (fun (x: xtor) -> 
      Path.equal x.name xtor_name
    ) dec.xtors
    with
      Some x -> x
    | None -> failwith ("xtor not found: " ^ Path.name xtor_name)
  in
  let args = List.map2 (fun v ct -> (v, ct)) term_vars xtor.argument_types in
  (* For clauses: args @ tail_ctx *)
  let branch_ctx = args @ tail_ctx in
  { xtor = xtor_name
  ; type_vars
  ; args
  ; branch_ctx
  ; body = check_cmd defs branch_ctx body
  }

(** Check branch for New (method): body runs in args @ captured_ctx *)
and check_method (defs: definition Path.tbl) (dec: dec) (captured_ctx: ctx)
    (xtor_name: Path.t) (type_vars: var list) (term_vars: var list) 
    (body: command) : checked_branch =
  let xtor = match List.find_opt (fun (x: xtor) -> 
      Path.equal x.name xtor_name
    ) dec.xtors
    with
      Some x -> x
    | None -> failwith ("xtor not found: " ^ Path.name xtor_name)
  in
  let args = List.map2 (fun v ct -> (v, ct)) term_vars xtor.argument_types in
  (* Register layout: captured_ctx @ args
     Args are at tail (lower pos_from_end, earlier registers).
     Captured env is at head (higher pos_from_end, later registers).
     This matches: codeMethod as cs -> load as cs where as=captured, cs=args *)
  let branch_ctx = captured_ctx @ args in
  { xtor = xtor_name
  ; type_vars
  ; args
  ; branch_ctx
  ; body = check_cmd defs branch_ctx body
  }

(** Transform a definition *)
let check_definition (defs: definition Path.tbl) (def: definition) 
    : checked_definition =
  let ctx = def.term_params in
  { path = def.path
  ; params = ctx
  ; body = check_cmd defs ctx def.body
  }

(** Transform all definitions *)
let check_definitions (defs: definition Path.tbl) 
    : checked_definition Path.tbl =
  Path.map_tbl (check_definition defs) defs

(* ========================================================================= *)
(* Accessors                                                                 *)
(* ========================================================================= *)

(** Get the input context of a checked_command *)
let get_ctx : checked_command -> ctx = function
    CLet { ctx; _ } -> ctx
  | CSwitch { ctx; _ } -> ctx
  | CNew { ctx; _ } -> ctx
  | CInvoke { ctx; _ } -> ctx
  | CSubstitute { src_ctx; _ } -> src_ctx
  | CJump { ctx; _ } -> ctx
  | CAxiom { ctx; _ } -> ctx
  | CLit { ctx; _ } -> ctx
  | CNewInt { ctx; _ } -> ctx
  | CAdd { ctx; _ } -> ctx
  | CSub { ctx; _ } -> ctx
  | CMul { ctx; _ } -> ctx
  | CDiv { ctx; _ } -> ctx
  | CRem { ctx; _ } -> ctx
  | CIfz { ctx; _ } -> ctx
  | CRet { ctx; _ } -> ctx
  | CEnd { ctx } -> ctx
