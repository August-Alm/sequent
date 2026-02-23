(** 
  This file contains a focusing normalization algorithm mapping a
  polarized sequent calculus with user-defined types, down to
  a Target language with eight statement form and no relations:
   
  ⟨C(Γ) | µ˜x.s⟩                 & ⟨µα.s |D(Γ)⟩
  ⟨x | case {C(Γ) ⇒ s, ... }⟩    & ⟨cocase {D(Γ) ⇒ s, ... } | α⟩
  ⟨µα.s | case {C(Γ) ⇒ s, ... }⟩ & ⟨cocase {D(Γ) ⇒ s, ... } | µ˜x.s⟩
  ⟨C(Γ) | α⟩                     & ⟨x | D(Γ)⟩

  It also incorporates encoding of a simple source lambda calculus into
  the polarized sequent calculus.
*)

open Common.Identifiers

module Fun = struct

  (* ========================================================================= *)
  (* Types (Fun Language)                                                      *)
  (* ========================================================================= *)

  type signature = tpe list list

  and tpe =
    | Int
    | Fun of tpe * tpe
    | Data of signature
    | Code of signature

  (* ========================================================================= *)
  (* Terms (Fun Language)                                                     *)
  (* ========================================================================= *)

  type term =
    | Var of Ident.t
    | Lam of Ident.t * tpe * term
    | App of term * term
    | Case of signature * term * clause list
    | Cocase of signature * clause list
    | Ctor of signature * int * term list
    | Dtor of signature * int * term list  (* first term is the subject *)
    | Lit of int
    | Add of term * term
  
  and clause = (Ident.t list) * term

  (** Show functions for Fun types *)
  let rec show_tpe = function
    | Int -> "Int"
    | Fun (a, b) -> Printf.sprintf "(%s → %s)" (show_tpe a) (show_tpe b)
    | Data sgn -> Printf.sprintf "Data%s" (show_signature sgn)
    | Code sgn -> Printf.sprintf "Code%s" (show_signature sgn)

  and show_signature sgn =
    let show_ctor tpes = Printf.sprintf "[%s]" (String.concat ", " (List.map show_tpe tpes)) in
    Printf.sprintf "[%s]" (String.concat "; " (List.map show_ctor sgn))

  (** Show functions for Fun terms *)
  let rec show_term = function
    | Var x -> Ident.name x
    | Lam (x, t, body) -> Printf.sprintf "λ%s:%s. %s" (Ident.name x) (show_tpe t) (show_term body)
    | App (f, arg) -> Printf.sprintf "(%s %s)" (show_term f) (show_term arg)
    | Lit n -> string_of_int n
    | Add (m, n) -> Printf.sprintf "add(%s, %s)" (show_term m) (show_term n)
    | Ctor (_, n, []) -> Printf.sprintf "C%d" n
    | Ctor (_, n, args) -> Printf.sprintf "C%d(%s)" n (String.concat ", " (List.map show_term args))
    | Dtor (_, n, args) -> Printf.sprintf "D%d(%s)" n (String.concat ", " (List.map show_term args))
    | Case (_, scrut, clauses) ->
        Printf.sprintf "case %s of {%s}" (show_term scrut) (show_clauses clauses)
    | Cocase (_, clauses) ->
        Printf.sprintf "cocase {%s}" (show_clauses clauses)

  and show_clauses clauses =
    String.concat "; " (List.mapi (fun i (params, body) ->
      Printf.sprintf "C%d(%s) ⇒ %s" i 
        (String.concat ", " (List.map Ident.name params))
        (show_term body)
    ) clauses)
end

(* ========================================================================= *)
(* Types (Core Language)                                                     *)
(* ========================================================================= *)

type signature = chiral_tpe list list

and tpe =
  | Int  (** Base integer type (positive) *)
  | Pos of signature
  | Neg of signature

and chiral_tpe =
  | Lhs of tpe
  | Rhs of tpe

let fun_tpe (a: tpe) (b: tpe) : tpe =
  match a, b with
  | (Pos _ | Int), Neg _ -> Neg [[Lhs a; Rhs b]]
  | _ -> failwith "Bad polarities for function type"

let raise_tpe (a: tpe) : tpe =
  match a with
  | Neg _ -> Pos [[Lhs a]]  (* data with one ctor holding a Neg producer *)
  | _ -> failwith "Bad polarity for raise type"

let lower_tpe (a: tpe) : tpe =
  match a with
  | Pos _ | Int -> Neg [[Rhs a]]  (* codata with one dtor returning a Pos/Int via continuation *)
  | _ -> failwith "Bad polarity for lower type"

(** Show functions for core types *)
let rec show_tpe = function
  | Int -> "Int"
  | Pos sgn -> Printf.sprintf "Pos%s" (show_signature sgn)
  | Neg sgn -> Printf.sprintf "Neg%s" (show_signature sgn)

and show_signature sgn =
  let show_ctor chiral_tpes = 
    Printf.sprintf "[%s]" (String.concat ", " (List.map show_chiral_tpe chiral_tpes)) 
  in
  Printf.sprintf "[%s]" (String.concat "; " (List.map show_ctor sgn))

and show_chiral_tpe = function
  | Lhs t -> Printf.sprintf "Lhs(%s)" (show_tpe t)
  | Rhs t -> Printf.sprintf "Rhs(%s)" (show_tpe t)

(* ========================================================================= *)
(* Substitutions (Renamings)                                                 *)
(* ========================================================================= *)

module Sub = struct
  (** A substitution is a finite map from identifiers to identifiers *)
  type t = Ident.t Ident.tbl

  let empty : t = Ident.emptytbl

  let add (x : Ident.t) (y : Ident.t) (s : t) : t = 
    Ident.add x y s

  let apply (s : t) (x : Ident.t) : Ident.t =
    match Ident.find_opt x s with
    | Some y -> y
    | None -> x
end

(* ========================================================================= *)
(* Core Language                                                           *)
(* ========================================================================= *)

module Source = struct

  type command =
    | CutPos of signature * term * term
    | CutNeg of signature * term * term
    | CutInt of term * term  (** ⟨int | k⟩ at Int type *)
    | Add of term * term * term  (** add(n, m, k) where n, m : Int, k : continuation *)
    | Ret of signature * Ident.t  (** Return a value *)
    | RetInt of Ident.t  (** Return an integer *)
    | End

  and term =
    | Variable of Ident.t
    | Lit of int  (** Integer literal *)
    | Constructor of signature * int * term list
    | Match of signature * branch list
    | Comatch of signature * branch list
    | Destructor of signature * int * term list
    | MuLhsPos of signature * Ident.t * command
    | MuRhsPos of signature * Ident.t * command
    | MuLhsNeg of signature * Ident.t * command
    | MuRhsNeg of signature * Ident.t * command
    | MuInt of Ident.t * command  (** μx.s where x : Int *)

  and branch = Clause of Ident.t list * command

  (** Apply renaming to a command *)
  let rec rename_command (h : Sub.t) : command -> command = function
    | CutPos (sgn, lhs, rhs) -> 
        CutPos (sgn, rename_term h lhs, rename_term h rhs)
    | CutNeg (sgn, lhs, rhs) -> 
        CutNeg (sgn, rename_term h lhs, rename_term h rhs)
    | CutInt (lhs, rhs) ->
        CutInt (rename_term h lhs, rename_term h rhs)
    | Add (t1, t2, k) ->
        Add (rename_term h t1, rename_term h t2, rename_term h k)
    | Ret (sgn, x) -> Ret (sgn, Sub.apply h x)
    | RetInt x -> RetInt (Sub.apply h x)
    | End -> End

  and rename_term (h : Sub.t) : term -> term = function
    | Variable x -> Variable (Sub.apply h x)
    | Lit n -> Lit n
    | Constructor (sgn, n, args) -> 
        Constructor (sgn, n, List.map (rename_term h) args)
    | Match (sgn, branches) -> 
        Match (sgn, List.map (rename_branch h) branches)
    | Comatch (sgn, branches) -> 
        Comatch (sgn, List.map (rename_branch h) branches)
    | Destructor (sgn, n, args) -> 
        Destructor (sgn, n, List.map (rename_term h) args)
    | MuLhsPos (sgn, x, cmd) ->
        let x' = Ident.fresh () in
        MuLhsPos (sgn, x', rename_command (Sub.add x x' h) cmd)
    | MuRhsPos (sgn, x, cmd) ->
        let x' = Ident.fresh () in
        MuRhsPos (sgn, x', rename_command (Sub.add x x' h) cmd)
    | MuLhsNeg (sgn, a, cmd) ->
        let a' = Ident.fresh () in
        MuLhsNeg (sgn, a', rename_command (Sub.add a a' h) cmd)
    | MuRhsNeg (sgn, a, cmd) ->
        let a' = Ident.fresh () in
        MuRhsNeg (sgn, a', rename_command (Sub.add a a' h) cmd)
    | MuInt (x, cmd) ->
        let x' = Ident.fresh () in
        MuInt (x', rename_command (Sub.add x x' h) cmd)

  and rename_branch (h : Sub.t) (Clause (params, body)) : branch =
    let params' = List.map (fun _ -> Ident.fresh ()) params in
    let h' = List.fold_left2 (fun acc p p' -> Sub.add p p' acc) h params params' in
    Clause (params', rename_command h' body)

  (** Show functions for debugging *)
  let rec show_command = function
    | CutPos (_, l, r) -> Printf.sprintf "⟨%s | %s⟩⁺" (show_term l) (show_term r)
    | CutNeg (_, l, r) -> Printf.sprintf "⟨%s | %s⟩⁻" (show_term l) (show_term r)
    | CutInt (l, r) -> Printf.sprintf "⟨%s | %s⟩ⁱ" (show_term l) (show_term r)
    | Add (t1, t2, k) -> Printf.sprintf "add(%s, %s, %s)" (show_term t1) (show_term t2) (show_term k)
    | Ret (_, x) -> Printf.sprintf "ret %s" (Ident.name x)
    | RetInt x -> Printf.sprintf "ret %s" (Ident.name x)
    | End -> "∎"

  and show_term = function
    | Variable x -> Ident.name x
    | Lit n -> string_of_int n
    | Constructor (_, n, args) -> 
        Printf.sprintf "C%d(%s)" n (String.concat ", " (List.map show_term args))
    | Match (_, bs) -> 
        Printf.sprintf "case{%s}" (String.concat "; " (List.map show_branch bs))
    | Comatch (_, bs) -> 
        Printf.sprintf "cocase{%s}" (String.concat "; " (List.map show_branch bs))
    | Destructor (_, n, args) -> 
        Printf.sprintf "D%d(%s)" n (String.concat ", " (List.map show_term args))
    | MuLhsPos (_, x, cmd) -> 
        Printf.sprintf "μ⁺%s.%s" (Ident.name x) (show_command cmd)
    | MuRhsPos (_, x, cmd) -> 
        Printf.sprintf "μ̃⁺%s.%s" (Ident.name x) (show_command cmd)
    | MuLhsNeg (_, x, cmd) -> 
        Printf.sprintf "μ⁻%s.%s" (Ident.name x) (show_command cmd)
    | MuRhsNeg (_, x, cmd) -> 
        Printf.sprintf "μ̃⁻%s.%s" (Ident.name x) (show_command cmd)
    | MuInt (x, cmd) ->
        Printf.sprintf "μⁱ%s.%s" (Ident.name x) (show_command cmd)

  and show_branch (Clause (params, body)) =
    Printf.sprintf "(%s)⇒%s" (String.concat "," (List.map Ident.name params)) (show_command body)
end
module Encode = struct

  (* ========================================================================= *)
  (* Type Encoding                                                            *)
  (* ========================================================================= *)

  let rec encode_tpe (t : Fun.tpe) : tpe =
    match t with
    | Int -> Int
    | Fun (a, b) ->
      (match encode_tpe a, encode_tpe b with
      | (Pos _ as a'), (Neg _ as b') -> fun_tpe a' b'
      | (Pos _ as a'), (Pos _ as b') -> fun_tpe a' (lower_tpe b')
      | (Neg _ as a'), (Neg _ as b') -> fun_tpe (raise_tpe a') b'
      | (Neg _ as a'), (Pos _ as b') -> fun_tpe (raise_tpe a') (lower_tpe b')
      (* Int in function types - treat as positive *)
      | Int, (Neg _ as b') -> fun_tpe Int b'
      | Int, (Pos _ as b') -> fun_tpe Int (lower_tpe b')
      | Int, Int -> fun_tpe Int (lower_tpe Int)
      | (Pos _ as a'), Int -> fun_tpe a' (lower_tpe Int)
      | (Neg _ as a'), Int -> fun_tpe (raise_tpe a') (lower_tpe Int))
    | Data sgn -> Pos (encode_data_sgn sgn)
    | Code sgn -> Neg (encode_code_sgn sgn)
  
  and encode_data_sgn (sgn : Fun.signature) : signature =
    List.map (List.map (fun t -> Lhs (encode_tpe t))) sgn
  
  and encode_code_sgn (sgn : Fun.signature) : signature =
    let encode_dtor tys =
      match List.rev tys with
      | [] -> failwith "Code signature must have at least one argument"
      | cod_tpe :: arg_tpes ->
          let cod_tpe' = Rhs (encode_tpe cod_tpe) in
          let arg_tpes' = List.rev_map (fun t -> Lhs (encode_tpe t)) arg_tpes in
          arg_tpes' @ [cod_tpe']
    in
    List.map encode_dtor sgn

  (* ========================================================================= *)
  (* Fun Type Checking                                                         *)
  (* ========================================================================= *)

  type ctx = Fun.tpe Ident.tbl

  type error =
    | UnboundVar of Ident.t
    | TypeMismatch of { expected: string; got: Fun.tpe }
    | NotAFunction of Fun.tpe
    | NotAData of Fun.tpe
    | NotACode of Fun.tpe
    | ArityMismatch of { expected: int; got: int }
    | XtorOutOfBounds of { idx: int; size: int }

  type 'a result = ('a, error) Result.t
  let ( let* ) = Result.bind

  let lookup (ctx : ctx) (x : Ident.t) : Fun.tpe result =
    match Ident.find_opt x ctx with
    | Some t -> Ok t
    | None -> Error (UnboundVar x)

  let expect_fun (t : Fun.tpe) : (Fun.tpe * Fun.tpe) result =
    match t with
    | Fun (a, b) -> Ok (a, b)
    | _ -> Error (NotAFunction t)

  let expect_data (t : Fun.tpe) : Fun.signature result =
    match t with
    | Data sgn -> Ok sgn
    | _ -> Error (NotAData t)

  let expect_code (t : Fun.tpe) : Fun.signature result =
    match t with
    | Code sgn -> Ok sgn
    | _ -> Error (NotACode t)

  let get_xtor (sgn : Fun.signature) (n : int) : Fun.tpe list result =
    if n < 0 || n >= List.length sgn then
      Error (XtorOutOfBounds { idx = n; size = List.length sgn })
    else
      Ok (List.nth sgn n)

  (** Infer the type of a Fun term *)
  let rec infer (ctx : ctx) (term : Fun.term) : Fun.tpe result =
    match term with
    | Fun.Var x -> lookup ctx x

    | Fun.Lam (x, t, body) ->
        let ctx' = Ident.add x t ctx in
        let* body_tpe = infer ctx' body in
        Ok (Fun.Fun (t, body_tpe))

    | Fun.App (f, arg) ->
        let* f_tpe = infer ctx f in
        let* (a, b) = expect_fun f_tpe in
        let* arg_tpe = infer ctx arg in
        if arg_tpe = a then Ok b
        else Error (TypeMismatch { expected = "argument type"; got = arg_tpe })

    | Fun.Case (sgn, scrut, clauses) ->
        let* scrut_tpe = infer ctx scrut in
        let* _ = expect_data scrut_tpe in
        (* All clauses must return the same type *)
        infer_clauses ctx sgn clauses

    | Fun.Cocase (sgn, clauses) ->
        (* Each clause corresponds to a destructor *)
        let* _ = check_cocase_clauses ctx sgn clauses in
        Ok (Fun.Code sgn)

    | Fun.Ctor (sgn, n, args) ->
        let* expected_tpes = get_xtor sgn n in
        let* _ = check_args ctx args expected_tpes in
        Ok (Fun.Data sgn)

    | Fun.Dtor (sgn, n, args) ->
        (* args = [subject; arg1; ...; argN] *)
        (match args with
        | [] -> failwith "Destructor must have at least a subject"
        | subj :: rest_args ->
            let* subj_tpe = infer ctx subj in
            let* subj_sgn = expect_code subj_tpe in
            if subj_sgn <> sgn then
              Error (TypeMismatch { expected = "matching Code signature"; got = subj_tpe })
            else
              let* dtor_tpes = get_xtor sgn n in
              (* dtor_tpes = [arg1_tpe; ...; argN_tpe; result_tpe] *)
              (match List.rev dtor_tpes with
              | [] -> failwith "Destructor must have at least a result type"
              | result_tpe :: arg_tpes_rev ->
                  let arg_tpes = List.rev arg_tpes_rev in
                  let* _ = check_args ctx rest_args arg_tpes in
                  Ok result_tpe))

    | Fun.Lit _ -> Ok Fun.Int

    | Fun.Add (m, n) ->
        let* m_tpe = infer ctx m in
        let* n_tpe = infer ctx n in
        (match m_tpe, n_tpe with
        | Fun.Int, Fun.Int -> Ok Fun.Int
        | Fun.Int, _ -> Error (TypeMismatch { expected = "Int"; got = n_tpe })
        | _, _ -> Error (TypeMismatch { expected = "Int"; got = m_tpe }))

  (** Check arguments against expected types *)
  and check_args (ctx : ctx) (args : Fun.term list) (expected : Fun.tpe list) : unit result =
    if List.length args <> List.length expected then
      Error (ArityMismatch { expected = List.length expected; got = List.length args })
    else
      List.fold_left2 (fun acc arg exp ->
        let* () = acc in
        let* got = infer ctx arg in
        if got = exp then Ok ()
        else Error (TypeMismatch { expected = "matching type"; got })
      ) (Ok ()) args expected

  (** Infer common return type from case clauses *)
  and infer_clauses (ctx : ctx) (sgn : Fun.signature) (clauses : Fun.clause list) 
      : Fun.tpe result =
    if List.length clauses <> List.length sgn then
      Error (ArityMismatch { expected = List.length sgn; got = List.length clauses })
    else
      match clauses with
      | [] -> failwith "Case must have at least one clause"
      | (params, body) :: rest ->
          let param_tpes = List.hd sgn in
          if List.length params <> List.length param_tpes then
            Error (ArityMismatch { expected = List.length param_tpes; got = List.length params })
          else
            let ctx' = List.fold_left2 (fun c p t -> Ident.add p t c) ctx params param_tpes in
            let* first_tpe = infer ctx' body in
            let* _ = check_rest_clauses ctx (List.tl sgn) rest first_tpe in
            Ok first_tpe

  (** Check remaining clauses return the same type *)
  and check_rest_clauses (ctx : ctx) (sgn : Fun.signature) (clauses : Fun.clause list) 
      (expected : Fun.tpe) : unit result =
    match clauses, sgn with
    | [], [] -> Ok ()
    | (params, body) :: rest, ctor_tpes :: rest_sgn ->
        if List.length params <> List.length ctor_tpes then
          Error (ArityMismatch { expected = List.length ctor_tpes; got = List.length params })
        else
          let ctx' = List.fold_left2 (fun c p t -> Ident.add p t c) ctx params ctor_tpes in
          let* got = infer ctx' body in
          if got = expected then check_rest_clauses ctx rest_sgn rest expected
          else Error (TypeMismatch { expected = "same return type"; got })
    | _ -> Error (ArityMismatch { expected = List.length sgn; got = List.length clauses })

  (** Check cocase clauses (destructors) *)
  and check_cocase_clauses (ctx : ctx) (sgn : Fun.signature) (clauses : Fun.clause list) 
      : unit result =
    if List.length clauses <> List.length sgn then
      Error (ArityMismatch { expected = List.length sgn; got = List.length clauses })
    else
      List.fold_left2 (fun acc (params, body) dtor_tpes ->
        let* () = acc in
        (* dtor_tpes = [arg1; ...; argN; result] - params bind all including result *)
        if List.length params <> List.length dtor_tpes then
          Error (ArityMismatch { expected = List.length dtor_tpes; got = List.length params })
        else
          let ctx' = List.fold_left2 (fun c p t -> Ident.add p t c) ctx params dtor_tpes in
          let result_tpe = List.nth dtor_tpes (List.length dtor_tpes - 1) in
          let* body_tpe = infer ctx' body in
          if body_tpe = result_tpe then Ok ()
          else Error (TypeMismatch { expected = "destructor result type"; got = body_tpe })
      ) (Ok ()) clauses sgn

  (* ========================================================================= *)
  (* Term Encoding                                                             *)
  (* ========================================================================= *)

  (** Helper to get result type, failing on error *)
  let infer_exn (ctx : ctx) (term : Fun.term) : Fun.tpe =
    match infer ctx term with
    | Ok t -> t
    | Error _ -> failwith "Type inference failed in encode_term"

  (** Encode a Fun term as a Source term.
      
      The encoding is "term-style" where terms encode to terms.
      To run a term against a continuation, use a cut.
      
      Key encodings:
      - Var x → Variable x
      - Lam(x, t, body) → Comatch { apply(x, k) ⇒ ⟨body | k⟩ }
      - App(f, arg) → μα.⟨f | apply(arg, α)⟩  (but we need to handle polarity)
      - Ctor(sig, n, args) → Constructor(sig', n, args')
      - Dtor(sig, n, [subj; args...]) → μα.⟨subj | Dₙ(args..., α)⟩
      - Case(sig, scrut, clauses) → μα.⟨scrut | case { ... }⟩
      - Cocase(sig, clauses) → Comatch { ... }
  *)
  let rec encode_term (ctx : ctx) (term : Fun.term) : Source.term =
    match term with
    | Fun.Var x -> Source.Variable x

    | Fun.Lam (x, t, body) ->
        (* λx:t. body  →  cocase { apply(x, k) ⇒ ⟨body | k⟩ }
           Function types have shape Fun(+, -):-, so negative args must be raised *)
        let ctx' = Ident.add x t ctx in
        let body_tpe = infer_exn ctx' body in
        let a' = encode_tpe t in
        let b' = encode_tpe body_tpe in
        (* Determine the codomain - only lower positive results (Int is positive) *)
        let codomain = match b' with
          | Neg _ -> b'
          | Pos _ | Int -> lower_tpe b'
        in
        (* Raise negative arg types to match function type convention (Int is positive) *)
        let arg_in_sig = match a' with Neg _ -> raise_tpe a' | Pos _ | Int -> a' in
        let fun_sig = [[Lhs arg_in_sig; Rhs codomain]] in
        let k = Ident.fresh () in
        let body' = encode_term ctx' body in
        (* If arg was raised, we need to unwrap it. Bind a wrapper variable. *)
        let (wrapper_var, unwrap_body) = match a' with
          | Pos _ | Int -> 
              (* No unwrapping needed, x is directly usable *)
              (x, fun cmd -> cmd)
          | Neg _ ->
              (* x is bound at type raise_tpe(Neg sig) = Pos [[Lhs (Neg sig)]]
                 We need to case on x to get the actual function out.
                 But since the user code uses x directly, we need to rebind.
                 Let x_wrapped be the raised value, and extract x from it. *)
              let x_wrapped = Ident.fresh () in
              let raised_sig = [[Lhs a']] in
              (x_wrapped, fun cmd ->
                (* ⟨x_wrapped | case { C(x) ⇒ cmd }⟩ *)
                Source.CutPos (raised_sig, Source.Variable x_wrapped,
                  Source.Match (raised_sig, [Source.Clause ([x], cmd)])))
        in
        (* If the body was lowered, we need to wrap it in a thunk *)
        let body_cmd = match b' with
          | Neg _ -> 
              (* No wrapping - body is already negative, cut directly *)
              unwrap_body (cut_term ctx' body body' (Source.Variable k))
          | Int ->
              (* Int result - lower it and wrap *)
              let lowered_sig = [[Rhs b']] in
              let ret = Ident.fresh () in
              let r = Ident.fresh () in
              unwrap_body (Source.CutInt (body',
                Source.MuInt (ret,
                  Source.CutNeg (lowered_sig,
                    Source.Comatch (lowered_sig, [Source.Clause ([r], 
                      Source.CutInt (Source.Variable ret, Source.Variable r))]),
                    Source.Variable k))))
          | Pos body_sig ->
              (* Body is positive but codomain is Neg (lowered) - wrap in destructor *)
              let lowered_sig = [[Rhs b']] in
              let ret = Ident.fresh () in
              let r = Ident.fresh () in
              unwrap_body (Source.CutPos (body_sig, body',
                Source.MuRhsPos (body_sig, ret,
                  Source.CutNeg (lowered_sig,
                    Source.Comatch (lowered_sig, [Source.Clause ([r], 
                      Source.CutPos (body_sig, Source.Variable ret, Source.Variable r))]),
                    Source.Variable k))))
        in
        Source.Comatch (fun_sig, [Source.Clause ([wrapper_var; k], body_cmd)])

    | Fun.App (f, arg) ->
        (* f arg  →  depends on polarity of result type *)
        let f_tpe = infer_exn ctx f in
        let (_, result_tpe) = 
          match f_tpe with 
          | Fun.Fun (a, b) -> (a, b) 
          | _ -> failwith "App of non-function" 
        in
        let f' = encode_term ctx f in
        let arg' = encode_term ctx arg in
        let result_tpe' = encode_tpe result_tpe in
        let arg_tpe = 
          match f_tpe with Fun.Fun (a, _) -> a | _ -> failwith "impossible" 
        in
        let arg_tpe' = encode_tpe arg_tpe in
        (* Build the destructor - must match function type convention Fun(+, -) *)
        let codomain = match result_tpe' with
          | Neg _ -> result_tpe'
          | Pos _ | Int -> lower_tpe result_tpe'
        in
        (* Raise negative arg types to match function type convention *)
        let arg_in_sig = match arg_tpe' with Neg _ -> raise_tpe arg_tpe' | Pos _ | Int -> arg_tpe' in
        let fun_sig = [[Lhs arg_in_sig; Rhs codomain]] in
        (* Wrap arg if needed for the raised type *)
        let wrapped_arg = wrap_for_lhs_tpe arg' arg_tpe' in
        (* μα.⟨f | apply(arg, α)⟩ but we need to handle polarity shifts *)
        (match result_tpe' with
        | Neg neg_sig ->
            (* Result is negative, use MuLhsNeg *)
            let alpha = Ident.fresh () in
            let dtor_args = [wrapped_arg; Source.Variable alpha] in
            Source.MuLhsNeg (neg_sig, alpha,
              Source.CutNeg (fun_sig, f', Source.Destructor (fun_sig, 0, dtor_args)))
        | Int ->
            (* Result is Int, use MuInt *)
            let lowered_sig = [[Rhs result_tpe']] in
            let ret = Ident.fresh () in
            let thunk = Ident.fresh () in
            let dtor_args = [wrapped_arg; 
              Source.MuRhsNeg (lowered_sig, thunk,
                Source.CutNeg (lowered_sig, Source.Variable thunk,
                  Source.Destructor (lowered_sig, 0, [Source.Variable ret])))] in
            Source.MuInt (ret,
              Source.CutNeg (fun_sig, f', Source.Destructor (fun_sig, 0, dtor_args)))
        | Pos pos_sig ->
            (* Result is positive, but fun_sig has lowered result.
               The destructor returns a Neg thunk, we need to force it.
               μret.⟨f | apply(arg, μ̃thunk.⟨thunk | force(ret)⟩)⟩ *)
            let lowered_sig = [[Rhs result_tpe']] in
            let ret = Ident.fresh () in
            let thunk = Ident.fresh () in
            let dtor_args = [wrapped_arg; 
              Source.MuRhsNeg (lowered_sig, thunk,
                Source.CutNeg (lowered_sig, Source.Variable thunk,
                  Source.Destructor (lowered_sig, 0, [Source.Variable ret])))] in
            Source.MuLhsPos (pos_sig, ret,
              Source.CutNeg (fun_sig, f', Source.Destructor (fun_sig, 0, dtor_args))))

    | Fun.Ctor (sgn, n, args) ->
        let sgn' = encode_data_sgn sgn in
        let args' = List.map (encode_term ctx) args in
        (* Need to wrap args if they're negative *)
        let ctor_tpes = List.nth sgn n in
        let wrapped_args = List.map2 (fun arg' arg_tpe ->
          wrap_for_lhs_tpe arg' (encode_tpe arg_tpe)
        ) args' ctor_tpes in
        Source.Constructor (sgn', n, wrapped_args)

    | Fun.Dtor (sgn, n, args) ->
        (* args = [subject; arg1; ...; argN] *)
        (match args with
        | [] -> failwith "Destructor must have subject"
        | subj :: rest_args ->
            let sgn' = encode_code_sgn sgn in
            let subj' = encode_term ctx subj in
            let rest_args' = List.map (encode_term ctx) rest_args in
            let dtor_tpes = List.nth sgn n in
            (* dtor_tpes = [arg1_tpe; ...; argN_tpe; result_tpe] *)
            let (arg_tpes, result_tpe) = 
              match List.rev dtor_tpes with
              | [] -> failwith "Destructor needs result type"
              | r :: rest -> (List.rev rest, r)
            in
            let result_tpe' = encode_tpe result_tpe in
            (* Wrap arguments for Lhs *)
            let wrapped_args = List.map2 (fun arg' arg_tpe ->
              wrap_for_lhs_tpe arg' (encode_tpe arg_tpe)
            ) rest_args' arg_tpes in
            (match result_tpe' with
            | Neg _ ->
                let alpha = Ident.fresh () in
                let dtor_args = wrapped_args @ [Source.Variable alpha] in
                Source.MuLhsNeg (sgn', alpha,
                  Source.CutNeg (sgn', subj', Source.Destructor (sgn', n, dtor_args)))
            | Int ->
                let alpha = Ident.fresh () in
                let dtor_args = wrapped_args @ [Source.Variable alpha] in
                Source.MuInt (alpha,
                  Source.CutNeg (sgn', subj', Source.Destructor (sgn', n, dtor_args)))
            | Pos _ ->
                let lowered_sig = [[Rhs result_tpe']] in
                let alpha = Ident.fresh () in
                let dtor_args = wrapped_args @ [Source.Variable alpha] in
                Source.MuLhsPos (lowered_sig, alpha,
                  Source.CutNeg (sgn', subj', Source.Destructor (sgn', n, dtor_args)))))

    | Fun.Case (sgn, scrut, clauses) ->
        let sgn' = encode_data_sgn sgn in
        let scrut' = encode_term ctx scrut in
        let result_tpe = infer_exn ctx term in
        let result_tpe' = encode_tpe result_tpe in
        (* μα.⟨scrut | case { ... }⟩ - bind alpha first so branches can use it *)
        let alpha = Ident.fresh () in
        (* Build match branches - all branches return to the same alpha *)
        let branches = List.map2 (fun (params, body) ctor_tpes ->
          let ctx' = List.fold_left2 (fun c p t -> Ident.add p t c) ctx params ctor_tpes in
          let body' = encode_term ctx' body in
          Source.Clause (params, cut_term ctx' body body' (Source.Variable alpha))
        ) clauses sgn in
        (match result_tpe' with
        | Pos _ ->
            Source.MuLhsPos (sgn', alpha,
              Source.CutPos (sgn', scrut', Source.Match (sgn', branches)))
        | Int ->
            Source.MuInt (alpha,
              Source.CutPos (sgn', scrut', Source.Match (sgn', branches)))
        | Neg _ ->
            Source.MuLhsNeg (sgn', alpha,
              Source.CutPos (sgn', scrut', Source.Match (sgn', branches))))

    | Fun.Cocase (sgn, clauses) ->
        let sgn' = encode_code_sgn sgn in
        (* Build comatch branches *)
        let branches = List.map2 (fun (params, body) dtor_tpes ->
          (* params bind [arg1; ...; argN; k] where k is the result continuation *)
          let ctx' = List.fold_left2 (fun c p t -> Ident.add p t c) ctx params dtor_tpes in
          let body' = encode_term ctx' body in
          let k = List.nth params (List.length params - 1) in
          Source.Clause (params, cut_term ctx' body body' (Source.Variable k))
        ) clauses sgn in
        Source.Comatch (sgn', branches)

    | Fun.Lit n -> Source.Lit n

    | Fun.Add (m, n) ->
        (* add(m, n) → μα.add(m, n, α) where α binds the result *)
        let m' = encode_term ctx m in
        let n' = encode_term ctx n in
        let alpha = Ident.fresh () in
        Source.MuInt (alpha, Source.Add (m', n', Source.Variable alpha))

  (** Create a cut between a term and a continuation, handling polarity *)
  and cut_term (ctx : ctx) (orig : Fun.term) (lhs : Source.term) (rhs : Source.term) 
      : Source.command =
    let tpe = infer_exn ctx orig in
    let tpe' = encode_tpe tpe in
    match tpe' with
    | Int -> Source.CutInt (lhs, rhs)
    | Pos sgn -> Source.CutPos (sgn, lhs, rhs)
    | Neg sgn -> Source.CutNeg (sgn, lhs, rhs)

  (** Wrap a term for use in Lhs position based on encoded type *)
  and wrap_for_lhs_tpe (term : Source.term) (tpe : tpe) : Source.term =
    match tpe with
    | Int -> term
    | Pos _ -> term
    | Neg _ -> 
        let raised_sig = [[Lhs tpe]] in
        Source.Constructor (raised_sig, 0, [term])
  
end


(* ========================================================================= *)
(* Target Language                                                           *)
(* ========================================================================= *)

module Target = struct

  type command =
    | LetConstructor of signature * int * Ident.t list * Ident.t * command  (** [⟨Cₙ(Γ) | μ̃x.s⟩] *)
    | LetMatch of signature * branch list * Ident.t * command  (** [⟨μα.s | case \{C₁(Γ₁) ⇒ s₁; …\}⟩] *)
    | LetComatch of signature * branch list * Ident.t * command  (** [⟨cocase \{D₁(Γ₁) ⇒ s₁; …\} | μ̃x.s⟩] *)
    | LetDestructor of signature * int * Ident.t list * Ident.t * command  (** [⟨μα.s | Dₙ(Γ)⟩] *)
    | LetInt of int * Ident.t * command  (** [⟨n | μ̃ⁱx.s⟩] - let x = n in s *)
    | CutConstructor of signature * int * Ident.t list * Ident.t  (** [⟨Cₙ(Γ) | α⟩] *)
    | CutMatch of signature * Ident.t * branch list  (** [⟨x | case \{C₁(Γ₁) ⇒ s₁; …\}⟩] *)
    | CutComatch of signature * branch list * Ident.t  (** [⟨cocase \{D₁(Γ₁) ⇒ s₁; …\} | α⟩] *)
    | CutDestructor of signature * Ident.t * int * Ident.t list  (** [⟨x | Dₙ(Γ)⟩] *)
    | CutInt of Ident.t * Ident.t  (** [⟨x | α⟩ⁱ] - return integer variable *)
    | Add of Ident.t * Ident.t * Ident.t * command  (** add(x, y, k, cont) *)
    | Ret of signature * Ident.t  (** Return a value *)
    | RetInt of Ident.t  (** Return an integer *)
    | End  (** Terminal / halt *)

  and branch = Clause of Ident.t list * command

  (** Apply renaming to a command *)
  let rec rename_command (h : Sub.t) : command -> command = function
    | LetConstructor (sgn, n, args, x, cont) ->
        let x' = Ident.fresh () in
        LetConstructor (sgn, n, List.map (Sub.apply h) args, x',
          rename_command (Sub.add x x' h) cont)
    | LetMatch (sgn, branches, x, cont) ->
        let x' = Ident.fresh () in
        LetMatch (sgn, List.map (rename_branch h) branches, x',
          rename_command (Sub.add x x' h) cont)
    | LetComatch (sgn, branches, a, cont) ->
        let a' = Ident.fresh () in
        LetComatch (sgn, List.map (rename_branch h) branches, a',
          rename_command (Sub.add a a' h) cont)
    | LetDestructor (sgn, n, args, a, cont) ->
        let a' = Ident.fresh () in
        LetDestructor (sgn, n, List.map (Sub.apply h) args, a',
          rename_command (Sub.add a a' h) cont)
    | CutConstructor (sgn, n, args, a) ->
        CutConstructor (sgn, n, List.map (Sub.apply h) args, Sub.apply h a)
    | CutMatch (sgn, x, branches) ->
        CutMatch (sgn, Sub.apply h x, List.map (rename_branch h) branches)
    | CutComatch (sgn, branches, a) ->
        CutComatch (sgn, List.map (rename_branch h) branches, Sub.apply h a)
    | CutDestructor (sgn, x, n, args) ->
        CutDestructor (sgn, Sub.apply h x, n, List.map (Sub.apply h) args)
    | LetInt (n, x, cont) ->
        let x' = Ident.fresh () in
        LetInt (n, x', rename_command (Sub.add x x' h) cont)
    | CutInt (x, a) -> CutInt (Sub.apply h x, Sub.apply h a)
    | Add (x, y, k, cont) ->
        let k' = Ident.fresh () in
        Add (Sub.apply h x, Sub.apply h y, k', rename_command (Sub.add k k' h) cont)
    | Ret (sgn, x) -> Ret (sgn, Sub.apply h x)
    | RetInt x -> RetInt (Sub.apply h x)
    | End -> End

  and rename_branch (h : Sub.t) (Clause (params, body)) : branch =
    let params' = List.map (fun _ -> Ident.fresh ()) params in
    let h' = List.fold_left2 (fun acc p p' -> Sub.add p p' acc) h params params' in
    Clause (params', rename_command h' body)
end

(* ========================================================================= *)
(* Transformation                                                            *)
(* ========================================================================= *)

module Transform = struct
  open Source

  (** Generate fresh parameter names from a parameter spec *)
  let fresh_params (ps : 'a list) : Ident.t list =
    List.map (fun _ -> Ident.fresh ()) ps

  (** Lookup and inline the n-th branch body, substituting arg_vars for params *)
  let lookup_branch_body (branches : Target.branch list) (n : int) 
      (arg_vars : Ident.t list) : Target.command =
    match List.nth_opt branches n with
    | Some (Target.Clause (params, body)) ->
        let sub = List.fold_left2 (fun acc p v -> Sub.add p v acc) 
                    Sub.empty params arg_vars in
        Target.rename_command sub body
    | None -> Target.End

  (** Build target branches from a signature using a builder function *)
  let build_branches_from_sig (sgn : signature) 
      (build : Ident.t list -> int -> Target.command) : Target.branch list =
    List.mapi (fun idx ps ->
      let params = fresh_params ps in
      Target.Clause (params, build params idx)
    ) sgn

  (** Transform source branches to target branches *)
  let rec transform_source_branches (branches : Source.branch list) 
      (h : Sub.t) : Target.branch list =
    List.map (fun (Clause (params, body)) ->
      let params' = fresh_params params in
      let h' = List.fold_left2 (fun acc p p' -> Sub.add p p' acc) h params params' in
      Target.Clause (params', transform_command body h')
    ) branches

  (** Bind a single term, calling continuation with the resulting variable *)
  and bind_term (term : Source.term) (h : Sub.t) 
      (k : Ident.t -> Target.command) : Target.command =
    match term with
    | Variable x -> 
        k (Sub.apply h x)

    | Constructor (sgn, n, args) ->
        bind_terms args h (fun arg_vars ->
          let x = Ident.fresh () in
          Target.LetConstructor (sgn, n, arg_vars, x, k x))

    | Match (sgn, bs) ->
        let x = Ident.fresh () in
        Target.LetMatch (sgn, transform_source_branches bs h, x, k x)

    | Comatch (sgn, bs) ->
        let a = Ident.fresh () in
        Target.LetComatch (sgn, transform_source_branches bs h, a, k a)

    | Destructor (sgn, n, args) ->
        bind_terms args h (fun arg_vars ->
          let a = Ident.fresh () in
          Target.LetDestructor (sgn, n, arg_vars, a, k a))

    | MuLhsPos (sgn, x, s) ->
        let bound = Ident.fresh () in
        Target.LetMatch (sgn,
          build_branches_from_sig sgn (fun params n ->
            Target.LetConstructor (sgn, n, params, bound, k bound)),
          x,
          transform_command s (Sub.add x x h))

    | MuRhsPos (sgn, a, s) ->
        let bound = Ident.fresh () in
        Target.LetMatch (sgn,
          build_branches_from_sig sgn (fun params n ->
            let a' = Ident.fresh () in
            Target.LetConstructor (sgn, n, params, a',
              transform_command s (Sub.add a a' h))),
          bound,
          k bound)

    | MuLhsNeg (sgn, a, s) ->
        let bound = Ident.fresh () in
        Target.LetComatch (sgn,
          build_branches_from_sig sgn (fun params n ->
            let a' = Ident.fresh () in
            Target.LetDestructor (sgn, n, params, a',
              transform_command s (Sub.add a a' h))),
          bound,
          k bound)

    | MuRhsNeg (sgn, x, s) ->
        let bound = Ident.fresh () in
        Target.LetComatch (sgn,
          build_branches_from_sig sgn (fun params n ->
            Target.LetDestructor (sgn, n, params, bound, k bound)),
          x,
          transform_command s (Sub.add x x h))

    | Lit n ->
        let x = Ident.fresh () in
        Target.LetInt (n, x, k x)

    | MuInt (x, s) ->
        (* MuInt(x, s) as a term means "execute s, which will produce a value into x"
           We transform s and replace any RetInt with the continuation k *)
        let x' = Ident.fresh () in
        let transformed_s = transform_command s (Sub.add x x' h) in
        (* Now we need to replace RetInt(v) in transformed_s with k(v) *)
        let rec replace_retint cmd =
          match cmd with
          | Target.RetInt v -> k v
          | Target.LetInt (n, v, cont) -> Target.LetInt (n, v, replace_retint cont)
          | Target.Add (m, n, r, cont) -> Target.Add (m, n, r, replace_retint cont)
          | Target.CutInt (v, a) ->
              (* CutInt at the end means we're returning v to continuation a.
                 If a = x' (our result variable), then we should call k(v) *)
              if a = x' then k v
              else Target.CutInt (v, a)
          | Target.LetConstructor (sgn, n, args, x, cont) ->
              Target.LetConstructor (sgn, n, args, x, replace_retint cont)
          | Target.LetMatch (sgn, bs, x, cont) ->
              Target.LetMatch (sgn, List.map (replace_retint_branch) bs, x, replace_retint cont)
          | Target.LetComatch (sgn, bs, x, cont) ->
              Target.LetComatch (sgn, List.map (replace_retint_branch) bs, x, replace_retint cont)
          | Target.LetDestructor (sgn, n, args, x, cont) ->
              Target.LetDestructor (sgn, n, args, x, replace_retint cont)
          | _ -> cmd
        and replace_retint_branch (Target.Clause (params, body)) =
          Target.Clause (params, replace_retint body)
        in
        replace_retint transformed_s

  (** Bind multiple terms, calling continuation with the resulting variables *)
  and bind_terms (terms : Source.term list) (h : Sub.t)
      (k : Ident.t list -> Target.command) : Target.command =
    match terms with
    | [] -> k []
    | t :: rest ->
        bind_term t h (fun v ->
          bind_terms rest h (fun vs -> k (v :: vs)))

  (** Main transformation function *)
  and transform_command (cmd : Source.command) (h : Sub.t) : Target.command =
    match cmd with
    | CutPos (sgn, Variable x, Variable y) ->
        Target.CutMatch (sgn, Sub.apply h x,
          build_branches_from_sig sgn (fun params n ->
            Target.CutConstructor (sgn, n, params, Sub.apply h y)))

    | CutPos (sgn, Variable x, Match (_, bs)) ->
        Target.CutMatch (sgn, Sub.apply h x, transform_source_branches bs h)

    | CutPos (_, Variable x, MuRhsPos (_, a, r)) ->
        transform_command r (Sub.add a (Sub.apply h x) h)

    | CutPos (sgn, Constructor (_, n, args), Variable y) ->
        bind_terms args h (fun arg_vars ->
          Target.CutConstructor (sgn, n, arg_vars, Sub.apply h y))

    | CutPos (_, Constructor (_, n, args), Match (_, bs)) ->
        bind_terms args h (fun arg_vars ->
          let branches = transform_source_branches bs h in
          lookup_branch_body branches n arg_vars)

    | CutPos (sgn, Constructor (_, n, args), MuRhsPos (_, a, r)) ->
        bind_terms args h (fun arg_vars ->
          let a' = Ident.fresh () in
          Target.LetConstructor (sgn, n, arg_vars, a',
            transform_command r (Sub.add a a' h)))

    | CutPos (_, MuLhsPos (_, x, s), Variable y) ->
        transform_command s (Sub.add x (Sub.apply h y) h)

    | CutPos (sgn, MuLhsPos (_, x, s), Match (_, bs)) ->
        let x' = Ident.fresh () in
        Target.LetMatch (sgn, transform_source_branches bs h, x',
          transform_command s (Sub.add x x' h))

    | CutPos (sgn, MuLhsPos (_, x, s), MuRhsPos (_, a, r)) ->
        let x' = Ident.fresh () in
        Target.LetMatch (sgn,
          build_branches_from_sig sgn (fun params n ->
            let a' = Ident.fresh () in
            Target.LetConstructor (sgn, n, params, a',
              transform_command r (Sub.add a a' h))),
          x',
          transform_command s (Sub.add x x' h))

    | CutNeg (sgn, Variable x, Variable y) ->
        Target.CutComatch (sgn,
          build_branches_from_sig sgn (fun params n ->
            Target.CutDestructor (sgn, Sub.apply h x, n, params)),
          Sub.apply h y)

    | CutNeg (sgn, Variable x, Destructor (_, n, args)) ->
        bind_terms args h (fun arg_vars ->
          Target.CutDestructor (sgn, Sub.apply h x, n, arg_vars))

    | CutNeg (_, Variable x, MuRhsNeg (_, a, r)) ->
        transform_command r (Sub.add a (Sub.apply h x) h)

    | CutNeg (sgn, Comatch (_, bs), Variable y) ->
        Target.CutComatch (sgn, transform_source_branches bs h, Sub.apply h y)

    | CutNeg (_, Comatch (_, bs), Destructor (_, n, args)) ->
        bind_terms args h (fun arg_vars ->
          let branches = transform_source_branches bs h in
          lookup_branch_body branches n arg_vars)

    | CutNeg (sgn, Comatch (_, bs), MuRhsNeg (_, a, r)) ->
        let a' = Ident.fresh () in
        Target.LetComatch (sgn, transform_source_branches bs h, a',
          transform_command r (Sub.add a a' h))

    | CutNeg (_, MuLhsNeg (_, x, s), Variable y) ->
        transform_command s (Sub.add x (Sub.apply h y) h)

    | CutNeg (sgn, MuLhsNeg (_, x, s), Destructor (_, n, args)) ->
        bind_terms args h (fun arg_vars ->
          let x' = Ident.fresh () in
          Target.LetDestructor (sgn, n, arg_vars, x',
            transform_command s (Sub.add x x' h)))

    | CutNeg (sgn, MuLhsNeg (_, x, s), MuRhsNeg (_, a, r)) ->
        let a' = Ident.fresh () in
        Target.LetComatch (sgn,
          build_branches_from_sig sgn (fun params n ->
            let x' = Ident.fresh () in
            Target.LetDestructor (sgn, n, params, x',
              transform_command s (Sub.add x x' h))),
          a',
          transform_command r (Sub.add a a' h))

    | Ret (sgn, x) -> Target.Ret (sgn, Sub.apply h x)
    | RetInt x -> Target.RetInt (Sub.apply h x)
    | End -> Target.End

    (* Int operations *)
    | CutInt (Lit n, MuInt (x, s)) ->
        let x' = Ident.fresh () in
        Target.LetInt (n, x', transform_command s (Sub.add x x' h))

    | CutInt (Lit n, Variable a) ->
        let x = Ident.fresh () in
        Target.LetInt (n, x, Target.CutInt (x, Sub.apply h a))

    | CutInt (Variable x, Variable a) ->
        Target.CutInt (Sub.apply h x, Sub.apply h a)

    | CutInt (Variable x, MuInt (k, s)) ->
        transform_command s (Sub.add k (Sub.apply h x) h)

    | CutInt (MuInt (x, s), Variable _a) ->
        let x' = Ident.fresh () in
        Target.LetInt (0, x',  (* placeholder, will be overwritten *)
          transform_command s (Sub.add x x' h))

    | CutInt (MuInt (x, s), MuInt (a, r)) ->
        (* ⟨μⁱx.s | μⁱa.r⟩ⁱ 
           The LHS produces an int to x, RHS consumes it at a.
           We create a consumer for x that, when invoked with a value,
           binds a to that value and runs r.
           This becomes: new x' = { (v) => r[a↦v] }; s[x↦x'] *)
        let x' = Ident.fresh () in
        let v = Ident.fresh () in
        (* The consumer has one branch that binds the int value to v,
           then runs r with a substituted to v *)
        let r' = transform_command r (Sub.add a v h) in
        let branch = Target.Clause ([v], r') in
        (* Create the consumer and then run the body *)
        let body = transform_command s (Sub.add x x' h) in
        (* The consumer needs a signature - for Int, we use [[Lhs Int]] meaning one "constructor" taking an int *)
        let int_sig = [[Lhs Int]] in
        Target.LetMatch (int_sig, [branch], x', body)

    | Add (m, n, k) ->
        bind_term m h (fun m_var ->
          bind_term n h (fun n_var ->
            bind_term k h (fun k_var ->
              let res = Ident.fresh () in
              Target.Add (m_var, n_var, res,
                Target.CutInt (res, k_var)))))

    | CutPos (_, _, _) -> 
        failwith "ill-typed: CutPos requires (Variable|Constructor|MuLhsPos) on LHS and (Variable|Match|MuRhsPos) on RHS"
    | CutNeg (_, _, _) -> 
        failwith "ill-typed: CutNeg requires (Variable|Comatch|MuLhsNeg) on LHS and (Variable|Destructor|MuRhsNeg) on RHS"
    | CutInt (_, _) ->
        failwith "ill-typed: CutInt requires (Lit|Variable|MuInt) on LHS and (Variable|MuInt) on RHS"
end

(* ========================================================================= *)
(* Collapsed Language                                                        *)
(* ========================================================================= *)

module Collapsed = struct

  (* Collapsed language makes no distinction between positive (data) and negative (codata) types *)
  type signature = chiral_tpe list list

  and chiral_tpe =
    | Lhs of signature (* prd *)
    | Rhs of signature (* cns *)

  type command =
    | Let of signature * int * Ident.t list * Ident.t * command  (** [⟨Cₙ(Γ) | μ̃x.s⟩] or [⟨μα.s | Dₙ(Γ)⟩] *)
    | Switch of signature * Ident.t * branch list  (** [⟨x | case \{C₁(Γ₁) ⇒ s₁; …\}⟩] or [⟨cocase \{D₁(Γ₁) ⇒ s₁; …\} | α⟩] *)
    | New of signature * branch list * Ident.t * command (* [⟨cocase \{D₁(Γ₁) ⇒ s₁; …\} | μ̃x.s⟩] or [⟨μα.s | case \{C₁(Γ₁) ⇒ s₁; …\}⟩] *)
    | Invoke of signature * int * Ident.t list * Ident.t  (** [⟨Cₙ(Γ) | α⟩] or [⟨x | Dₙ(Γ)⟩] *)
    | LetInt of int * Ident.t * command  (** let x = n in s *)
    | Add of Ident.t * Ident.t * Ident.t * command  (** add(x, y, k, cont) *)
    | CutInt of Ident.t * Ident.t  (** [⟨x | k⟩ⁱ] - pass int to continuation *)
    | Ret of signature * Ident.t  (** Return a value *)
    | RetInt of Ident.t  (** Return an integer *)
    | End  (** Terminal / halt *)

  and branch = Clause of Ident.t list * command

  (* ========================================================================= *)
  (* Type Checking                                                             *)
  (* ========================================================================= *)

  (** Type checking context: maps variables to their chiral types *)
  type ctx = chiral_tpe Ident.tbl

  (** Type checking errors *)
  type error =
    | UnboundVariable of Ident.t
    | ChiralityMismatch of { var: Ident.t; expected: string; got: chiral_tpe }
    | ArityMismatch of { xtor: int; expected: int; got: int }
    | XtorOutOfBounds of { xtor: int; sgnsize: int }
    | NonExhaustive of { expected: int; got: int }

  let show_chiral = function
    | Lhs _ -> "Lhs"
    | Rhs _ -> "Rhs"

  let show_error = function
    | UnboundVariable v -> 
        Printf.sprintf "Unbound variable: %s" (Ident.name v)
    | ChiralityMismatch { var; expected; got } ->
        Printf.sprintf "Chirality mismatch for %s: expected %s, got %s" 
          (Ident.name var) expected (show_chiral got)
    | ArityMismatch { xtor; expected; got } ->
        Printf.sprintf "Arity mismatch for xtor %d: expected %d args, got %d" 
          xtor expected got
    | XtorOutOfBounds { xtor; sgnsize } ->
        Printf.sprintf "Xtor index %d out of bounds (signature has %d xtors)" 
          xtor sgnsize
    | NonExhaustive { expected; got } ->
        Printf.sprintf "Non-exhaustive branches: expected %d, got %d" 
          expected got

  (** Show functions for debugging *)
  let show_signature sgn =
    let show_ctor chiral_tpes = 
      Printf.sprintf "[%s]" (String.concat ", " (List.map show_chiral chiral_tpes)) 
    in
    Printf.sprintf "[%s]" (String.concat "; " (List.map show_ctor sgn))

  let rec show_command = function
    | Let (_, n, args, x, cont) ->
        Printf.sprintf "let %s = C%d(%s);\n  %s" 
          (Ident.name x) n 
          (String.concat ", " (List.map Ident.name args))
          (show_command cont)
    | Switch (_, v, branches) ->
        Printf.sprintf "switch %s {\n  %s\n}" 
          (Ident.name v)
          (String.concat "\n  " (List.mapi (fun i b -> Printf.sprintf "C%d%s" i (show_branch b)) branches))
    | New (_, branches, x, cont) ->
        Printf.sprintf "new %s = {\n  %s\n};\n  %s" 
          (Ident.name x)
          (String.concat "\n  " (List.mapi (fun i b -> Printf.sprintf "D%d%s" i (show_branch b)) branches))
          (show_command cont)
    | Invoke (_, n, args, v) ->
        Printf.sprintf "invoke %s.D%d(%s)" 
          (Ident.name v) n 
          (String.concat ", " (List.map Ident.name args))
    | LetInt (n, x, cont) ->
        Printf.sprintf "let %s = %d;\n  %s"
          (Ident.name x) n (show_command cont)
    | Add (x, y, k, cont) ->
        Printf.sprintf "let %s = add(%s, %s);\n  %s"
          (Ident.name k) (Ident.name x) (Ident.name y) (show_command cont)
    | CutInt (x, k) ->
        Printf.sprintf "⟨%s | %s⟩ⁱ" (Ident.name x) (Ident.name k)
    | Ret (_, x) -> Printf.sprintf "ret %s" (Ident.name x)
    | RetInt x -> Printf.sprintf "ret %s" (Ident.name x)
    | End -> "end"

  and show_branch (Clause (params, body)) =
    Printf.sprintf "(%s) => %s" 
      (String.concat ", " (List.map Ident.name params))
      (show_command body)

  type 'a check_result = ('a, error) result
  let ( let* ) = Result.bind

  (** Lookup a variable in the context *)
  let lookup (ctx : ctx) (v : Ident.t) : chiral_tpe check_result =
    match Ident.find_opt v ctx with
    | Some ct -> Ok ct
    | None -> Error (UnboundVariable v)

  (** Expect a variable to be Lhs (producer) *)
  let expect_lhs (ctx : ctx) (v : Ident.t) : signature check_result =
    let* ct = lookup ctx v in
    match ct with
    | Lhs sgn -> Ok sgn
    | Rhs _ -> Error (ChiralityMismatch { var = v; expected = "Lhs"; got = ct })

  (** Expect a variable to be Rhs (consumer) *)
  let expect_rhs (ctx : ctx) (v : Ident.t) : signature check_result =
    let* ct = lookup ctx v in
    match ct with
    | Rhs sgn -> Ok sgn
    | Lhs _ -> Error (ChiralityMismatch { var = v; expected = "Rhs"; got = ct })

  (** Get the parameter types for an xtor *)
  let get_xtor_params (sgn : signature) (n : int) : chiral_tpe list check_result =
    if n < 0 || n >= List.length sgn then
      Error (XtorOutOfBounds { xtor = n; sgnsize = List.length sgn })
    else
      Ok (List.nth sgn n)

  (** Extend context with branch parameters *)
  let extend_with_params (ctx : ctx) (params : Ident.t list) (param_types : chiral_tpe list) : ctx =
    List.fold_left2 (fun acc p pt -> Ident.add p pt acc) ctx params param_types

  (** Check that arguments match expected chiralities *)
  let check_args (ctx : ctx) (args : Ident.t list) (expected : chiral_tpe list) : unit check_result =
    if List.length args <> List.length expected then
      Error (ArityMismatch { xtor = -1; expected = List.length expected; got = List.length args })
    else
      List.fold_left2 (fun acc arg exp ->
        let* () = acc in
        let* got = lookup ctx arg in
        match exp, got with
        | Lhs _, Lhs _ -> Ok ()
        | Rhs _, Rhs _ -> Ok ()
        | _ -> Error (ChiralityMismatch { var = arg; expected = show_chiral exp; got })
      ) (Ok ()) args expected

  (** Check a branch *)
  let rec check_branch (ctx : ctx) (sgn : signature) (n : int) 
      (Clause (params, body)) : unit check_result =
    let* param_types = get_xtor_params sgn n in
    if List.length params <> List.length param_types then
      Error (ArityMismatch { xtor = n; expected = List.length param_types; got = List.length params })
    else
      let ctx' = extend_with_params ctx params param_types in
      check_command ctx' body

  (** Check all branches *)
  and check_branches (ctx : ctx) (sgn : signature) (branches : branch list) : unit check_result =
    if List.length branches <> List.length sgn then
      Error (NonExhaustive { expected = List.length sgn; got = List.length branches })
    else
      List.fold_left (fun acc (n, branch) ->
        let* () = acc in
        check_branch ctx sgn n branch
      ) (Ok ()) (List.mapi (fun i b -> (i, b)) branches)

  (** Main type checking function *)
  and check_command (ctx : ctx) : command -> unit check_result = function
    | Let (sgn, n, args, x, cont) ->
        (* Let binds x as Lhs (producer) *)
        let* param_types = get_xtor_params sgn n in
        let* () = check_args ctx args param_types in
        let ctx' = Ident.add x (Lhs sgn) ctx in
        check_command ctx' cont

    | Switch (sgn, v, branches) ->
        (* Switch expects v to be Lhs (producer) *)
        let* _ = expect_lhs ctx v in
        check_branches ctx sgn branches

    | New (sgn, branches, x, cont) ->
        (* New binds x as Rhs (consumer) *)
        let* () = check_branches ctx sgn branches in
        let ctx' = Ident.add x (Rhs sgn) ctx in
        check_command ctx' cont

    | Invoke (sgn, n, args, v) ->
        (* Invoke expects v to be Rhs (consumer) *)
        let* _ = expect_rhs ctx v in
        let* param_types = get_xtor_params sgn n in
        check_args ctx args param_types

    | LetInt (_, x, cont) ->
        (* LetInt binds x as an integer (we treat as Lhs with empty signature) *)
        let ctx' = Ident.add x (Lhs []) ctx in
        check_command ctx' cont

    | Add (x, y, k, cont) ->
        (* Add expects x and y to be integers, binds k as integer *)
        let* _ = lookup ctx x in
        let* _ = lookup ctx y in
        let ctx' = Ident.add k (Lhs []) ctx in
        check_command ctx' cont

    | CutInt (x, k) ->
        (* CutInt passes an int to a continuation *)
        let* _ = lookup ctx x in
        let* _ = lookup ctx k in
        Ok ()

    | Ret (_, x) ->
        (* Ret expects x to be in scope with matching signature.
           For positive types collapsed from Source, x is Lhs.
           For negative types collapsed from Source, x is Rhs (due to chirality flip). *)
        let* _ = lookup ctx x in
        Ok ()

    | RetInt x ->
        (* RetInt expects x to be in scope *)
        let* _ = lookup ctx x in
        Ok ()

    | End -> Ok ()

  (** Entry point for type checking *)
  let typecheck (cmd : command) : unit check_result =
    check_command Ident.emptytbl cmd

end

(* ========================================================================= *)
(* Collapse Transformation (Target → Collapsed)                              *)
(* ========================================================================= *)

module Collapse = struct
  (** 
    Collapse the 8-form Target language to the 4-form Collapsed language.
    
    Key insight: chirality flips for negative types.
    - Positive type T: Lhs T → Lhs, Rhs T → Rhs  (preserved)
    - Negative type T: Lhs T → Rhs, Rhs T → Lhs  (flipped)
    
    This ensures consistent variable typing:
    - Let/Switch operate on producers (Lhs in Collapsed)
    - New/Invoke operate on consumers (Rhs in Collapsed)
  *)

  (** Collapse a chiral type, flipping chirality for negative types *)
  let rec collapse_chiral : chiral_tpe -> Collapsed.chiral_tpe = function
    | Lhs Int -> Collapsed.Lhs []  (* Int is positive, treat as empty signature *)
    | Rhs Int -> Collapsed.Rhs []
    | Lhs (Pos sgn) -> Collapsed.Lhs (collapse_sig sgn)
    | Rhs (Pos sgn) -> Collapsed.Rhs (collapse_sig sgn)
    | Lhs (Neg sgn) -> Collapsed.Rhs (collapse_sig sgn)  (* flip! *)
    | Rhs (Neg sgn) -> Collapsed.Lhs (collapse_sig sgn)  (* flip! *)

  (** Collapse a signature (list of constructor/destructor parameter lists) *)
  and collapse_sig (sgn : signature) : Collapsed.signature =
    List.map (List.map collapse_chiral) sgn

  (** Collapse a branch *)
  let rec collapse_branch (Target.Clause (params, body)) : Collapsed.branch =
    Collapsed.Clause (params, collapse_command body)

  (** Main collapse transformation *)
  and collapse_command : Target.command -> Collapsed.command = function
    (* Let: ⟨C(Γ)|μ̃x.s⟩ and ⟨μα.s|D(Γ)⟩ both become Let *)
    | Target.LetConstructor (sgn, n, args, x, cont) ->
        Collapsed.Let (collapse_sig sgn, n, args, x, collapse_command cont)
    | Target.LetDestructor (sgn, n, args, a, cont) ->
        Collapsed.Let (collapse_sig sgn, n, args, a, collapse_command cont)

    (* Switch: ⟨x|case{…}⟩ and ⟨cocase{…}|α⟩ both become Switch *)
    | Target.CutMatch (sgn, x, branches) ->
        Collapsed.Switch (collapse_sig sgn, x, List.map collapse_branch branches)
    | Target.CutComatch (sgn, branches, a) ->
        Collapsed.Switch (collapse_sig sgn, a, List.map collapse_branch branches)

    (* New: ⟨cocase{…}|μ̃x.s⟩ and ⟨μα.s|case{…}⟩ both become New *)
    | Target.LetComatch (sgn, branches, x, cont) ->
        Collapsed.New (collapse_sig sgn, List.map collapse_branch branches, x, collapse_command cont)
    | Target.LetMatch (sgn, branches, a, cont) ->
        Collapsed.New (collapse_sig sgn, List.map collapse_branch branches, a, collapse_command cont)

    (* Invoke: ⟨C(Γ)|α⟩ and ⟨x|D(Γ)⟩ both become Invoke *)
    | Target.CutConstructor (sgn, n, args, a) ->
        Collapsed.Invoke (collapse_sig sgn, n, args, a)
    | Target.CutDestructor (sgn, x, n, args) ->
        Collapsed.Invoke (collapse_sig sgn, n, args, x)

    (* Int operations *)
    | Target.LetInt (n, x, cont) ->
        Collapsed.LetInt (n, x, collapse_command cont)
    | Target.CutInt (x, k) ->
        Collapsed.CutInt (x, k)
    | Target.Add (x, y, k, cont) ->
        Collapsed.Add (x, y, k, collapse_command cont)

    | Target.Ret (sgn, x) -> Collapsed.Ret (collapse_sig sgn, x)
    | Target.RetInt x -> Collapsed.RetInt x
    | Target.End -> Collapsed.End

  (** Full pipeline: Source → Target → Collapsed *)
  let from_source (cmd : Source.command) : Collapsed.command =
    collapse_command (Transform.transform_command cmd Sub.empty)
end

(* ========================================================================= *)
(* Abstract Machine for Collapsed                                            *)
(* ========================================================================= *)

module Machine = struct

  (** Values in the machine *)
  type value =
    | Producer of int * Ident.t list * env  (** {xtor_index; args; E} - a constructor with its captured environment *)
    | Consumer of env * Collapsed.branch list  (** {E; branches} - branches with captured environment *)
    | IntVal of int  (** Integer literal *)

  (** Environment maps variables to values *)
  and env = value Ident.tbl

  (** Configuration: command + environment *)
  type config = Collapsed.command * env

  let empty_env : env = Ident.emptytbl

  let lookup (e: env) (x: Ident.t) : value =
    match Ident.find_opt x e with
    | Some v -> v
    | None -> failwith ("unbound variable: " ^ Ident.name x)

  let lookup_opt (e: env) (x: Ident.t) : value option =
    Ident.find_opt x e

  let lookup_int (e: env) (x: Ident.t) : int =
    match lookup e x with
    | IntVal n -> n
    | _ -> failwith ("expected int value for: " ^ Ident.name x)

  let lookup_producer (e: env) (x: Ident.t) : int * Ident.t list * env =
    match lookup e x with
    | Producer (n, args, e0) -> (n, args, e0)
    | _ -> failwith ("expected producer value for: " ^ Ident.name x)

  let lookup_consumer (e: env) (x: Ident.t) : env * Collapsed.branch list =
    match lookup e x with
    | Consumer (e0, branches) -> (e0, branches)
    | _ -> failwith ("expected consumer value for: " ^ Ident.name x)

  let extend (e: env) (x: Ident.t) (v: value) : env =
    Ident.add x v e

  (** Build sub-environment for a list of variables *)
  let sub_env (e: env) (vars: Ident.t list) : env =
    List.fold_left (fun acc x -> extend acc x (lookup e x)) empty_env vars

  (** Pretty-print a value *)
  let pp_value = function
    | Producer (n, args, _) -> 
        Printf.sprintf "{C%d(%s); ...}" n (String.concat ", " (List.map Ident.name args))
    | Consumer (_, branches) -> 
        Printf.sprintf "{...; %d branches}" (List.length branches)
    | IntVal n -> string_of_int n

  (** Pretty-print environment (just the bindings) *)
  let pp_env (e: env) : string =
    let bindings = Ident.to_list e in
    String.concat ", " (List.map (fun (x, v) -> Ident.name x ^ " → " ^ pp_value v) bindings)

  (** Pretty-print configuration *)
  let pp_config ((cmd, e): config) : string =
    "⟨" ^ Collapsed.show_command cmd ^ " ∥ {" ^ pp_env e ^ "}⟩"

  (** Merge two environments (e2 values override e1 on conflicts) *)
  let merge_env (e1: env) (e2: env) : env =
    List.fold_left (fun acc (x, v) -> extend acc x v) e1 (Ident.to_list e2)

  (** Single step of the machine. Returns None if stuck or terminal. *)
  let step ((cmd, e): config) : config option =
    match cmd with
    (* (let) ⟨let v = C_n(Γ); s ∥ E⟩ → ⟨s ∥ E, v → {n; Γ; E|Γ}⟩
       Creates a producer: the xtor index with args and captured environment *)
    | Collapsed.Let (_, n, args, v, body) ->
        let e0 = sub_env e args in
        let e' = extend e v (Producer (n, args, e0)) in
        Some (body, e')

    (* (new) ⟨new v = branches; s ∥ E⟩ → ⟨s ∥ E, v → {E; branches}⟩
       Creates a consumer: captures current env and all branches *)
    | Collapsed.New (_, branches, v, body) ->
        let e' = extend e v (Consumer (e, branches)) in
        Some (body, e')

    (* (switch) ⟨switch v {branches} ∥ E⟩
       Matches on a producer, selecting the appropriate branch.
       NOTE: Only handles producers - consumers are a type error! *)
    | Collapsed.Switch (_, v, branches) ->
        (match lookup e v with
         | Producer (n, _, e0) ->
             (* Select the n-th branch and bind captured values to params *)
             let Collapsed.Clause (params, branch_body) = List.nth branches n in
             let e0_list = List.rev (Ident.to_list e0) in
             let e' = List.fold_left2 (fun acc p (_, val_) -> extend acc p val_) e params e0_list in
             Some (branch_body, e')
         | Consumer _ ->
             failwith "type error: switch on consumer (expected producer)"
         | IntVal _ ->
             failwith "type error: switch on int (expected producer)")

    (* (invoke) ⟨v.D_n(Γ) ∥ E, v → {E0; branches}⟩ → ⟨branch_n ∥ E0[params↦E(Γ)]⟩
       Invokes a consumer: selects the n-th branch and binds args to params *)
    | Collapsed.Invoke (_, n, args, v) ->
        let (e0, branches) = lookup_consumer e v in
        let Collapsed.Clause (params, branch_body) = List.nth branches n in
        let arg_vals = List.map (fun a -> lookup e a) args in
        let e_merged = merge_env e0 e in
        let e' = List.fold_left2 extend e_merged params arg_vals in
        Some (branch_body, e')

    (* (letint) ⟨let v = n; s ∥ E⟩ → ⟨s ∥ E, v → n⟩ *)
    | Collapsed.LetInt (n, v, body) ->
        let e' = extend e v (IntVal n) in
        Some (body, e')

    (* (add) ⟨let k = add(x, y); s ∥ E⟩ → ⟨s ∥ E, k → E(x) + E(y)⟩ *)
    | Collapsed.Add (x, y, k, body) ->
        let n1 = lookup_int e x in
        let n2 = lookup_int e y in
        let e' = extend e k (IntVal (n1 + n2)) in
        Some (body, e')

    (* (cutint) ⟨x | k⟩ⁱ ∥ E → pass int value to consumer k *)
    | Collapsed.CutInt (x, k) ->
        (match lookup_opt e k with
         | None ->
             (* k is unbound (open term) - stuck *)
             None
         | Some (Consumer (e0, branches)) ->
             (* k is a consumer - select first branch (Int has one "constructor") *)
             let Collapsed.Clause (params, branch_body) = List.hd branches in
             let int_val = lookup e x in
             let e' = extend e0 (List.hd params) int_val in
             Some (branch_body, e')
         | Some _ ->
             failwith "cutint: k should be a consumer")

    (* Terminal commands *)
    | Collapsed.Ret _ -> None
    | Collapsed.RetInt _ -> None
    | Collapsed.End -> None

  (** Check if machine terminated with a result *)
  let get_result ((cmd, e): config) : value option =
    match cmd with
    | Collapsed.Ret (_, v) -> Some (lookup e v)
    | Collapsed.RetInt v -> Some (lookup e v)
    | Collapsed.CutInt (x, k) when lookup_opt e k = None ->
        (* Open term: return the value being passed *)
        Some (lookup e x)
    | _ -> None

  (** Short name for a command (for tracing) *)
  let cmd_name = function
    | Collapsed.Let (_, n, _, v, _) -> Printf.sprintf "let %s = C%d" (Ident.name v) n
    | Collapsed.New (_, branches, v, _) -> Printf.sprintf "new %s (%d branches)" (Ident.name v) (List.length branches)
    | Collapsed.Switch (_, v, _) -> "switch " ^ Ident.name v
    | Collapsed.Invoke (_, n, _, v) -> Printf.sprintf "%s.D%d" (Ident.name v) n
    | Collapsed.LetInt (n, v, _) -> Printf.sprintf "let %s = %d" (Ident.name v) n
    | Collapsed.Add (x, y, k, _) -> Printf.sprintf "let %s = %s + %s" (Ident.name k) (Ident.name x) (Ident.name y)
    | Collapsed.CutInt (x, k) -> Printf.sprintf "⟨%s | %s⟩ⁱ" (Ident.name x) (Ident.name k)
    | Collapsed.Ret (_, v) -> "ret " ^ Ident.name v
    | Collapsed.RetInt v -> "retint " ^ Ident.name v
    | Collapsed.End -> "end"

  (** Run the machine until it stops. Returns (final_config, step_count) *)
  let rec run ?(trace=false) ?(steps=0) (cfg: config) : config * int =
    let (cmd, e) = cfg in
    if trace then
      Printf.printf "    [%d] %s | env has %d bindings\n"
        steps (cmd_name cmd) (List.length (Ident.to_list e));
    match step cfg with
    | None -> (cfg, steps)
    | Some cfg' -> run ~trace ~steps:(steps + 1) cfg'

  (** Run with tracing (returns all configurations) *)
  let rec run_trace (cfg: config) : config list =
    cfg :: (match step cfg with
            | None -> []
            | Some cfg' -> run_trace cfg')

  (** Initialize and run a command. Returns (final_config, step_count) *)
  let eval ?(trace=false) (cmd: Collapsed.command) : config * int =
    run ~trace (cmd, empty_env)

  (** Initialize and run with trace *)
  let eval_trace (cmd: Collapsed.command) : config list =
    run_trace (cmd, empty_env)

end
