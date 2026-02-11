open Common.Identifiers

type var = Ident.t

module Pcf = struct

  type typ = Int | Arrow of typ * typ

  type term =
      Var of var
    | Lam of var * typ * term
    | App of term * term
    | Lit of int
    | Add of term * term
    | Ifz of term * term * term

  let rec pp_typ =
    function
      Int -> "Int"
    | Arrow (t1, t2) ->
        let t1_str =
          match t1 with
          | Arrow _ -> "(" ^ pp_typ t1 ^ ")"
          | _ -> pp_typ t1
        in t1_str ^ " -> " ^ pp_typ t2
  
  let rec pp_term =
    function
      Var x -> Ident.name x
    | Lam (x, ty, body) ->
        "λ" ^ Ident.name x ^ ": " ^ pp_typ ty ^ ". " ^ pp_term body
    | App (t1, t2) ->
        let t1_str =
          match t1 with
          | Lam _ -> "(" ^ pp_term t1 ^ ")"
          | _ -> pp_term t1
        in t1_str ^ " " ^ pp_term t2
    | Lit n -> string_of_int n
    | Add (t1, t2) -> "(" ^ pp_term t1 ^ " + " ^ pp_term t2 ^ ")"
    | Ifz (t1, t2, t3) ->
        "ifz " ^ pp_term t1 ^ " then " ^ pp_term t2 ^ " else " ^ pp_term t3
    
  let rec infer_typ (ctx: typ Ident.tbl) =
    function
      Var x -> Ident.find x ctx
    | Lam (x, ty, body) ->
        let ctx' = Ident.add x ty ctx in
        let body_ty = infer_typ ctx' body in
        Arrow (ty, body_ty)
    | App (t1, t2) ->
        let t1_ty = infer_typ ctx t1 in
        let t2_ty = infer_typ ctx t2 in
        (match t1_ty with
        Arrow (arg_ty, ret_ty) ->
          if arg_ty = t2_ty then ret_ty
          else failwith "Type error: argument type mismatch"
        | _ -> failwith "Type error: expected a function")
    | Lit _ -> Int
    | Add (t1, t2) ->
        let t1_ty = infer_typ ctx t1 in
        let t2_ty = infer_typ ctx t2 in
        if t1_ty = Int && t2_ty = Int then Int
        else failwith "Type error: expected integers in addition"
    | Ifz (t1, t2, t3) ->
        let t1_ty = infer_typ ctx t1 in
        let t2_ty = infer_typ ctx t2 in
        let t3_ty = infer_typ ctx t3 in
        if t1_ty = Int && t2_ty = t3_ty then t2_ty
        else failwith "Type error: expected int condition and matching branches"
end

module Seq = struct

  type typ =
      Int 
    | Sig of xtor

  and xtor =
      Apply of typ * typ (** Xtor of Fun(A, B) **)
    | Return of typ (** Xtor of Lower(A) - shifts to consumer **)
    | Thunk of typ (** Xtor of Raise(A) - shifts to producer **)

  (** Chirality: Lhs = producer, Rhs = consumer **)
  type chiral_typ = Lhs of typ | Rhs of typ

  type command =
      Cut of typ * term * term  (** ⟨producer | consumer⟩ at type **)
    | Add of term * term * term
    | Ifz of term * command * command
    | End

  and term =
      Variable of var
    | Lit of int
    (** Constructors build data (Lhs/producer) **)
    | CtorApply of typ * typ * term * term
    | CtorReturn of typ * term
    | CtorThunk of typ * term
    (** Destructors build codata (Rhs/consumer) **)
    | DtorApply of typ * typ * term * term
    | DtorReturn of typ * term
    | DtorThunk of typ * term
    (** Match consumes data (Rhs/consumer) **)
    | MatchApply of typ * typ * var * var * command
    | MatchReturn of typ * var * command
    | MatchThunk of typ * var * command
    (** Comatch produces codata (Lhs/producer) **)
    | ComatchApply of typ * typ * var * var * command
    | ComatchReturn of typ * var * command
    | ComatchThunk of typ * var * command
    (** Mu binds a continuation **)
    | MuLhs of typ * var * command  (** μL binds Rhs var, produces Lhs **)
    | MuRhs of typ * var * command  (** μR binds Lhs var, produces Rhs **)

  let rec rename ((x, y): var * var) =
    function
      Variable z when Ident.equal z x -> Variable y
    | Variable z -> Variable z
    | Lit n -> Lit n
    | CtorApply (a, b, arg, cont) ->
        CtorApply (a, b, rename (x, y) arg, rename (x, y) cont)
    | CtorReturn (a, arg) ->
        CtorReturn (a, rename (x, y) arg)
    | CtorThunk (a, arg) ->
        CtorThunk (a, rename (x, y) arg)
    | DtorApply (a, b, arg, cont) ->
        DtorApply (a, b, rename (x, y) arg, rename (x, y) cont)
    | DtorReturn (a, arg) ->
        DtorReturn (a, rename (x, y) arg)
    | DtorThunk (a, arg) ->
        DtorThunk (a, rename (x, y) arg)
    | MatchApply (a, b, z, k, cmd) when Ident.equal z x || Ident.equal k x ->
        MatchApply (a, b, z, k, cmd)  (* Shadowing: do not rename inside *)
    | MatchApply (a, b, z, k, cmd) ->
        MatchApply (a, b, z, k, rename_cmd (x, y) cmd)
    | MatchReturn (a, z, cmd) when Ident.equal z x ->
        MatchReturn (a, z, cmd)  (* Shadowing *)
    | MatchReturn (a, z, cmd) ->
        MatchReturn (a, z, rename_cmd (x, y) cmd)
    | MatchThunk (a, z, cmd) when Ident.equal z x ->
        MatchThunk (a, z, cmd)  (* Shadowing *)
    | MatchThunk (a, z, cmd) ->
        MatchThunk (a, z, rename_cmd (x, y) cmd)
    | ComatchApply (a, b, z, k, cmd) when Ident.equal z x || Ident.equal k x ->
        ComatchApply (a, b, z, k, cmd)  (* Shadowing *)
    | ComatchApply (a, b, z, k, cmd) ->
        ComatchApply (a, b, z, k, rename_cmd (x, y) cmd)
    | ComatchReturn (a, z, cmd) when Ident.equal z x ->
        ComatchReturn (a, z, cmd)  (* Shadowing *)
    | ComatchReturn (a, z, cmd) ->
        ComatchReturn (a, z, rename_cmd (x, y) cmd)
    | ComatchThunk (a, z, cmd) when Ident.equal z x ->
        ComatchThunk (a, z, cmd)  (* Shadowing *)
    | ComatchThunk (a, z, cmd) ->
        ComatchThunk (a, z, rename_cmd (x, y) cmd)
    | MuLhs (a, z, cmd) when Ident.equal z x ->
        MuLhs (a, z, cmd)  (* Shadowing *)
    | MuLhs (a, z, cmd) ->
        MuLhs (a, z, rename_cmd (x, y) cmd)
    | MuRhs (a, z, cmd) when Ident.equal z x ->
        MuRhs (a, z, cmd)  (* Shadowing *)
    | MuRhs (a, z, cmd) ->
        MuRhs (a, z, rename_cmd (x, y) cmd)
  
  and rename_cmd (x, y) =
    function
      Cut (a, t1, t2) ->
        Cut (a, rename (x, y) t1, rename (x, y) t2)
    | Add (t1, t2, t3) ->
        Add (rename (x, y) t1, rename (x, y) t2, rename (x, y) t3)
    | Ifz (t, cmd1, cmd2) ->
        Ifz (rename (x, y) t, rename_cmd (x, y) cmd1, rename_cmd (x, y) cmd2)
    | End -> End

  let rec pp_command =
    function
      Cut (_, t1, t2) -> "⟨" ^ pp_term t1 ^ " ∥ " ^ pp_term t2 ^ "⟩"
    | Add (t1, t2, t3) -> "add(" ^ pp_term t1 ^ ", " ^ pp_term t2 ^ ", " ^ pp_term t3 ^ ")"
    | Ifz (t, cmd1, cmd2) -> "ifz(" ^ pp_term t ^ ") then " ^ pp_command cmd1 ^ " else " ^ pp_command cmd2
    | End -> "end"
  
  and pp_term =
    function
      Variable x -> Ident.name x
    | Lit n -> string_of_int n
    | CtorApply (a, b, arg, cont) ->
        "ctor_apply[" ^ pp_typ a ^ ", " ^ pp_typ b ^ "](" 
          ^ pp_term arg ^ ", " ^ pp_term cont ^ ")"
    | CtorReturn (a, arg) ->
        "ctor_return[" ^ pp_typ a ^ "](" ^ pp_term arg ^ ")"
    | CtorThunk (a, arg) ->
        "ctor_thunk[" ^ pp_typ a ^ "](" ^ pp_term arg ^ ")"
    | DtorApply (a, b, arg, cont) ->
        "dtor_apply[" ^ pp_typ a ^ ", " ^ pp_typ b ^ "](" 
          ^ pp_term arg ^ ", " ^ pp_term cont ^ ")"
    | DtorReturn (a, arg) ->
        "dtor_return[" ^ pp_typ a ^ "](" ^ pp_term arg ^ ")"
    | DtorThunk (a, arg) ->
        "dtor_thunk[" ^ pp_typ a ^ "](" ^ pp_term arg ^ ")"
    | MatchApply (a, b, x, k, cmd) ->
        "case { ctor_apply[" ^ pp_typ a ^ ", " ^ pp_typ b ^ "](" 
          ^ Ident.name x ^ ", " ^ Ident.name k ^ ") ⇒ " ^ pp_command cmd ^ "}"
    | MatchReturn (a, x, cmd) ->
        "case { ctor_return[" ^ pp_typ a ^ "](" 
          ^ Ident.name x ^ ") ⇒ " ^ pp_command cmd ^ "}"
    | MatchThunk (a, x, cmd) ->
        "case { ctor_thunk[" ^ pp_typ a ^ "](" 
          ^ Ident.name x ^ ") ⇒ " ^ pp_command cmd ^ "}"
    | ComatchApply (a, b, x, k, cmd) ->
        "cocase { dtor_apply[" ^ pp_typ a ^ ", " ^ pp_typ b ^ "](" 
          ^ Ident.name x ^ ", " ^ Ident.name k ^ ") ⇒ " ^ pp_command cmd ^ "}"
    | ComatchReturn (a, x, cmd) ->
        "cocase { dtor_return[" ^ pp_typ a ^ "](" 
          ^ Ident.name x ^ ") ⇒ " ^ pp_command cmd ^ "}"
    | ComatchThunk (a, x, cmd) ->
        "cocase { dtor_thunk[" ^ pp_typ a ^ "](" 
          ^ Ident.name x ^ ") ⇒ " ^ pp_command cmd ^ "}"
    | MuLhs (_, k, cmd) -> "μL " ^ Ident.name k ^ ". " ^ pp_command cmd
    | MuRhs (_, k, cmd) -> "μR " ^ Ident.name k ^ ". " ^ pp_command cmd
  
  and pp_typ =
    function
      Int -> "Int"
    | Sig (Apply (a, b)) -> "Fun(" ^ pp_typ a ^ ", " ^ pp_typ b ^ ")"
    | Sig (Return a) -> "Lower(" ^ pp_typ a ^ ")"
    | Sig (Thunk a) -> "Raise(" ^ pp_typ a ^ ")"

  (* Determine the "natural chirality" of a type:
    - Int is positive (data-like), so values are Lhs
    - Sig(Return A) is positive - it's data packaging a value/computation
    - Sig(Thunk A) is positive - it's data packaging a suspended computation
    - Sig(Apply ...) is negative - functions are codata-like (demand-driven) *)
  let is_positive_typ = function
    | Int -> true
    | Sig (Return _) -> true   (* Lower makes something data-like *)
    | Sig (Thunk _) -> true    (* Raise makes something data-like (thunk is a value) *)
    | Sig (Apply _) -> false   (* Functions are codata-like *)
  
  (* The chirality of a term of type A:
    - If A is positive, terms are Lhs (producers/values)
    - If A is negative, terms are Rhs (consumers/computations) *)
  let natural_chirality ty =
    if is_positive_typ ty then Lhs ty else Rhs ty

  let rec infer_command_typ (ctx: chiral_typ Ident.tbl) =
    function
      Cut (ret_ty, t1, t2) ->
        let t1_ty = infer_typ ctx t1 in
        let t2_ty = infer_typ ctx t2 in
        (match t1_ty, t2_ty with
          Lhs ty1, Rhs ty2 when ty1 = ret_ty && ty2 = ret_ty ->
            Some ret_ty
        | _ -> 
            failwith (Printf.sprintf "Type error in Cut (type %s): expected Lhs %s and Rhs %s, got %s and %s"
              (pp_typ ret_ty) (pp_typ ret_ty) (pp_typ ret_ty)
              (match t1_ty with Lhs t -> "Lhs " ^ pp_typ t | Rhs t -> "Rhs " ^ pp_typ t)
              (match t2_ty with Lhs t -> "Lhs " ^ pp_typ t | Rhs t -> "Rhs " ^ pp_typ t)))
    | Add (t1, t2, t3) ->
        let t1_ty = infer_typ ctx t1 in
        let t2_ty = infer_typ ctx t2 in
        let t3_ty = infer_typ ctx t3 in
        if t1_ty = Lhs Int && t2_ty = Lhs Int && t3_ty = Rhs Int
        then Some Int
        else failwith "Type error in Add"
    | Ifz (t, cmd1, cmd2) ->
        (match infer_typ ctx t with
          Lhs Int ->
            let cmd1_ty = infer_command_typ ctx cmd1 in
            let cmd2_ty = infer_command_typ ctx cmd2 in
            if cmd1_ty = cmd2_ty then cmd1_ty
            else failwith "Type error: branches of Ifz have different types"
        | _ -> failwith "Type error: condition of Ifz must be Int")
    | End -> None

  and infer_typ (ctx: chiral_typ Ident.tbl) =
    function
      Variable x -> Ident.find x ctx
    | Lit _ -> Lhs Int
    | CtorApply (a, b, arg, cont) ->
        let arg_ty = infer_typ ctx arg in
        let cont_ty = infer_typ ctx cont in
        (* arg has natural chirality of a, cont is always Rhs b *)
        let expected_arg = natural_chirality a in
        let expected_cont = Rhs b in
        if arg_ty = expected_arg && cont_ty = expected_cont then
          Lhs (Sig (Apply (a, b)))
        else failwith (Printf.sprintf "Type error in CtorApply: expected %s and %s, got %s and %s"
          (match expected_arg with Lhs t -> "Lhs " ^ pp_typ t | Rhs t -> "Rhs " ^ pp_typ t)
          (match expected_cont with Lhs t -> "Lhs " ^ pp_typ t | Rhs t -> "Rhs " ^ pp_typ t)
          (match arg_ty with Lhs t -> "Lhs " ^ pp_typ t | Rhs t -> "Rhs " ^ pp_typ t)
          (match cont_ty with Lhs t -> "Lhs " ^ pp_typ t | Rhs t -> "Rhs " ^ pp_typ t))
    | CtorReturn (a, arg) ->
        let arg_ty = infer_typ ctx arg in
        (* The argument's chirality depends on whether a is positive or negative *)
        let expected = natural_chirality a in
        if arg_ty = expected then
          Lhs (Sig (Return a))
        else failwith "Type error in CtorReturn"
    | CtorThunk (a, arg) ->
        let arg_ty = infer_typ ctx arg in
        (* Thunk suspends a computation, so arg should match natural chirality of a *)
        let expected = natural_chirality a in
        if arg_ty = expected then
          Lhs (Sig (Thunk a))
        else failwith "Type error in CtorThunk"
    | DtorApply (a, b, arg, cont) ->
        let arg_ty = infer_typ ctx arg in
        let cont_ty = infer_typ ctx cont in
        (* arg is always Lhs (value), cont is always Rhs (continuation) *)
        if arg_ty = Lhs a && cont_ty = Rhs b then
          Lhs (Sig (Apply (a, b)))
        else failwith "Type error in DtorApply"
    | DtorReturn (a, arg) ->
        let arg_ty = infer_typ ctx arg in
        let expected = natural_chirality a in
        if arg_ty = expected then
          Lhs (Sig (Return a))  (* Producer - placed on left against MatchReturn *)
        else failwith "Type error in DtorReturn"
    | DtorThunk (a, arg) ->
        let arg_ty = infer_typ ctx arg in
        let expected = natural_chirality a in
        if arg_ty = expected then
          Lhs (Sig (Thunk a))  (* Producer - placed on left against MatchThunk *)
        else failwith "Type error in DtorThunk"
    | MatchApply (a, b, x, k, cmd) ->
        (* x receives the argument (always Lhs - values are passed)
          k receives the continuation (always Rhs - continuations consume) *)
        let ctx' =
          Ident.add x (Lhs a) (Ident.add k (Rhs b) ctx)
        in
        infer_command_typ ctx' cmd |> ignore;
        Rhs (Sig (Apply (a, b)))
    | MatchReturn (a, x, cmd) ->
        let ctx' = Ident.add x (natural_chirality a) ctx in
        infer_command_typ ctx' cmd |> ignore;
        Rhs (Sig (Return a))
    | MatchThunk (a, x, cmd) ->
        let ctx' = Ident.add x (natural_chirality a) ctx in
        infer_command_typ ctx' cmd |> ignore;
        Rhs (Sig (Thunk a))
    | ComatchApply (a, b, x, k, cmd) ->
        (* x receives the argument (always Lhs - values are passed)
          k receives the continuation (always Rhs - continuations consume) *)
        let ctx' =
          Ident.add x (Lhs a) (Ident.add k (Rhs b) ctx)
        in
        infer_command_typ ctx' cmd |> ignore;
        Rhs (Sig (Apply (a, b)))  (* Consumer - placed on right against CtorApply *)
    | ComatchReturn (a, x, cmd) ->
        let ctx' = Ident.add x (natural_chirality a) ctx in
        infer_command_typ ctx' cmd |> ignore;
        Rhs (Sig (Return a))  (* Consumer - placed on right against CtorReturn *)
    | ComatchThunk (a, x, cmd) ->
        let ctx' = Ident.add x (natural_chirality a) ctx in
        infer_command_typ ctx' cmd |> ignore;
        Rhs (Sig (Thunk a))  (* Consumer - placed on right against CtorThunk *)
    | MuLhs (ty, x, cmd) ->
        let ctx' = Ident.add x (Rhs ty) ctx in
        infer_command_typ ctx' cmd |> ignore;
        Lhs ty
    | MuRhs (ty, k, cmd) ->
        let ctx' = Ident.add k (Lhs ty) ctx in
        infer_command_typ ctx' cmd |> ignore;
        Rhs ty
    
end

module Encode = struct

  open Seq
  
  (* Lower shifts a type to consumer position (CPS return) *)
  let lower ty = Sig (Return ty)
  (* Raise shifts a type to producer position (thunk/suspend) *)
  let raise ty = Sig (Thunk ty)

  (* Determine if a PCF type is "positive" (data-like) or "negative" (codata-like) *)
  let is_positive = function
    | Pcf.Int -> true
    | Pcf.Arrow _ -> false

  let rec map_typ = function
    | Pcf.Int -> Int
    | Pcf.Arrow (a, b) ->
        let a' = map_typ a in
        let b' = map_typ b in
        (* We always lower the codomain because the body of a lambda
          must be in producer position (Lhs) to cut against the continuation.
          For arguments:
          - Positive args (Int) stay as-is: they're values (Lhs)
          - Negative args (functions) are raised: they're computations 
            that need to be suspended into values (Lhs) *)
        match is_positive a with
        | true -> Sig (Apply (a', lower b'))
        | false -> Sig (Apply (raise a', lower b'))
    
  let rec map_term (ctx: Pcf.typ Ident.tbl) =
    function
      Pcf.Var x -> Variable x
    | Pcf.Lam (x, a, body) ->
        (* λx:A. body  where body: B
          Type is Fun(A', Lower(B')) where A' may be raised if A is negative.
          The encoding wraps body' in CtorReturn since we always lower the result. *)
        let ctx' = Ident.add x a ctx in
        let b = Pcf.infer_typ ctx' body in
        let body' = map_term ctx' body in
        let k = Ident.fresh () in
        let a' = map_typ a in
        let b' = map_typ b in
        (match is_positive a with
        | true ->
            (* case { ctor_apply[a', lower b'](x, k) ⇒ ⟨ctor_return[b'](body') | k⟩ } *)
            MatchApply (a', lower b', x, k,
              Cut (lower b', CtorReturn (b', body'), Variable k))
        | false ->
            (* case { ctor_apply[raise a', lower b'](x', k) ⇒
                 ⟨x' | case { ctor_thunk[a'](x) ⇒ ⟨ctor_return[b'](body') | k⟩ }⟩ } *)
            let x' = Ident.fresh () in
            MatchApply (raise a', lower b', x', k,
              Cut (raise a',
                Variable x',
                MatchThunk (a', x, Cut (lower b', CtorReturn (b', body'), Variable k)))))
    | Pcf.App (t1, t2) ->
        (* t1 t2  where t1 : A → B, t2 : A
          A function call is: ⟨ctor_apply[A', Lower(B')](t2', k) | t1'⟩
          where k is a continuation that receives the result.
          We wrap in μL/μR based on whether B is positive/negative. *)
        let t1_ty = Pcf.infer_typ ctx t1 in
        let (a, b) = match t1_ty with
          | Pcf.Arrow (a, b) -> (a, b)
          | _ -> failwith "Application of non-function"
        in
        let t1' = map_term ctx t1 in
        let t2' = map_term ctx t2 in
        let k = Ident.fresh () in
        let a' = map_typ a in
        let b' = map_typ b in
        (* Choose Mu form based on whether result type is positive or negative *)
        let make_mu = if is_positive b then
          (fun ty k cmd -> MuLhs (ty, k, cmd))
        else
          (fun ty k cmd -> MuRhs (ty, k, cmd))
        in
        (* Inner cut between return value x and continuation k.
          For positive b': x is Lhs, k is Rhs (from MuLhs), so Cut(b', x, k)
          For negative b': x is Rhs (natural chirality), k is Lhs (from MuRhs), so Cut(b', k, x) *)
        let make_inner_cut b' x k =
          if is_positive_typ b' then
            Cut (b', Variable x, Variable k)
          else
            Cut (b', Variable k, Variable x)
        in
        (match is_positive a with
        | true ->
            (* μ k. ⟨ctor_apply[a', lower b'](t2', cocase{dtor_return[b'](x) ⇒ ⟨x | k⟩}) | t1'⟩ *)
            let x = Ident.fresh () in
            make_mu b' k
              (Cut (Sig (Apply (a', lower b')),
                CtorApply (a', lower b', t2',
                  ComatchReturn (b', x, make_inner_cut b' x k)),
                t1'))
        | false ->
            (* μ k. ⟨ctor_apply[raise a', lower b'](ctor_thunk[a'](t2'), 
                      cocase{dtor_return[b'](x) ⇒ ⟨x | k⟩}) | t1'⟩ *)
            let x = Ident.fresh () in
            make_mu b' k
              (Cut (Sig (Apply (raise a', lower b')),
                CtorApply (raise a', lower b',
                  CtorThunk (a', t2'),
                  ComatchReturn (b', x, make_inner_cut b' x k)),
                t1')))
    | Pcf.Lit n -> Lit n
    | Pcf.Add (t1, t2) ->
        (* t1 + t2  where t1, t2 : Int
          Translates to: μL k. add(t1', t2', k) *)
        let t1' = map_term ctx t1 in
        let t2' = map_term ctx t2 in
        let k = Ident.fresh () in
        MuLhs (Int, k, Add (t1', t2', Variable k))
    | Pcf.Ifz (t1, t2, t3) ->
        (* ifz t1 then t2 else t3  where t1 : Int, t2 and t3 : B
          Translates to: μ k. ifz(t1') then ⟨t2' | k⟩ else ⟨t3' | k⟩
          Use μL/μR and swap cut order based on whether B is positive/negative *)
        let b = Pcf.infer_typ ctx t2 in
        let t1' = map_term ctx t1 in
        let t2' = map_term ctx t2 in
        let t3' = map_term ctx t3 in
        let k = Ident.fresh () in
        let b' = map_typ b in
        let make_mu = if is_positive b then
          (fun ty k cmd -> MuLhs (ty, k, cmd))
        else
          (fun ty k cmd -> MuRhs (ty, k, cmd))
        in
        (* For positive b': t2'/t3' are Lhs, k is Rhs, so Cut(b', t2'/t3', k)
          For negative b': t2'/t3' are Rhs, k is Lhs, so Cut(b', k, t2'/t3') *)
        let make_branch_cut b' branch k =
          if is_positive_typ b' then
            Cut (b', branch, Variable k)
          else
            Cut (b', Variable k, branch)
        in
        make_mu b' k
          (Ifz (t1', 
            make_branch_cut b' t2' k,
            make_branch_cut b' t3' k))

end