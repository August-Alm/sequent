open Common.Identifiers

type var = Ident.t

module Pcf = struct

  type typ = Int | Arrow of typ * typ

  type term =
      Var of var
    | Lam of var * typ * term
    | App of term * term
    | Let of var * term * term
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
    | Let (x, t1, t2) ->
        "let " ^ Ident.name x ^ " = " ^ pp_term t1 ^ " in " ^ pp_term t2
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
    | Let (x, t1, t2) ->
        let t1_ty = infer_typ ctx t1 in
        let ctx' = Ident.add x t1_ty ctx in
        infer_typ ctx' t2
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
    | Pack of typ (** Xtor of Raise(A) - shifts to producer **)

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
    | CtorPack of typ * term
    (** Destructors build codata (Rhs/consumer) **)
    | DtorApply of typ * typ * term * term
    | DtorReturn of typ * term
    | DtorPack of typ * term
    (** Match consumes data (Rhs/consumer) **)
    | MatchApply of typ * typ * var * var * command
    | MatchReturn of typ * var * command
    | MatchPack of typ * var * command
    (** Comatch produces codata (Lhs/producer) **)
    | ComatchApply of typ * typ * var * var * command
    | ComatchReturn of typ * var * command
    | ComatchPack of typ * var * command
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
    | CtorPack (a, arg) ->
        CtorPack (a, rename (x, y) arg)
    | DtorApply (a, b, arg, cont) ->
        DtorApply (a, b, rename (x, y) arg, rename (x, y) cont)
    | DtorReturn (a, arg) ->
        DtorReturn (a, rename (x, y) arg)
    | DtorPack (a, arg) ->
        DtorPack (a, rename (x, y) arg)
    | MatchApply (a, b, z, k, cmd) when Ident.equal z x || Ident.equal k x ->
        MatchApply (a, b, z, k, cmd)  (* Shadowing: do not rename inside *)
    | MatchApply (a, b, z, k, cmd) ->
        MatchApply (a, b, z, k, rename_cmd (x, y) cmd)
    | MatchReturn (a, z, cmd) when Ident.equal z x ->
        MatchReturn (a, z, cmd)  (* Shadowing *)
    | MatchReturn (a, z, cmd) ->
        MatchReturn (a, z, rename_cmd (x, y) cmd)
    | MatchPack (a, z, cmd) when Ident.equal z x ->
        MatchPack (a, z, cmd)  (* Shadowing *)
    | MatchPack (a, z, cmd) ->
        MatchPack (a, z, rename_cmd (x, y) cmd)
    | ComatchApply (a, b, z, k, cmd) when Ident.equal z x || Ident.equal k x ->
        ComatchApply (a, b, z, k, cmd)  (* Shadowing *)
    | ComatchApply (a, b, z, k, cmd) ->
        ComatchApply (a, b, z, k, rename_cmd (x, y) cmd)
    | ComatchReturn (a, z, cmd) when Ident.equal z x ->
        ComatchReturn (a, z, cmd)  (* Shadowing *)
    | ComatchReturn (a, z, cmd) ->
        ComatchReturn (a, z, rename_cmd (x, y) cmd)
    | ComatchPack (a, z, cmd) when Ident.equal z x ->
        ComatchPack (a, z, cmd)  (* Shadowing *)
    | ComatchPack (a, z, cmd) ->
        ComatchPack (a, z, rename_cmd (x, y) cmd)
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
    | CtorPack (a, arg) ->
        "ctor_pack[" ^ pp_typ a ^ "](" ^ pp_term arg ^ ")"
    | DtorApply (a, b, arg, cont) ->
        "dtor_apply[" ^ pp_typ a ^ ", " ^ pp_typ b ^ "](" 
          ^ pp_term arg ^ ", " ^ pp_term cont ^ ")"
    | DtorReturn (a, arg) ->
        "dtor_return[" ^ pp_typ a ^ "](" ^ pp_term arg ^ ")"
    | DtorPack (a, arg) ->
        "dtor_pack[" ^ pp_typ a ^ "](" ^ pp_term arg ^ ")"
    | MatchApply (a, b, x, k, cmd) ->
        "case { ctor_apply[" ^ pp_typ a ^ ", " ^ pp_typ b ^ "](" 
          ^ Ident.name x ^ ", " ^ Ident.name k ^ ") ⇒ " ^ pp_command cmd ^ "}"
    | MatchReturn (a, x, cmd) ->
        "case { ctor_return[" ^ pp_typ a ^ "](" 
          ^ Ident.name x ^ ") ⇒ " ^ pp_command cmd ^ "}"
    | MatchPack (a, x, cmd) ->
        "case { ctor_pack[" ^ pp_typ a ^ "](" 
          ^ Ident.name x ^ ") ⇒ " ^ pp_command cmd ^ "}"
    | ComatchApply (a, b, x, k, cmd) ->
        "cocase { dtor_apply[" ^ pp_typ a ^ ", " ^ pp_typ b ^ "](" 
          ^ Ident.name x ^ ", " ^ Ident.name k ^ ") ⇒ " ^ pp_command cmd ^ "}"
    | ComatchReturn (a, x, cmd) ->
        "cocase { dtor_return[" ^ pp_typ a ^ "](" 
          ^ Ident.name x ^ ") ⇒ " ^ pp_command cmd ^ "}"
    | ComatchPack (a, x, cmd) ->
        "cocase { dtor_pack[" ^ pp_typ a ^ "](" 
          ^ Ident.name x ^ ") ⇒ " ^ pp_command cmd ^ "}"
    | MuLhs (_, k, cmd) -> "μL " ^ Ident.name k ^ ". " ^ pp_command cmd
    | MuRhs (_, k, cmd) -> "μR " ^ Ident.name k ^ ". " ^ pp_command cmd
  
  and pp_typ =
    function
      Int -> "Int"
    | Sig (Apply (a, b)) -> "Fun(" ^ pp_typ a ^ ", " ^ pp_typ b ^ ")"
    | Sig (Return a) -> "↓" ^ pp_typ a
    | Sig (Pack a) -> "↑" ^ pp_typ a

  (* Determine the "natural chirality" of a type:
    - Int is positive (data-like), so values are Lhs
    - Sig(Return A) is positive - it's data packaging a value/computation
    - Sig(Pack A) is positive - it's data packaging a suspended computation
    - Sig(Apply ...) is negative - functions are codata-like (demand-driven) *)
  let is_positive_typ = function
    | Int -> true
    | Sig (Return _) -> true   (* Lower makes something data-like *)
    | Sig (Pack _) -> true    (* Raise makes something data-like (pack is a value) *)
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
    | CtorPack (a, arg) ->
        let arg_ty = infer_typ ctx arg in
        (* Pack suspends a computation, so arg should match natural chirality of a *)
        let expected = natural_chirality a in
        if arg_ty = expected then
          Lhs (Sig (Pack a))
        else failwith "Type error in CtorPack"
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
    | DtorPack (a, arg) ->
        let arg_ty = infer_typ ctx arg in
        let expected = natural_chirality a in
        if arg_ty = expected then
          Lhs (Sig (Pack a))  (* Producer - placed on left against MatchPack *)
        else failwith "Type error in DtorPack"
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
    | MatchPack (a, x, cmd) ->
        let ctx' = Ident.add x (natural_chirality a) ctx in
        infer_command_typ ctx' cmd |> ignore;
        Rhs (Sig (Pack a))
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
    | ComatchPack (a, x, cmd) ->
        let ctx' = Ident.add x (natural_chirality a) ctx in
        infer_command_typ ctx' cmd |> ignore;
        Rhs (Sig (Pack a))  (* Consumer - placed on right against CtorPack *)
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
  (* Raise shifts a type to producer position (pack/suspend) *)
  let raise ty = Sig (Pack ty)

  (* Determine if a PCF type is "positive" (data-like) or "negative" (codata-like) *)
  let is_positive = function
      Pcf.Int -> true
    | Pcf.Arrow _ -> false

  let rec map_typ = function
      Pcf.Int -> Int
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
    
  let rec map_term (ctx: Pcf.typ Ident.tbl) = function
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
          true ->
            (* case { ctor_apply[a', lower b'](x, k) ⇒ ⟨ctor_return[b'](body') | k⟩ } *)
            MatchApply (a', lower b', x, k,
              Cut (lower b', CtorReturn (b', body'), Variable k))
        | false ->
            (* case { ctor_apply[raise a', lower b'](x', k) ⇒
                 ⟨x' | case { ctor_pack[a'](x) ⇒ ⟨ctor_return[b'](body') | k⟩ }⟩ } *)
            let x' = Ident.fresh () in
            MatchApply (raise a', lower b', x', k,
              Cut (raise a',
                Variable x',
                MatchPack (a', x, Cut (lower b', CtorReturn (b', body'), Variable k)))))
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
          true ->
            (* μ k. ⟨ctor_apply[a', lower b'](t2', cocase{dtor_return[b'](x) ⇒ ⟨x | k⟩}) | t1'⟩ *)
            let x = Ident.fresh () in
            make_mu b' k
              (Cut (Sig (Apply (a', lower b')),
                CtorApply (a', lower b', t2',
                  ComatchReturn (b', x, make_inner_cut b' x k)),
                t1'))
        | false ->
            (* μ k. ⟨ctor_apply[raise a', lower b'](ctor_pack[a'](t2'), 
                      cocase{dtor_return[b'](x) ⇒ ⟨x | k⟩}) | t1'⟩ *)
            let x = Ident.fresh () in
            make_mu b' k
              (Cut (Sig (Apply (raise a', lower b')),
                CtorApply (raise a', lower b',
                  CtorPack (a', t2'),
                  ComatchReturn (b', x, make_inner_cut b' x k)),
                t1')))
    | Pcf.Let (x, t1, t2) ->
        (* let x = t1 in t2  is equivalent to  (λx:A. t2) t1
           where A is the type of t1 *)
        let a = Pcf.infer_typ ctx t1 in
        map_term ctx (Pcf.App (Pcf.Lam (x, a, t2), t1))
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

module Cut = struct

  type typ = Seq.typ
  type chiral_typ = Seq.chiral_typ
  type signature = Seq.xtor
  type xtor = Seq.xtor

  type command =
      (* ⟨Cₙ(Γ) | μ̃x.s⟩ or ⟨μα.s | Dₙ(Γ)⟩ *)
      Let of var * xtor * var list * command
      (* ⟨x | case {C(Γ) ⇒ s}⟩ or ⟨cocase {D(Γ) ⇒ s} | α⟩ *)
    | Switch of signature * var * branch
      (* [⟨cocase {D(Γ) ⇒ s₁} | μ̃x.s⟩ or ⟨μα.s | case {C(Γ) ⇒ s₁}⟩ *)
    | New of signature * var * branch * command
      (* ⟨C(Γ) | α⟩ or ⟨x | D(Γ)⟩ *)
    | Invoke of var * xtor * var list
      (* ⟨v | k⟩ at Int - pass value to continuation *)
    | Axiom of var * var
      (* lit n {(v) ⇒ s} *)
    | Lit of int * var * command
      (* add(x, y) {(v) ⇒ s} *)
    | Add of var * var * var * command
      (* ifz(v) {() ⇒ sThen; () ⇒ sElse} *)
    | Ifz of var * command * command
      (* ret ty v - return the value of v at type ty (terminal) *)
    | Ret of Seq.typ * var
      (* end *)
    | End
  
  and branch = var list * command

  let pp_xtor = function
      Seq.Apply (a, b) -> "apply[" ^ Seq.pp_typ a ^ ", " ^ Seq.pp_typ b ^ "]"
    | Seq.Return a -> "return[" ^ Seq.pp_typ a ^ "]"
    | Seq.Pack a -> "pack[" ^ Seq.pp_typ a ^ "]"

  let pp_vars vs = String.concat ", " (List.map Ident.name vs)

  let indent n = String.make (n * 2) ' '

  let rec pp_cmd n = function
      Let (x, xtor, args, body) ->
        indent n ^ "let " ^ Ident.name x ^ " = " ^ pp_xtor xtor ^ "(" ^ pp_vars args ^ ");\n" ^
        pp_cmd n body
    | Switch (sig_, x, (params, body)) ->
        indent n ^ "switch " ^ Ident.name x ^ " {\n" ^
        indent (n+1) ^ pp_xtor sig_ ^ "(" ^ pp_vars params ^ ") ⇒\n" ^
        pp_cmd (n+1) body ^ "\n" ^
        indent n ^ "}"
    | New (sig_, x, (params, branch), body) ->
        indent n ^ "new " ^ Ident.name x ^ " = {\n" ^
        indent (n+1) ^ pp_xtor sig_ ^ "(" ^ pp_vars params ^ ") ⇒\n" ^
        pp_cmd (n+1) branch ^ "\n" ^
        indent n ^ "};\n" ^
        pp_cmd n body
    | Invoke (x, xtor, args) ->
        indent n ^ Ident.name x ^ "." ^ pp_xtor xtor ^ "(" ^ pp_vars args ^ ")"
    | Axiom (v, k) ->
        indent n ^ "axiom(" ^ Ident.name v ^ ", " ^ Ident.name k ^ ")"
    | Lit (n_, v, body) ->
        indent n ^ "let " ^ Ident.name v ^ " = " ^ string_of_int n_ ^ ";\n" ^
        pp_cmd n body
    | Add (a, b, r, body) ->
        indent n ^ "let " ^ Ident.name r ^ " = " ^ Ident.name a ^ " + " ^ Ident.name b ^ ";\n" ^
        pp_cmd n body
    | Ifz (v, then_cmd, else_cmd) ->
        indent n ^ "ifz " ^ Ident.name v ^ " {\n" ^
        pp_cmd (n+1) then_cmd ^ "\n" ^
        indent n ^ "} else {\n" ^
        pp_cmd (n+1) else_cmd ^ "\n" ^
        indent n ^ "}"
    | End -> indent n ^ "end"
    | Ret (ty, v) -> indent n ^ "ret[" ^ Seq.pp_typ ty ^ "] " ^ Ident.name v

  let pp_command cmd = pp_cmd 0 cmd

  (** Abstract machine semantics *)
  module Machine = struct
    
    (** Values in the machine *)
    type value =
        Producer of xtor * env        (** {m; E} - a constructor with its environment *)
      | Consumer of env * branch      (** {E; b} - a branch with its environment *)
      | IntVal of int                 (** Literals *)

    (** Environment maps variables to values *)
    and env = value Ident.tbl

    (** Configuration: command + environment *)
    type config = command * env

    let empty_env : env = Ident.emptytbl

    let lookup (e: env) (x: var) : value =
      match Ident.find_opt x e with
        Some v -> v
      | None -> failwith ("unbound variable: " ^ Ident.name x)

    let lookup_opt (e: env) (x: var) : value option =
      Ident.find_opt x e

    let lookup_int (e: env) (x: var) : int =
      match lookup e x with
        IntVal n -> n
      | _ -> failwith ("expected int value for: " ^ Ident.name x)

    let lookup_producer (e: env) (x: var) : xtor * env =
      match lookup e x with
        Producer (m, e0) -> (m, e0)
      | _ -> failwith ("expected producer value for: " ^ Ident.name x)

    let lookup_consumer (e: env) (x: var) : env * branch =
      match lookup e x with
        Consumer (e0, b) -> (e0, b)
      | _ -> failwith ("expected consumer value for: " ^ Ident.name x)

    let extend (e: env) (x: var) (v: value) : env =
      Ident.add x v e

    (** Build sub-environment for a list of variables *)
    let sub_env (e: env) (vars: var list) : env =
      List.fold_left (fun acc x -> extend acc x (lookup e x)) empty_env vars

    (** Pretty-print a value *)
    let pp_value = function
        Producer (m, _) -> "{" ^ pp_xtor m ^ "; ...}"
      | Consumer (_, (params, _)) -> "{...; (" ^ pp_vars params ^ ") ⇒ ...}"
      | IntVal n -> string_of_int n

    (** Pretty-print environment (just the bindings) *)
    let pp_env (e: env) : string =
      let bindings = Ident.to_list e in
      String.concat ", " (List.map (fun (x, v) -> Ident.name x ^ " → " ^ pp_value v) bindings)

    (** Pretty-print configuration *)
    let pp_config ((cmd, e): config) : string =
      "⟨" ^ pp_command cmd ^ " ∥ {" ^ pp_env e ^ "}⟩"

    (** Merge two environments (e2 values override e1 on conflicts) *)
    let merge_env (e1: env) (e2: env) : env =
      List.fold_left (fun acc (x, v) -> extend acc x v) e1 (Ident.to_list e2)

    (** Single step of the machine. Returns None if stuck or terminal. *)
    let step ((cmd, e): config) : config option =
      match cmd with
      (* (let) ⟨let v = m(Γ); s ∥ E⟩ → ⟨s ∥ E, v → {m; E|Γ}⟩ 
         Creates a producer: the xtor m with captured environment for args *)
        Let (v, m, args, body) ->
          let e0 = sub_env e args in
          let e' = extend e v (Producer (m, e0)) in
          Some (body, e')

      (* (new) ⟨new v = {(Γ) ⇒ b}; s ∥ E⟩ → ⟨s ∥ E, v → {E; b}⟩
         Creates a consumer: captures current env, branch will bind params when invoked *)
      | New (_, v, branch, body) ->
          let e' = extend e v (Consumer (e, branch)) in
          Some (body, e')

      (* (switch) ⟨switch v {(Γ) ⇒ b} ∥ E⟩
         For producers: destructure and bind captured values to branch params
         For consumers: this is an eta-expansion - bind the consumer itself to params *)
      | Switch (_, v, (params, branch_body)) ->
          (match lookup e v with
           | Producer (_m, e0) ->
               (* Destructure producer: e0 has captured values, bind to params *)
               (* Note: e0 was built with fold_left, so to_list is reversed. Fix order. *)
               let e0_list = List.rev (Ident.to_list e0) in
               let e' = List.fold_left2 (fun acc p (_, v) -> extend acc p v) e params e0_list in
               Some (branch_body, e')
           | Consumer _ as c ->
               (* For a consumer value, the switch "unpacks" it - but consumers have 
                  no components to unpack. This represents eta-expansion where we 
                  just re-package the same consumer. Bind the whole consumer to the first param? 
                  Actually, for function types, params are [arg, cont] and we're forwarding. *)
               (* The consumer is the function itself; bind it to the single param (the cont) *)
               if List.length params = 2 then
                 (* Apply pattern: params = [arg, cont]; forward consumer to cont *)
                 let e' = List.fold_left (fun acc p -> extend acc p c) e params in
                 Some (branch_body, e')
               else
                 failwith "switch on consumer with unexpected params"
           | IntVal n ->
               (* For int values, bind to the single param *)
               let e' = extend e (List.hd params) (IntVal n) in
               Some (branch_body, e'))

      (* (invoke) ⟨v.m(Γ) ∥ E, v → {E0; b}⟩ → ⟨b ∥ E0[params↦E(Γ)]⟩
         Invokes a consumer: binds args to branch params in captured env *)
      | Invoke (v, _m, args) ->
          let (e0, (params, branch_body)) = lookup_consumer e v in
          (* Bind the current values of args to the branch params *)
          let arg_vals = List.map (fun a -> lookup e a) args in
          (* Merge current env with captured env, then add params *)
          let e_merged = merge_env e0 e in
          let e' = List.fold_left2 extend e_merged params arg_vals in
          Some (branch_body, e')

      (* (lit) ⟨let v = n; s ∥ E⟩ → ⟨s ∥ E, v → n⟩ *)
      | Lit (n, v, body) ->
          let e' = extend e v (IntVal n) in
          Some (body, e')

      (* (add) ⟨let v = v1 + v2; s ∥ E⟩ → ⟨s ∥ E, v → E(v1) + E(v2)⟩ *)
      | Add (v1, v2, v, body) ->
          (match (lookup_opt e v1, lookup_opt e v2) with
           | (Some (IntVal n1), Some (IntVal n2)) ->
               let e' = extend e v (IntVal (n1 + n2)) in
               Some (body, e')
           | (Some val1, Some val2) ->
               failwith (Printf.sprintf "add: expected ints, got %s=%s, %s=%s"
                 (Ident.name v1) (pp_value val1) (Ident.name v2) (pp_value val2))
           | (None, _) -> failwith ("add: unbound " ^ Ident.name v1)
           | (_, None) -> failwith ("add: unbound " ^ Ident.name v2))

      (* (ifz) ⟨ifz v {s1} {s2} ∥ E⟩ → if E(v) = 0 then ⟨s1 ∥ E⟩ else ⟨s2 ∥ E⟩ *)
      | Ifz (v, then_cmd, else_cmd) ->
          let n = lookup_int e v in
          if n = 0 then Some (then_cmd, e)
          else Some (else_cmd, e)

      (* (axiom) ⟨axiom v₁ v₂ ∥ E⟩ - interaction between producer and consumer *)
      | Axiom (v1, v2) ->
          (match lookup_opt e v2 with
            None ->
              (* v2 is unbound (open term) - stuck, but record the value *)
              None
          | Some (Consumer (e0, (params, branch_body))) ->
              (match lookup e v1 with
               | IntVal n ->
                   (* Int value passed to continuation - bind the int to the param *)
                   let e' = extend e0 (List.hd params) (IntVal n) in
                   Some (branch_body, e')
               | Producer (_m, e1) ->
                   (* Producer passed to consumer - bind producer's values to params *)
                   let e1_list = Ident.to_list e1 in
                   let e' = List.fold_left2 (fun acc p (_, v) -> extend acc p v) e0 params e1_list in
                   Some (branch_body, e')
               | Consumer _ ->
                   failwith "axiom: expected producer or int, got consumer")
          | Some _ ->
              failwith "axiom: v2 should be a consumer")

      | End -> None

      (* (ret) ⟨ret[ty] v ∥ E⟩ → terminal, returns E(v) *)
      | Ret _ -> None

    (** Check if machine terminated with a result *)
    let get_result ((cmd, e): config) : value option =
      match cmd with
        Ret (_, v) -> Some (lookup e v)
      | Axiom (v1, v2) when lookup_opt e v2 = None ->
          Some (lookup e v1)
      | _ -> None

    (** Check if machine is stuck on an open term (axiom with unbound continuation) *)
    let is_open_result ((cmd, e): config) : (var * value) option =
      match cmd with
        Axiom (v1, v2) when lookup_opt e v2 = None ->
          Some (v2, lookup e v1)
      | _ -> None

    (** Short name for a command (for tracing) *)
    let cmd_name = function
        Let (v, _, _, _) -> "let " ^ Ident.name v
      | New (_, v, _, _) -> "new " ^ Ident.name v
      | Switch (_, v, _) -> "switch " ^ Ident.name v
      | Invoke (v, xtor, _) -> Ident.name v ^ "." ^ pp_xtor xtor
      | Axiom (v, k) -> "axiom(" ^ Ident.name v ^ ", " ^ Ident.name k ^ ")"
      | Lit (n, v, _) -> "lit " ^ string_of_int n ^ " → " ^ Ident.name v
      | Add (a, b, v, _) -> Ident.name a ^ " + " ^ Ident.name b ^ " → " ^ Ident.name v
      | Ifz (v, _, _) -> "ifz " ^ Ident.name v
      | End -> "end"
      | Ret (_, v) -> "ret " ^ Ident.name v

    (** Run the machine until it stops. Returns (final_config, step_count) *)
    let rec run ?(trace=false) ?(steps=0) (cfg: config) : config * int =
      let (cmd, e) = cfg in
      if trace then 
        Printf.printf "    [%d] %s | env has %d bindings\n"
          steps (cmd_name cmd) (List.length (Ident.to_list e));
      match step cfg with
        None -> (cfg, steps)
      | Some cfg' -> run ~trace ~steps:(steps + 1) cfg'

    (** Run with tracing *)
    let rec run_trace (cfg: config) : config list =
      cfg :: (match step cfg with
                None -> []
              | Some cfg' -> run_trace cfg')

    (** Initialize and run a command. Returns (final_config, step_count) *)
    let eval ?(trace=false) (cmd: command) : config * int =
      run ~trace (cmd, empty_env)

    (** Initialize and run with trace *)
    let eval_trace (cmd: command) : config list =
      run_trace (cmd, empty_env)
  end

end

module Focus = struct
  open Seq

  (** Get the xtor from a Sig type *)
  let xtor_of_typ : typ -> xtor = function
      Int -> failwith "Int has no xtor"
    | Sig x -> x

  (** Generate fresh parameter names for an xtor *)
  let fresh_params (x: xtor) : var list =
    match x with
      Apply (_, _) -> [Ident.fresh (); Ident.fresh ()]
    | Return _ -> [Ident.fresh ()]
    | Pack _ -> [Ident.fresh ()]

  (** Extract xtor and arguments from a constructor/destructor term *)
  let ctor_info : term -> xtor * term list = function
      CtorApply (a, b, arg, cont) -> (Apply (a, b), [arg; cont])
    | CtorReturn (a, arg) -> (Return a, [arg])
    | CtorPack (a, arg) -> (Pack a, [arg])
    | DtorApply (a, b, arg, cont) -> (Apply (a, b), [arg; cont])
    | DtorReturn (a, arg) -> (Return a, [arg])
    | DtorPack (a, arg) -> (Pack a, [arg])
    | _ -> failwith "Not a constructor/destructor"

  (** Extract xtor, params, and body from a match/comatch term *)
  let match_info : term -> xtor * var list * command = function
      MatchApply (a, b, x, k, cmd) -> (Apply (a, b), [x; k], cmd)
    | MatchReturn (a, x, cmd) -> (Return a, [x], cmd)
    | MatchPack (a, x, cmd) -> (Pack a, [x], cmd)
    | ComatchApply (a, b, x, k, cmd) -> (Apply (a, b), [x; k], cmd)
    | ComatchReturn (a, x, cmd) -> (Return a, [x], cmd)
    | ComatchPack (a, x, cmd) -> (Pack a, [x], cmd)
    | _ -> failwith "Not a match/comatch"

  (** Substitute variables: replace params with args in cmd *)
  let subst_params (params: var list) (args: var list) (cmd: command) : command =
    List.fold_left2 (fun c p a -> rename_cmd (p, a) c) cmd params args

  (** Substitute a term for a variable in a Seq command.
      This enables on-demand substitution for pack optimization. *)
  let rec subst_term_in_cmd (x: var) (t: term) (cmd: command) : command =
    match cmd with
    | Cut (ty, lhs, rhs) ->
        Cut (ty, subst_term_in_term x t lhs, subst_term_in_term x t rhs)
    | Add (t1, t2, t3) ->
        Add (subst_term_in_term x t t1, subst_term_in_term x t t2, subst_term_in_term x t t3)
    | Ifz (cond, then_cmd, else_cmd) ->
        Ifz (subst_term_in_term x t cond, subst_term_in_cmd x t then_cmd, subst_term_in_cmd x t else_cmd)
    | End -> End

  and subst_term_in_term (x: var) (t: term) (tm: term) : term =
    match tm with
    | Variable y when Ident.equal y x -> t
    | Variable y -> Variable y
    | Lit n -> Lit n
    | CtorApply (a, b, arg, cont) ->
        CtorApply (a, b, subst_term_in_term x t arg, subst_term_in_term x t cont)
    | CtorReturn (a, arg) -> CtorReturn (a, subst_term_in_term x t arg)
    | CtorPack (a, arg) -> CtorPack (a, subst_term_in_term x t arg)
    | DtorApply (a, b, arg, cont) ->
        DtorApply (a, b, subst_term_in_term x t arg, subst_term_in_term x t cont)
    | DtorReturn (a, arg) -> DtorReturn (a, subst_term_in_term x t arg)
    | DtorPack (a, arg) -> DtorPack (a, subst_term_in_term x t arg)
    | MatchApply (a, b, y, k, cmd) ->
        if Ident.equal y x || Ident.equal k x then tm  (* shadowing *)
        else MatchApply (a, b, y, k, subst_term_in_cmd x t cmd)
    | MatchReturn (a, y, cmd) ->
        if Ident.equal y x then tm else MatchReturn (a, y, subst_term_in_cmd x t cmd)
    | MatchPack (a, y, cmd) ->
        if Ident.equal y x then tm else MatchPack (a, y, subst_term_in_cmd x t cmd)
    | ComatchApply (a, b, y, k, cmd) ->
        if Ident.equal y x || Ident.equal k x then tm
        else ComatchApply (a, b, y, k, subst_term_in_cmd x t cmd)
    | ComatchReturn (a, y, cmd) ->
        if Ident.equal y x then tm else ComatchReturn (a, y, subst_term_in_cmd x t cmd)
    | ComatchPack (a, y, cmd) ->
        if Ident.equal y x then tm else ComatchPack (a, y, subst_term_in_cmd x t cmd)
    | MuLhs (ty, y, cmd) ->
        if Ident.equal y x then tm else MuLhs (ty, y, subst_term_in_cmd x t cmd)
    | MuRhs (ty, y, cmd) ->
        if Ident.equal y x then tm else MuRhs (ty, y, subst_term_in_cmd x t cmd)

  (** Substitute multiple terms for params *)
  let subst_terms_in_cmd (params: var list) (terms: term list) (cmd: command) : command =
    List.fold_left2 (fun c p t -> subst_term_in_cmd p t c) cmd params terms

  (** Bind multiple terms to variables *)
  let rec bind_terms (terms: term list) (k: var list -> Cut.command) : Cut.command =
    match terms with
      [] -> k []
    | t :: rest ->
        bind_term t (fun v ->
          bind_terms rest (fun vs -> k (v :: vs)))

  (** Bind a single term to a variable, calling continuation with the variable *)
  and bind_term (t: term) (k: var -> Cut.command) : Cut.command =
    match t with
      Variable x -> k x
    | Lit n ->
        let v = Ident.fresh () in
        Cut.Lit (n, v, k v)
    (* Constructors become Let bindings *)
    | CtorApply (a, b, arg, cont) ->
        bind_terms [arg; cont] (fun vs ->
          let x = Ident.fresh () in
          Cut.Let (x, Apply (a, b), vs, k x))
    | CtorReturn (a, arg) ->
        bind_term arg (fun v ->
          let x = Ident.fresh () in
          Cut.Let (x, Return a, [v], k x))
    | CtorPack (a, arg) ->
        bind_term arg (fun v ->
          let x = Ident.fresh () in
          Cut.Let (x, Pack a, [v], k x))
    (* Destructors also become Let bindings (same as Ctor in collapsed view) *)
    | DtorApply (a, b, arg, cont) ->
        bind_terms [arg; cont] (fun vs ->
          let x = Ident.fresh () in
          Cut.Let (x, Apply (a, b), vs, k x))
    | DtorReturn (a, arg) ->
        bind_term arg (fun v ->
          let x = Ident.fresh () in
          Cut.Let (x, Return a, [v], k x))
    | DtorPack (a, arg) ->
        bind_term arg (fun v ->
          let x = Ident.fresh () in
          Cut.Let (x, Pack a, [v], k x))
    (* Matches become New bindings *)
    | MatchApply (a, b, x, kv, cmd) ->
        let bound = Ident.fresh () in
        Cut.New (Apply (a, b), bound, ([x; kv], transform_command cmd), k bound)
    | MatchReturn (a, x, cmd) ->
        let bound = Ident.fresh () in
        Cut.New (Return a, bound, ([x], transform_command cmd), k bound)
    | MatchPack (a, x, cmd) ->
        let bound = Ident.fresh () in
        Cut.New (Pack a, bound, ([x], transform_command cmd), k bound)
    (* Comatches also become New bindings *)
    | ComatchApply (a, b, x, kv, cmd) ->
        let bound = Ident.fresh () in
        Cut.New (Apply (a, b), bound, ([x; kv], transform_command cmd), k bound)
    | ComatchReturn (a, x, cmd) ->
        let bound = Ident.fresh () in
        Cut.New (Return a, bound, ([x], transform_command cmd), k bound)
    | ComatchPack (a, x, cmd) ->
        let bound = Ident.fresh () in
        Cut.New (Pack a, bound, ([x], transform_command cmd), k bound)
    (* MuLhs: bind continuation, transform body *)
    | MuLhs (ty, x, cmd) ->
        (match ty with
          Int ->
            (* For Int: the body will produce a value that jumps to x.
               We create a New that captures this pattern. *)
            let bound = Ident.fresh () in
            (* Transform body, replacing x with bound *)
            let body' = transform_command (rename_cmd (x, bound) cmd) in
            (* Wrap: when body produces result via Jump(v, bound), 
               we want to continue with k bound. But this requires CPS... 
               For now, use a simpler approach: just transform and let caller handle *)
            bind_mu_int bound body' k
        | Sig xtor ->
            let bound = Ident.fresh () in
            let params = fresh_params xtor in
            Cut.New (xtor, x, 
              (params, Cut.Let (bound, xtor, params, k bound)),
              transform_command cmd))
    (* MuRhs: similar but for consumers *)
    | MuRhs (ty, x, cmd) ->
        (match ty with
          Int ->
            let bound = Ident.fresh () in
            bind_mu_int bound (transform_command (rename_cmd (x, bound) cmd)) k
        | Sig xtor ->
            let bound = Ident.fresh () in
            let params = fresh_params xtor in
            Cut.New (xtor, x,
              (params, Cut.Let (bound, xtor, params, k bound)),
              transform_command cmd))

  (** Handle MuLhs/MuRhs at Int type - we need to thread the continuation *)
  and bind_mu_int (bound: var) (body: Cut.command) (k: var -> Cut.command) : Cut.command =
    (* The body should end with Jump(v, bound) for some v.
      We want to replace that with: let result = v in k result
      For now, just return body - proper handling would need CPS transform *)
    replace_int_axiom bound body k

  (** Replace Axiom(v, target) with continuation applied to v *)
  and replace_int_axiom (target: var) (cmd: Cut.command) (k: var -> Cut.command) : Cut.command =
    match cmd with
      Cut.Axiom (v, dest) when Ident.equal dest target ->
        k v
    | Cut.Axiom (v, dest) -> Cut.Axiom (v, dest)
    | Cut.Let (x, xtor, args, body) ->
        Cut.Let (x, xtor, args, replace_int_axiom target body k)
    | Cut.Switch (sig_, x, (params, body)) ->
        Cut.Switch (sig_, x, (params, replace_int_axiom target body k))
    | Cut.New (sig_, x, (params, branch), body) ->
        Cut.New (sig_, x, (params, replace_int_axiom target branch k),
                 replace_int_axiom target body k)
    | Cut.Invoke (x, xtor, args) -> Cut.Invoke (x, xtor, args)
    | Cut.Lit (n, x, body) ->
        Cut.Lit (n, x, replace_int_axiom target body k)
    | Cut.Add (a, b, r, body) ->
        Cut.Add (a, b, r, replace_int_axiom target body k)
    | Cut.Ifz (x, then_cmd, else_cmd) ->
        Cut.Ifz (x, replace_int_axiom target then_cmd k,
                    replace_int_axiom target else_cmd k)
    | Cut.End -> Cut.End
    | Cut.Ret (ty, v) -> Cut.Ret (ty, v)

  (** Main transformation: Seq.command -> Cut.command *)
  and transform_command : command -> Cut.command = function
      End -> Cut.End
    | Add (t1, t2, t3) ->
        bind_term t1 (fun v1 ->
          bind_term t2 (fun v2 ->
            match t3 with
            | Variable k ->
                let r = Ident.fresh () in
                Cut.Add (v1, v2, r, Cut.Axiom (r, k))
            | MuRhs (Int, a, cmd) ->
                Cut.Add (v1, v2, a, transform_command cmd)
            | _ -> failwith "Add continuation must be Variable or MuRhs"))
    | Ifz (t, cmd1, cmd2) ->
        bind_term t (fun v ->
          Cut.Ifz (v, transform_command cmd1, transform_command cmd2))
    | Cut (ty, lhs, rhs) ->
        transform_cut ty lhs rhs

  (** Transform a Cut based on the shapes of lhs and rhs *)
  and transform_cut ty lhs rhs =
    match ty with
      Int -> transform_cut_int lhs rhs
    | Sig _ -> transform_cut_sig ty lhs rhs

  (** Transform cuts at Int type *)
  and transform_cut_int lhs rhs =
    match lhs, rhs with
      Variable x, Variable y ->
        Cut.Axiom (x, y)
    | Variable x, MuRhs (_, a, cmd) ->
        transform_command (rename_cmd (a, x) cmd)
    | Lit n, Variable y ->
        let v = Ident.fresh () in
        Cut.Lit (n, v, Cut.Axiom (v, y))
    | Lit n, MuRhs (_, a, cmd) ->
        Cut.Lit (n, a, transform_command cmd)
    | MuLhs (_, x, cmd), Variable y ->
        transform_command (rename_cmd (x, y) cmd)
    | MuLhs (_, x, mu_cmd), MuRhs (_, a, rhs_cmd) ->
        (* Connect: result of mu_cmd goes to a in rhs_cmd *)
        let transformed_mu = transform_command (rename_cmd (x, a) mu_cmd) in
        let transformed_rhs = transform_command rhs_cmd in
        replace_int_axiom a transformed_mu (fun v ->
          subst_var_cmd a v transformed_rhs)
    | _ -> failwith "ill-typed cut at Int"

  (** Substitute a variable in a command *)
  and subst_var_cmd (x: var) (v: var) (cmd: Cut.command) : Cut.command =
    let sv y = if Ident.equal y x then v else y in
    let sv_list = List.map sv in
    match cmd with
      Cut.Let (y, xtor, args, body) ->
        if Ident.equal y x then Cut.Let (y, xtor, sv_list args, body)
        else Cut.Let (y, xtor, sv_list args, subst_var_cmd x v body)
    | Cut.Switch (sig_, y, (params, body)) ->
        if List.exists (Ident.equal x) params then
          Cut.Switch (sig_, sv y, (params, body))
        else
          Cut.Switch (sig_, sv y, (params, subst_var_cmd x v body))
    | Cut.New (sig_, y, (params, branch), body) ->
        let branch' = if List.exists (Ident.equal x) params then branch
                      else subst_var_cmd x v branch in
        let body' = if Ident.equal y x then body
                    else subst_var_cmd x v body in
        Cut.New (sig_, y, (params, branch'), body')
    | Cut.Invoke (y, xtor, args) ->
        Cut.Invoke (sv y, xtor, sv_list args)
    | Cut.Axiom (y, k) ->
        Cut.Axiom (sv y, sv k)
    | Cut.Lit (n, y, body) ->
        if Ident.equal y x then Cut.Lit (n, y, body)
        else Cut.Lit (n, y, subst_var_cmd x v body)
    | Cut.Add (a, b, r, body) ->
        if Ident.equal r x then Cut.Add (sv a, sv b, r, body)
        else Cut.Add (sv a, sv b, r, subst_var_cmd x v body)
    | Cut.Ifz (y, then_cmd, else_cmd) ->
        Cut.Ifz (sv y, subst_var_cmd x v then_cmd, subst_var_cmd x v else_cmd)
    | Cut.End -> Cut.End
    | Cut.Ret (ty, y) -> Cut.Ret (ty, sv y)

  (** Transform cuts at Sig types *)
  and transform_cut_sig ty lhs rhs =
    let xtor = xtor_of_typ ty in
    match lhs, rhs with
    (* Variable | Variable: eta-expand *)
      Variable x, Variable y ->
        let params = fresh_params xtor in
        Cut.Switch (xtor, x, (params, Cut.Invoke (y, xtor, params)))

    (* Variable | Match/Comatch: Switch *)
    | Variable x, (MatchApply _ | MatchReturn _ | MatchPack _ |
                   ComatchApply _ | ComatchReturn _ | ComatchPack _ as m) ->
        let (_, params, cmd) = match_info m in
        Cut.Switch (xtor, x, (params, transform_command cmd))

    (* Variable | MuRhs: substitute *)
    | Variable x, MuRhs (_, a, cmd) ->
        transform_command (rename_cmd (a, x) cmd)

    (* Ctor/Dtor | Variable: Invoke *)
    | (CtorApply _ | CtorReturn _ | CtorPack _ |
       DtorApply _ | DtorReturn _ | DtorPack _ as c), Variable y ->
        let (xtor, args) = ctor_info c in
        bind_terms args (fun arg_vars ->
          Cut.Invoke (y, xtor, arg_vars))

    (* CtorPack/DtorPack | MatchPack/ComatchPack: direct substitution without binding *)
    (* This eliminates the pack/unpack pattern by inlining directly *)
    | (CtorPack (a, arg) | DtorPack (a, arg)),
      (MatchPack (a', x, cmd) | ComatchPack (a', x, cmd)) when a = a' ->
        (* The pack and unpack cancel: just bind arg to x *)
        bind_term arg (fun v ->
          transform_command (rename_cmd (x, v) cmd))

    (* Ctor/Dtor | Match/Comatch: inline the branch using term-level substitution *)
    (* This allows CtorPack args to be substituted as terms, so they can meet MatchPack directly *)
    | (CtorApply _ | CtorReturn _ | CtorPack _ |
       DtorApply _ | DtorReturn _ | DtorPack _ as c),
      (MatchApply _ | MatchReturn _ | MatchPack _ |
       ComatchApply _ | ComatchReturn _ | ComatchPack _ as m) ->
        let (_, args) = ctor_info c in
        let (_, params, cmd) = match_info m in
        (* Substitute terms directly into the command, then transform *)
        transform_command (subst_terms_in_cmd params args cmd)

    (* Ctor/Dtor | MuRhs: Let binding *)
    | (CtorApply _ | CtorReturn _ | CtorPack _ |
       DtorApply _ | DtorReturn _ | DtorPack _ as c), MuRhs (_, a, cmd) ->
        let (xtor, args) = ctor_info c in
        bind_terms args (fun arg_vars ->
          Cut.Let (a, xtor, arg_vars, transform_command cmd))

    (* Match/Comatch | Variable: bind the match and invoke on k *)
    | (MatchApply _ | MatchReturn _ | MatchPack _ |
       ComatchApply _ | ComatchReturn _ | ComatchPack _ as m), Variable y ->
        bind_term m (fun x ->
          let params = fresh_params xtor in
          Cut.Switch (xtor, x, (params, Cut.Invoke (y, xtor, params))))

    (* Match/Comatch | Match/Comatch: eta-expand *)
    | (MatchApply _ | MatchReturn _ | MatchPack _ |
       ComatchApply _ | ComatchReturn _ | ComatchPack _ as m1),
      (MatchApply _ | MatchReturn _ | MatchPack _ |
       ComatchApply _ | ComatchReturn _ | ComatchPack _ as m2) ->
        bind_term m1 (fun x ->
          let (_, params, cmd) = match_info m2 in
          Cut.Switch (xtor, x, (params, transform_command cmd)))

    (* Match/Comatch | MuRhs: bind the match *)
    | (MatchApply _ | MatchReturn _ | MatchPack _ |
       ComatchApply _ | ComatchReturn _ | ComatchPack _ as m), MuRhs (_, a, cmd) ->
        bind_term m (fun x ->
          transform_command (rename_cmd (a, x) cmd))

    (* MuLhs | Variable: substitute *)
    | MuLhs (_, x, cmd), Variable y ->
        transform_command (rename_cmd (x, y) cmd)

    (* MuLhs | Match/Comatch: New *)
    | MuLhs (_, x, mu_cmd),
      (MatchApply _ | MatchReturn _ | MatchPack _ |
       ComatchApply _ | ComatchReturn _ | ComatchPack _ as m) ->
        let (xtor, params, match_cmd) = match_info m in
        Cut.New (xtor, x, (params, transform_command match_cmd), 
                 transform_command mu_cmd)

    (* MuLhs | MuRhs: New with Let *)
    | MuLhs (_, x, mu_cmd), MuRhs (_, a, rhs_cmd) ->
        let params = fresh_params xtor in
        Cut.New (xtor, x,
          (params, Cut.Let (a, xtor, params, transform_command rhs_cmd)),
          transform_command mu_cmd)

    | _ -> failwith "ill-typed cut at Sig type"

  (** Entry point: transform a Seq command to Cut command *)
  let focus (cmd: command) : Cut.command =
    transform_command cmd

end