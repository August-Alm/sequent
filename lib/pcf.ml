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

  type kind =
      Positive
    | Negative
    | Arrow of kind * kind

  type typ =
      Pos of pos_typ
    | Neg of neg_typ
  
  and pos_typ =
      Int 
    | Data of xtor

  and neg_typ =
      Code of xtor
  
  and xtor =
      Apply of pos_typ * neg_typ (** Xtor of Fun(A, B) *)
    | Return of pos_typ (** Xtor of Lower(A) *)
    | Thunk of neg_typ (** Xtor of Raise(A) *)

  type chiral_typ = Lhs of typ | Rhs of typ

  type parity = Even | Odd

  type command =
      CutPos of pos_typ * term * term
    | CutNeg of neg_typ * term * term
    | Add of term * term * term
    | Ifz of term * command * command
    | End

  and term =
      Variable of var
    | Lit of int
    | CtorApply of pos_typ * neg_typ * term * term
    | CtorReturn of pos_typ * term
    | CtorThunk of neg_typ * term
    | DtorApply of pos_typ * neg_typ * term * term
    | DtorReturn of pos_typ * term
    | DtorThunk of neg_typ * term
    | MatchApply of pos_typ * neg_typ * var * var * command
    | MatchReturn of pos_typ * var * command
    | MatchEval of neg_typ * var * command
    | ComatchApply of pos_typ * neg_typ * var * var * command
    | ComatchReturn of pos_typ * var * command
    | ComatchEval of neg_typ * var * command
    | MuLhsPos of pos_typ * var * command
    | MuRhsPos of pos_typ * var * command
    | MuLhsNeg of neg_typ * var * command
    | MuRhsNeg of neg_typ * var * command

  let rec rename ((x, y): var * var) =
    function
      Variable z when Ident.equal z x -> Variable y
    | Variable z -> Variable z
    | Lit n -> Lit n
    | CtorApply (a, b, arg, cont) ->
        CtorApply (a, b, rename (x, y) arg, rename (x, y) cont)
    | CtorReturn (a, arg) ->
        CtorReturn (a, rename (x, y) arg)
    | CtorThunk (b, arg) ->
        CtorThunk (b, rename (x, y) arg)
    | DtorApply (a, b, arg, cont) ->
        DtorApply (a, b, rename (x, y) arg, rename (x, y) cont)
    | DtorReturn (a, arg) ->
        DtorReturn (a, rename (x, y) arg)
    | DtorThunk (b, arg) ->
        DtorThunk (b, rename (x, y) arg)
    | MatchApply (a, b, z, k, cmd) when Ident.equal z x || Ident.equal k x ->
        MatchApply (a, b, z, k, cmd)  (* Shadowing: do not rename inside *)
    | MatchApply (a, b, z, k, cmd) ->
        MatchApply (a, b, z, k, rename_cmd (x, y) cmd)
    | MatchReturn (a, z, cmd) when Ident.equal z x ->
        MatchReturn (a, z, cmd)  (* Shadowing *)
    | MatchReturn (a, z, cmd) ->
        MatchReturn (a, z, rename_cmd (x, y) cmd)
    | MatchEval (b, z, cmd) when Ident.equal z x ->
        MatchEval (b, z, cmd)  (* Shadowing *)
    | MatchEval (b, z, cmd) ->
        MatchEval (b, z, rename_cmd (x, y) cmd)
    | ComatchApply (a, b, z, k, cmd) when Ident.equal z x || Ident.equal k x ->
        ComatchApply (a, b, z, k, cmd)  (* Shadowing *)
    | ComatchApply (a, b, z, k, cmd) ->
        ComatchApply (a, b, z, k, rename_cmd (x, y) cmd)
    | ComatchReturn (a, z, cmd) when Ident.equal z x ->
        ComatchReturn (a, z, cmd)  (* Shadowing *)
    | ComatchReturn (a, z, cmd) ->
        ComatchReturn (a, z, rename_cmd (x, y) cmd)
    | ComatchEval (b, z, cmd) when Ident.equal z x ->
        ComatchEval (b, z, cmd)  (* Shadowing *)
    | ComatchEval (b, z, cmd) ->
        ComatchEval (b, z, rename_cmd (x, y) cmd)
    | MuLhsPos (a, z, cmd) when Ident.equal z x ->
        MuLhsPos (a, z, cmd)  (* Shadowing *)
    | MuLhsPos (a, z, cmd) ->
        MuLhsPos (a, z, rename_cmd (x, y) cmd)
    | MuRhsPos (a, z, cmd) when Ident.equal z x ->
        MuRhsPos (a, z, cmd)  (* Shadowing *)
    | MuRhsPos (a, z, cmd) ->
        MuRhsPos (a, z, rename_cmd (x, y) cmd)
    | MuLhsNeg (b, z, cmd) when Ident.equal z x ->
        MuLhsNeg (b, z, cmd)  (* Shadowing *)
    | MuLhsNeg (b, z, cmd) ->
        MuLhsNeg (b, z, rename_cmd (x, y) cmd)
    | MuRhsNeg (b, z, cmd) when Ident.equal z x ->
        MuRhsNeg (b, z, cmd)  (* Shadowing *)
    | MuRhsNeg (b, z, cmd) ->
        MuRhsNeg (b, z, rename_cmd (x, y) cmd)
  
  and rename_cmd (x, y) =
    function
      CutPos (a, t1, t2) ->
        CutPos (a, rename (x, y) t1, rename (x, y) t2)
    | CutNeg (a, t1, t2) ->
        CutNeg (a, rename (x, y) t1, rename (x, y) t2)
    | Add (t1, t2, t3) ->
        Add (rename (x, y) t1, rename (x, y) t2, rename (x, y) t3)
    | Ifz (t, cmd1, cmd2) ->
        Ifz (rename (x, y) t, rename_cmd (x, y) cmd1, rename_cmd (x, y) cmd2)
    | End -> End

  let rec pp_command =
    function
      CutPos (_, t1, t2) -> "⟨" ^ pp_term t1 ^ " ∥+∥ " ^ pp_term t2 ^ "⟩"
    | CutNeg (_, t1, t2) ->"⟨" ^ pp_term t1 ^ " ∥-∥ " ^ pp_term t2 ^ "⟩"
    | Add (t1, t2, t3) -> "add(" ^ pp_term t1 ^ ", " ^ pp_term t2 ^ ", " ^ pp_term t3 ^ ")"
    | Ifz (t, cmd1, cmd2) -> "ifz(" ^ pp_term t ^ ") then " ^ pp_command cmd1 ^ " else " ^ pp_command cmd2
    | End -> "end"
  
  and pp_term =
    function
      Variable x -> Ident.name x
    | Lit n -> string_of_int n
    | CtorApply (a, b, arg, cont) ->
        "ctor_apply[" ^ pp_pos a ^ ", " ^ pp_neg b ^ "]("
          ^ pp_term arg ^ ", " ^ pp_term cont ^ ")"
    | CtorReturn (a, arg) ->
        "ctor_return[" ^ pp_pos a ^ "](" ^ pp_term arg ^ ")"
    | CtorThunk (b, arg) ->
        "ctor_thunk[" ^ pp_neg b ^ "](" ^ pp_term arg ^ ")"
    | DtorApply (a, b, arg, cont) ->
        "dtor_apply[" ^ pp_pos a ^ ", " ^ pp_neg b ^ "]("
          ^ pp_term arg ^ ", " ^ pp_term cont ^ ")"
    | DtorReturn (a, arg) ->
        "dtor_return[" ^ pp_pos a ^ "](" ^ pp_term arg ^ ")"
    | DtorThunk (b, arg) ->
        "dtor_thunk[" ^ pp_neg b ^ "](" ^ pp_term arg ^ ")"
    | MatchApply (a, b, x, k, cmd) ->
        "case { ctor_apply[" ^ pp_pos a ^ ", " ^ pp_neg b ^ "]("
          ^ Ident.name x ^ ", " ^ Ident.name k ^ ") ⇒ " ^ pp_command cmd ^ "}"
    | MatchReturn (a, x, cmd) ->
        "case { ctor_return[" ^ pp_pos a ^ "]("
          ^ Ident.name x ^ ") ⇒ " ^ pp_command cmd ^ "}"
    | MatchEval (b, x, cmd) ->
        "case { ctor_eval[" ^ pp_neg b ^ "]("
          ^ Ident.name x ^ ") ⇒ " ^ pp_command cmd ^ "}"
    | ComatchApply (a, b, x, k, cmd) ->
        "cocase { dtor_apply[" ^ pp_pos a ^ ", " ^ pp_neg b ^ "]("
          ^ Ident.name x ^ ", " ^ Ident.name k ^ ") ⇒ " ^ pp_command cmd ^ "}"
    | ComatchReturn (a, x, cmd) ->
        "cocase { dtor_return[" ^ pp_pos a ^ "]("
          ^ Ident.name x ^ ") ⇒ " ^ pp_command cmd ^ "}"
    | ComatchEval (b, x, cmd) ->
        "cocase { dtor_eval[" ^ pp_neg b ^ "]("
          ^ Ident.name x ^ ") ⇒ " ^ pp_command cmd ^ "}"
    | MuLhsPos (_, k, cmd) -> "μ+L " ^ Ident.name k ^ ". " ^ pp_command cmd
    | MuRhsPos (_, k, cmd) -> "μ+R " ^ Ident.name k ^ ". " ^ pp_command cmd
    | MuLhsNeg (_, k, cmd) -> "μ-L " ^ Ident.name k ^ ". " ^ pp_command cmd
    | MuRhsNeg (_, k, cmd) -> "μ-R " ^ Ident.name k ^ ". " ^ pp_command cmd
  
  and pp_pos =
    function
      Int -> "Int"
    | Data (Apply (a, b)) -> "Fun_+(" ^ pp_pos a ^ ", " ^ pp_neg b ^ ")"
    | Data (Return a) -> "Lower_+(" ^ pp_pos a ^ ")"
    | Data (Thunk b) -> "Raise_+(" ^ pp_neg b ^ ")"
  
  and pp_neg =
    function
      Code (Apply (a, b)) -> "Fun_-(" ^ pp_pos a ^ ", " ^ pp_neg b ^ ")"
    | Code (Return a) -> "Lower_-(" ^ pp_pos a ^ ")"
    | Code (Thunk b) -> "Raise_-(" ^ pp_neg b ^ ")"

  let infer_kind =
    function
      Pos _ -> Positive
    | Neg _ -> Negative

  let infer_parity =
    function
      Lhs (Pos _) | Rhs (Neg _) -> Even
    | _ -> Odd
  
  let rec infer_command_typ (ctx: chiral_typ Ident.tbl) =
    function
      CutPos (ret_ty, t1, t2) ->
        let t1_ty = infer_typ ctx t1 in
        let t2_ty = infer_typ ctx t2 in
        (match t1_ty, t2_ty with
          Lhs ty1, Rhs ty2 when ty1 = Pos ret_ty && ty2 = Pos ret_ty ->
            Some (Pos ret_ty)
        | _ -> failwith "Type error in CutPos")
    | CutNeg (ret_ty, t1, t2) ->
        let t1_ty = infer_typ ctx t1 in
        let t2_ty = infer_typ ctx t2 in
        (match t1_ty, t2_ty with
          Lhs ty1, Rhs ty2 when ty1 = Neg ret_ty && ty2 = Neg ret_ty ->
            Some (Neg ret_ty)
        | _ -> failwith "Type error in CutNeg")
    | Add (t1, t2, t3) ->
        let t1_ty = infer_typ ctx t1 in
        let t2_ty = infer_typ ctx t2 in
        let t3_ty = infer_typ ctx t3 in
        if t1_ty = Lhs (Pos Int) && t2_ty = Lhs (Pos Int) && t3_ty = Rhs (Pos Int)
        then Some (Pos Int)
        else failwith "Type error in Add"
    | Ifz (t, cmd1, cmd2) ->
        (match infer_typ ctx t with
          Lhs (Pos Int) ->
            let cmd1_ty = infer_command_typ ctx cmd1 in
            let cmd2_ty = infer_command_typ ctx cmd2 in
            if cmd1_ty = cmd2_ty then cmd1_ty
            else failwith "Type error: branches of Ifz have different types"
        | _ -> failwith "Type error: condition of Ifz must be Int")
    | End -> None

  and infer_typ (ctx: chiral_typ Ident.tbl) =
    function
      Variable x -> Ident.find x ctx
    | Lit _ -> Lhs (Pos Int)
    | CtorApply (a, b, arg, cont) ->
        let arg_ty = infer_typ ctx arg in
        let cont_ty = infer_typ ctx cont in
        (match arg_ty, cont_ty with
          Lhs a', Rhs b' when a' = Pos a && b' = Neg b ->
            Lhs (Pos (Data (Apply (a, b))))
        | _ -> failwith "Type error in CtorApply")
    | CtorReturn (a, arg) ->
        let arg_ty = infer_typ ctx arg in
        (match arg_ty with
          Lhs a' when a' = Pos a ->
            Lhs (Pos (Data (Return a)))
        | _ -> failwith "Type error in CtorReturn")
    | CtorThunk (b, arg) ->
        let arg_ty = infer_typ ctx arg in
        (match arg_ty with
          Rhs b' when b' = Neg b ->
            Lhs (Pos (Data (Thunk b)))
        | _ -> failwith "Type error in CtorThunk")
    | DtorApply (a, b, arg, cont) ->
        let arg_ty = infer_typ ctx arg in
        let cont_ty = infer_typ ctx cont in
        (match arg_ty, cont_ty with
          Lhs a', Rhs b' when a' = Pos a && b' = Neg b ->
            Rhs (Neg (Code (Apply (a, b))))
        | _ -> failwith "Type error in DtorApply")
    | DtorReturn (a, arg) ->
        let arg_ty = infer_typ ctx arg in
        (match arg_ty with
          Lhs a' when a' = Pos a ->
            Rhs (Neg (Code (Return a)))
        | _ -> failwith "Type error in DtorReturn")
    | DtorThunk (b, arg) ->
        let arg_ty = infer_typ ctx arg in
        (match arg_ty with
          Rhs b' when b' = Neg b ->
            Rhs (Neg (Code (Thunk b)))
        | _ -> failwith "Type error in DtorThunk")
    | MatchApply (a, b, x, k, cmd) ->
        let ctx' =
          Ident.add x (Lhs (Pos a)) (Ident.add k (Rhs (Neg b)) ctx)
        in
        infer_command_typ ctx' cmd |> ignore; (* Just check *)
        Rhs (Pos (Data (Apply (a, b))))
    | MatchReturn (a, x, cmd) ->
        let ctx' = Ident.add x (Lhs (Pos a)) ctx in
        infer_command_typ ctx' cmd |> ignore; (* Just check *)
        Rhs (Pos (Data (Return a)))
    | MatchEval (b, x, cmd) ->
        let ctx' = Ident.add x (Rhs (Neg b)) ctx in
        infer_command_typ ctx' cmd |> ignore; (* Just check *)
        Rhs (Pos (Data (Thunk b)))
    | ComatchApply (a, b, x, k, cmd) ->
        let ctx' =
          Ident.add x (Lhs (Pos a)) (Ident.add k (Rhs (Neg b)) ctx)
        in
        infer_command_typ ctx' cmd |> ignore; (* Just check *)
        Lhs (Neg (Code (Apply (a, b))))
    | ComatchReturn (a, x, cmd) ->
        let ctx' = Ident.add x (Lhs (Pos a)) ctx in
        infer_command_typ ctx' cmd |> ignore; (* Just check *)
        Lhs (Neg (Code (Return a)))
    | ComatchEval (b, x, cmd) ->
        let ctx' = Ident.add x (Rhs (Neg b)) ctx in
        infer_command_typ ctx' cmd |> ignore; (* Just check *)
        Lhs (Neg (Code (Thunk b)))
    | MuLhsPos (ty, x, cmd) ->
        let ctx' = Ident.add x (Rhs (Pos ty)) ctx in
        infer_command_typ ctx' cmd |> ignore; (* Just check *)
        Lhs (Pos ty)
    | MuRhsPos (ty, k, cmd) ->
        let ctx' = Ident.add k (Lhs (Pos ty)) ctx in
        infer_command_typ ctx' cmd |> ignore; (* Just check *)
        Rhs (Pos ty)
    | MuLhsNeg (ty, x, cmd) ->
        let ctx' = Ident.add x (Rhs (Neg ty)) ctx in
        infer_command_typ ctx' cmd |> ignore; (* Just check *)
        Lhs (Neg ty)
    | MuRhsNeg (ty, k, cmd) ->
        let ctx' = Ident.add k (Lhs (Neg ty)) ctx in
        infer_command_typ ctx' cmd |> ignore; (* Just check *)
        Rhs (Neg ty)
  
  let infer_parity_term (t: term) =
    infer_parity (infer_typ Ident.emptytbl t)
    
end

module Encode = struct

  open Seq
  
  let lower ty = Code (Return ty)
  let raise ty = Data (Thunk ty)

  let rec map_typ =
    function
      Pcf.Int -> Pos Int
    | Pcf.Arrow (a, b) ->
        match map_typ a, map_typ b with
          Pos a, Pos b -> Neg (Code (Apply (a, lower b)))
        | Pos a, Neg b -> Neg (Code (Apply (a, b)))
        | Neg a, Pos b -> Neg (Code (Apply (raise a, lower b)))
        | Neg a, Neg b -> Neg (Code (Apply (raise a, b)))
    
  let rec map_term (ctx: Pcf.typ Ident.tbl) =
    function
      Pcf.Var x -> Variable x
    | Pcf.Lam (x, a, body) ->
        (* λx:A. body  where body: B *)
        let ctx' = Ident.add x a ctx in
        let b = Pcf.infer_typ ctx' body in
        let body' = map_term ctx' body in
        let k = Ident.fresh () in
        (match map_typ a, map_typ b with
          Pos a', Pos b' ->
            (* case { apply[a', ↓b'](x, k) => ⟨return[b'](body') | k⟩ } *)
            MatchApply (a', lower b', x, k,
              CutNeg (lower b', CtorReturn (b', body'), Variable k))
        | Pos a', Neg b' ->
            (* case { apply[a', b'](x, k) => ⟨body' | k⟩ } *)
            MatchApply (a', b', x, k,
              CutNeg (b', body', Variable k))
        | Neg a', Pos b' ->
            (* TODO: This is probably wrong! *)
            (* case { apply[↑a', ↓b'](x, k) => ⟨μ-L α.⟨return[b'](body'') | k⟩ | thunk[a'](x)⟩ } *)
            let alpha = Ident.fresh () in
            let body'' = rename (x, alpha) body' in
            MatchApply (raise a', lower b', x, k,
              CutNeg (lower b',
                MuLhsNeg (a', alpha, CutNeg (lower b', CtorReturn (b', body''), Variable k)),
                CtorThunk (a', Variable x)))
        | Neg a', Neg b' ->
            (* case { apply[↑a', b'](x, k) => ⟨μ-L α.⟨body'' | k⟩ | thunk[a'](x)⟩ } *)
            let alpha = Ident.fresh () in
            let body'' = rename (x, alpha) body' in
            MatchApply (raise a', b', x, k,
              CutNeg (b',
                MuLhsNeg (a', alpha, CutNeg (b', body'', Variable k)),
                CtorThunk (a', Variable x))))
    | Pcf.App (t1, t2) ->
        failwith "TODO"
    | Pcf.Lit n -> Lit n
    | Pcf.Add (t1, t2) ->
        (* t1 + t2  where t1, t2 : Int
          Translates to: μk. add([t1], [t2], k)
          Both operands are Rhs (positive Int), result is Lhs (positive Int) *)
        let t1' = map_term ctx t1 in
        let t2' = map_term ctx t2 in
        let k = Ident.fresh () in
        MuLhsPos (Int, k, Add (t1', t2', Variable k))
    | Pcf.Ifz (t1, t2, t3) ->
        (* ifz t1 then t2 else t3  where t1 : Int, t2 and t3 : B
          Translates to: μk. ifz([t1]) then ⟨[t2] | k⟩ else ⟨[t3] | k⟩
          The condition is Rhs Int, and we cut results with continuation k *)
        let b = Pcf.infer_typ ctx t2 in
        let t1' = map_term ctx t1 in
        let t2' = map_term ctx t2 in
        let t3' = map_term ctx t3 in
        let k = Ident.fresh () in
        (match map_typ b with
          Pos b' ->
            MuLhsPos (b', k,
              Ifz (t1', 
                CutPos (b', t2', Variable k),
                CutPos (b', t3', Variable k)))
        | Neg b' ->
            MuLhsNeg (b', k,
              Ifz (t1',
                CutNeg (b', t2', Variable k),
                CutNeg (b', t3', Variable k))))

end