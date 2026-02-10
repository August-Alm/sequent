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
    | Raise of neg_typ

  and neg_typ =
      Fun of pos_typ * neg_typ
    | Lower of pos_typ 
  
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
    | Eval of neg_typ * term (** Ctor of Raise(A) *)
    | MatchRaise of neg_typ * var * command (** Match of Raise(A) *)
    | Return of pos_typ * term (** Dtor of Lower(A) *)
    | Apply of pos_typ * neg_typ * term * term (** Dtor of Fun(A, B) *)
    | NewLower of pos_typ * var * command (** Cocase of Lower(A) *)
    | NewFun of pos_typ * neg_typ * var * var * command (** Cocase of Fun(A, B) *)
    | MuLhsPos of pos_typ * var * command
    | MuRhsPos of pos_typ * var * command
    | MuLhsNeg of neg_typ * var * command
    | MuRhsNeg of neg_typ * var * command

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
    | Eval (ty, t) -> "eval(" ^ pp_neg ty ^ ", " ^ pp_term t ^ ")"
    | MatchRaise (ty, x, cmd) ->
      "case { eval[" ^ pp_neg ty ^ "]("
        ^ Ident.name x ^ ") ⇒ " ^ pp_command cmd ^ " }"
    | Return (ty, t) -> "return[" ^ pp_pos ty ^ "](" ^ pp_term t ^ ")"
    | Apply (fun_ty, arg_ty, f, arg) ->
      "apply[" ^ pp_pos fun_ty ^ ", " ^ pp_neg arg_ty ^ "]("
        ^ pp_term f ^ ", " ^ pp_term arg ^ ")"
    | NewLower (arg_ty, x, cmd) ->
      "cocase { return[" ^ pp_pos arg_ty ^ "]("^
        Ident.name x ^") ⇒ " ^ pp_command cmd ^ " }"
    | NewFun (fun_ty, arg_ty, f, x, cmd) ->
      "cocase { apply[" ^ pp_pos fun_ty ^ ", " ^ pp_neg arg_ty ^ "](" ^
        Ident.name f ^ ", " ^ Ident.name x ^ ") ⇒ " ^ pp_command cmd ^ " }"
    | MuLhsPos (_, k, cmd) -> "μ+L " ^ Ident.name k ^ ". " ^ pp_command cmd
    | MuRhsPos (_, k, cmd) -> "μ+R " ^ Ident.name k ^ ". " ^ pp_command cmd
    | MuLhsNeg (_, k, cmd) -> "μ-L " ^ Ident.name k ^ ". " ^ pp_command cmd
    | MuRhsNeg (_, k, cmd) -> "μ-R " ^ Ident.name k ^ ". " ^ pp_command cmd
  
  and pp_pos =
    function
      Int -> "Int"
    | Raise ty -> "↑(" ^ pp_neg ty ^ ")"
  
  and pp_neg =
    function
      Fun (arg_ty, ret_ty) -> "Fun(" ^ pp_pos arg_ty ^ ", " ^ pp_neg ret_ty ^ ")"
    | Lower ty -> "↓(" ^ pp_pos ty ^ ")"

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
    | Eval (a, t) ->
        (match infer_typ ctx t with
          Lhs (Neg t_ty) when t_ty = a -> Lhs (Pos (Raise a))
        | _ -> failwith "Type error in Eval")
    | MatchRaise (ty, x, cmd) ->
        let ctx' = Ident.add x (Lhs (Neg ty)) ctx in
        infer_command_typ ctx' cmd |> ignore; (* Just check *)
        Rhs (Pos (Raise ty))
    | Return (ty, t) ->
        (match infer_typ ctx t with
          Lhs (Pos t_ty) when t_ty = ty -> Lhs (Neg (Lower ty))
        | _ -> failwith "Type error in Return")
    | Apply (a, b, arg, k) ->
        let arg_ty = infer_typ ctx arg in
        let k_ty = infer_typ ctx k in
        (match arg_ty, k_ty with
          Lhs a', Rhs b' when a' = Pos a && b' = Neg b -> Rhs (Neg (Fun (a, b)))
        | _ -> failwith "Type error in Apply")
    | NewLower (a, x, cmd) ->
        let ctx' = Ident.add x (Lhs (Pos a)) ctx in
        infer_command_typ ctx' cmd |> ignore; (* Just check *)
        Lhs (Neg (Lower a))
    | NewFun (a, b, x, k, cmd) ->
        let ctx' =
          Ident.add x (Lhs (Pos a)) (Ident.add k (Rhs (Neg b)) ctx)
        in
        infer_command_typ ctx' cmd |> ignore; (* Just check *)
        Lhs (Neg (Fun (a, b)))
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
  
  let rec map_typ =
    function
      Pcf.Int -> Pos Int
    | Pcf.Arrow (a, b) ->
        match map_typ a, map_typ b with
          Pos a, Pos b -> Neg (Fun (a, Lower b))
        | Pos a, Neg b -> Neg (Fun (a, b))
        | Neg a, Pos b -> Neg (Fun (Raise a, Lower b))
        | Neg a, Neg b -> Neg (Fun (Raise a, b))
    
  let rec map_term (ctx: Pcf.typ Ident.tbl) =
    function
      Pcf.Var x -> Variable x
    | Pcf.Lam (x, a, body) ->
        (* λx:A. body  where body: B
          Translates to: cocase { apply[A', B'](x, k) ⇒ ⟨[body] | k⟩ }
          The body is cut with the continuation k *)
        let ctx' = Ident.add x a ctx in
        let b = Pcf.infer_typ ctx' body in
        let body' = map_term ctx' body in
        let k = Ident.fresh () in
        (match map_typ a, map_typ b with
          Pos a', Pos b' ->
            (* A → B where both positive: Fun(A', ↓B')
              Body produces positive, so wrap in return and cut negatively *)
            NewFun (a', Lower b', x, k, 
              CutNeg (Lower b', Return (b', body'), Variable k))
        | Pos a', Neg b' ->
            (* A → B where A positive, B negative: Fun(A', B')
              Body is negative, cut negatively with k *)
            NewFun (a', b', x, k,
              CutNeg (b', body', Variable k))
        | Neg a', Pos b' ->
            (* A → B where A negative, B positive: Fun(↑A', ↓B')
              Parameter is negative wrapped in Raise, body positive wrapped in Lower *)
            let x' = Ident.fresh () in
            NewFun (Raise a', Lower b', x', k,
              CutPos (Raise a', Variable x', 
                MatchRaise (a', x,
                  CutNeg (Lower b', Return (b', body'), Variable k))))
        | Neg a', Neg b' ->
            (* A → B where A negative, B negative: Fun(↑A', B')
              Parameter is negative wrapped in Raise *)
            let x' = Ident.fresh () in
            NewFun (Raise a', b', x', k,
              CutPos (Raise a', Variable x',
                MatchRaise (a', x,
                  CutNeg (b', body', Variable k)))))
    | Pcf.App (t1, t2) ->
        (* t1 t2  where t1 : A → B, t2 : A
          Translates to: μk. ⟨[t1] | apply([t2], k)⟩
          We create a μ-abstraction to capture the result *)
        let t1_ty = Pcf.infer_typ ctx t1 in
        let t2_ty = Pcf.infer_typ ctx t2 in
        let (a, b) = match t1_ty with
          | Pcf.Arrow (a, b) -> (a, b)
          | _ -> failwith "Application of non-function"
        in
        let _ = t2_ty in (* t2_ty should equal a *)
        let t1' = map_term ctx t1 in
        let t2' = map_term ctx t2 in
        let k = Ident.fresh () in
        (match map_typ a, map_typ b with
          Pos a', Pos b' ->
            (* Result is positive, use MuLhsPos *)
            MuLhsPos (b', k,
              CutNeg (Fun (a', Lower b'), t1',
                Apply (a', Lower b', t2', Variable k)))
        | Pos a', Neg b' ->
            (* Result is negative, use MuLhsNeg *)
            MuLhsNeg (b', k,
              CutNeg (Fun (a', b'), t1',
                Apply (a', b', t2', Variable k)))
        | Neg a', Pos b' ->
            (* Arg is negative, result positive *)
            MuLhsPos (b', k,
              CutNeg (Fun (Raise a', Lower b'), t1',
                Apply (Raise a', Lower b', Eval (a', t2'), Variable k)))
        | Neg a', Neg b' ->
            (* Arg is negative, result negative *)
            MuLhsNeg (b', k,
              CutNeg (Fun (Raise a', b'), t1',
                Apply (Raise a', b', Eval (a', t2'), Variable k))))
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