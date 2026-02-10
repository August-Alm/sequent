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
    | Add (t1, t2) ->
      pp_term t1 ^ " + " ^ pp_term t2
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
       | Arrow (arg_ty, ret_ty) ->
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

  let rec infer_kind =
    function
      Pos _ -> Positive
    | Neg _ -> Negative

  type command =
      CutPos of pos_typ * term * term
    | CutNeg of neg_typ * term * term
    | End

  and term =
      Variable of var
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
    | End -> "end"

  and pp_term =
    function
      Variable x -> Ident.name x
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
    | End -> None

  and infer_typ (ctx: chiral_typ Ident.tbl) =
    function
      Variable x -> Ident.find x ctx
    | Eval (a, t) ->
        (match infer_typ ctx t with
          Rhs (Neg t_ty) when t_ty = a -> Lhs (Pos (Raise a))
        | _ -> failwith "Type error in Eval")
    | MatchRaise (ty, x, cmd) ->
        let ctx' = Ident.add x (Rhs (Neg ty)) ctx in
        infer_command_typ ctx' cmd |> ignore; (* just check *)
        Rhs (Pos (Raise ty))
    | Return (ty, t) ->
        (match infer_typ ctx t with
          Lhs (Pos t_ty) when t_ty = ty -> Rhs (Neg (Lower ty))
        | _ -> failwith "Type error in Return")
    | Apply (a, b, arg, k) ->
        let arg_ty = infer_typ ctx arg in
        let k_ty = infer_typ ctx k in
        (match arg_ty, k_ty with
        | Lhs a', Rhs b' when a' = Pos a && b' = Neg b -> Rhs (Neg (Fun (a, b)))
        | _ -> failwith "Type error in Apply")
    | NewLower (a, x, cmd) ->
        let ctx' = Ident.add x (Lhs (Pos a)) ctx in
        infer_command_typ ctx' cmd |> ignore; (* just check *)
        Rhs (Neg (Lower a))
    | NewFun (a, b, x, k, cmd) ->
        let ctx' =
          Ident.add x (Lhs (Pos a)) (Ident.add k (Rhs (Neg b)) ctx)
        in
        infer_command_typ ctx' cmd |> ignore; (* just check *)
        Rhs (Neg (Fun (a, b)))
    | MuLhsPos (ty, x, cmd) ->
        let ctx' = Ident.add x (Rhs (Pos ty)) ctx in
        (match infer_command_typ ctx' cmd with
          Some cmd_ty when cmd_ty = Pos ty -> Lhs (Pos ty)
        | _ -> failwith "Type error in MuLhsPos")
    | MuRhsPos (ty, k, cmd) ->
        let ctx' = Ident.add k (Lhs (Pos ty)) ctx in
        (match infer_command_typ ctx' cmd with
          Some cmd_ty when cmd_ty = Pos ty -> Rhs (Pos ty)
        | _ -> failwith "Type error in MuRhsPos")
    | MuLhsNeg (ty, x, cmd) ->
        let ctx' = Ident.add x (Rhs (Neg ty)) ctx in
        (match infer_command_typ ctx' cmd with
          Some cmd_ty when cmd_ty = Neg ty -> Lhs (Neg ty)
        | _ -> failwith "Type error in MuLhsNeg")
    | MuRhsNeg (ty, k, cmd) ->
        let ctx' = Ident.add k (Lhs (Neg ty)) ctx in
        (match infer_command_typ ctx' cmd with
          Some cmd_ty when cmd_ty = Neg ty -> Rhs (Neg ty)
        | _ -> failwith "Type error in MuRhsNeg")
end