(** 
   Translation of Idris2 dependent types to OCaml GADTs.
   
   Key insight: We use nested tuples for type-level lists:
   - [] becomes unit
   - [a; b; c] becomes (a, (b, (c, unit)))
   
   This version maximizes the use of typed GADTs, using existential
   wrappers and packed modules for higher-rank polymorphism.
*)

(* ========================================================================= *)
(* Type-Level Lists and Append Witnesses                                     *)
(* ========================================================================= *)

(** Type-level list append witness: (xs, ys, zs) append means xs ++ ys = zs *)
type (_, _, _) append =
  | AppNil : (unit, 'ys, 'ys) append
  | AppCons : ('xs, 'ys, 'zs) append -> ('x * 'xs, 'ys, 'x * 'zs) append

(** Existential wrapper for append with fixed base context *)
type 'ctx ex_append_with_base =
  ExAppBase : ('ps, 'ctx, 'ps_ctx) append -> 'ctx ex_append_with_base

(** Generate an append witness from a list length with fixed base *)
let rec make_append_with_base : type ctx. 'a list -> ctx ex_append_with_base = function
  | [] -> ExAppBase AppNil
  | _ :: rest ->
    let ExAppBase app = make_append_with_base rest in
    ExAppBase (AppCons app)

(** Existential wrapper for append with target context *)
type ('ps, 'ys) ex_append_to =
  ExAppTo : ('ps, 'ys, 'ps_ys) append -> ('ps, 'ys) ex_append_to

(** Rebind an append witness to a different base context *)
let rec rebind_append : type ps xs ys ps_xs.
    (ps, xs, ps_xs) append -> (ps, ys) ex_append_to =
  fun app ->
    match app with
    | AppNil -> ExAppTo AppNil
    | AppCons rest ->
      let ExAppTo rest' = rebind_append rest in
      ExAppTo (AppCons rest')

(* ========================================================================= *)
(* Typed Names (De Bruijn Indices)                                           *)
(* ========================================================================= *)

(** 
   [('ctx, 'a) name] witnesses that type ['a] is in context ['ctx].
   This is the typed De Bruijn index.
*)
type ('ctx, 'a) name =
  | Z : ('a * 'rest, 'a) name
  | S : ('rest, 'a) name -> ('b * 'rest, 'a) name

(* ========================================================================= *)
(* Typed Substitutions                                                       *)
(* ========================================================================= *)

(**
   [('xs, 'ys) sub] represents a typed renaming from context ['xs] to ['ys].
*)
type ('xs, 'ys) sub =
  | Keep : ('xs, 'xs) sub
  | Comp : ('xs, 'ys) sub * ('ys, 'zs) sub -> ('xs, 'zs) sub
  | Lift : ('xs, 'ys) sub -> ('z * 'xs, 'z * 'ys) sub
  | Weak : ('xs, 'x * 'xs) sub
  | Copy : ('x * ('x * 'xs), 'x * 'xs) sub
  | Swap : ('x * ('y * 'xs), 'y * ('x * 'xs)) sub

(** Apply typed substitution to typed name *)
let rec rename : type xs ys a. (xs, ys) sub -> (xs, a) name -> (ys, a) name =
  fun h n ->
    match h, n with
    | Keep, n -> n
    | Comp (h1, h2), n -> rename h2 (rename h1 n)
    | Weak, n -> S n
    | Lift _, Z -> Z
    | Lift h', S y -> S (rename h' y)
    | Copy, Z -> Z
    | Copy, S x -> x
    | Swap, Z -> S Z
    | Swap, S Z -> Z
    | Swap, S (S x) -> S (S x)

(** Weaken by multiple variables (given append witness) *)
let rec weak_many : type xs ys zs. (ys, xs, zs) append -> (xs, zs) sub =
  function
  | AppNil -> Keep
  | AppCons rest -> Comp (weak_many rest, Weak)

(** Substitution for a single variable *)
let rec substitute : type xs t. (xs, t) name -> (t * xs, xs) sub =
  function
  | Z -> Copy
  | S x -> Comp (Swap, Lift (substitute x))

(* ========================================================================= *)
(* Typed Environments                                                        *)
(* ========================================================================= *)

(**
   [('f, 'ctx) env] is a typed environment where each element is of type 'f.
   The context 'ctx tracks the structure.
*)
type ('f, 'ctx) env =
  | Nil : ('f, unit) env
  | Cons : 'f * ('f, 'rest) env -> ('f, 'a * 'rest) env

(** Transform all elements of an environment *)
let rec transform : type ctx. ('a -> 'b) -> ('a, ctx) env -> ('b, ctx) env =
  fun f env ->
    match env with
    | Nil -> Nil
    | Cons (v, rest) -> Cons (f v, transform f rest)

(* ========================================================================= *)
(* Types (Object Language)                                                   *)
(* ========================================================================= *)

type signature = chiral_tpe list list

and tpe =
  | Pos of signature
  | Neg of signature

and chiral_tpe =
  | Lhs of tpe
  | Rhs of tpe

(* ========================================================================= *)
(* Typed Source Language                                                     *)
(* ========================================================================= *)

module Source = struct
  
  (** Typed command indexed by context *)
  type 'ctx command =
    | CutPos : signature * 'ctx term * 'ctx term -> 'ctx command
    | CutNeg : signature * 'ctx term * 'ctx term -> 'ctx command
    | End : 'ctx command

  (** Typed term indexed by context *)
  and 'ctx term =
    | Variable : ('ctx, 'a) name -> 'ctx term
    | Constructor : signature * int * 'ctx term_list -> 'ctx term
    | Match : signature * 'ctx branch_list -> 'ctx term
    | Comatch : signature * 'ctx branch_list -> 'ctx term
    | Destructor : signature * int * 'ctx term_list -> 'ctx term
    | MuLhsPos : signature * ('a * 'ctx) command -> 'ctx term
    | MuRhsPos : signature * ('a * 'ctx) command -> 'ctx term
    | MuLhsNeg : signature * ('a * 'ctx) command -> 'ctx term
    | MuRhsNeg : signature * ('a * 'ctx) command -> 'ctx term

  (** List of terms (typed) *)
  and 'ctx term_list =
    | TLNil : 'ctx term_list
    | TLCons : 'ctx term * 'ctx term_list -> 'ctx term_list

  (** List of branches *)
  and 'ctx branch_list =
    | BLNil : 'ctx branch_list
    | BLCons : ('ctx, 'ps) branch * 'ctx branch_list -> 'ctx branch_list

  (** Branch with parameter context *)
  and ('ctx, 'ps) branch =
    | Clause : ('ps, 'ctx, 'extended) append * 'extended command -> ('ctx, 'ps) branch

  (** Convert term list to OCaml list *)
  let rec term_list_to_list : type ctx. ctx term_list -> ctx term list = function
    | TLNil -> []
    | TLCons (t, rest) -> t :: term_list_to_list rest
end

(* ========================================================================= *)
(* Typed Target Language                                                     *)
(* ========================================================================= *)

module Target = struct
  
  (** Existential name wrapper - hides the type being named *)
  type 'ctx ex_name = ExName : ('ctx, 'a) name -> 'ctx ex_name
  
  (** Typed command indexed by context *)
  type 'ctx command =
    | LetConstructor : signature * int * ('ctx ex_name, 'ps) env * ('t * 'ctx) command 
      -> 'ctx command  (** [⟨Cₙ(Γ) | μ̃x.s⟩]  Positive *)
    | CutMatch : signature * ('ctx, 'a) name * 'ctx branch_list
      -> 'ctx command  (** [⟨x | case \{C₁(Γ₁) ⇒ s₁; …\}⟩] Positive *)
    | LetMatch : signature * 'ctx branch_list * ('t * 'ctx) command
      -> 'ctx command  (** [⟨μα.s | case \{C₁(Γ₁) ⇒ s₁; …\}⟩] Positive *)
    | CutConstructor : signature * int * ('ctx ex_name, 'ps) env * ('ctx, 'b) name 
      -> 'ctx command  (** [⟨Cₙ(y₁, …, yₖ) | α⟩] Positive *)
    | LetDestructor : signature * int * ('ctx ex_name, 'ps) env * ('t * 'ctx) command 
      -> 'ctx command  (** [⟨μα.s | Dₙ(Γ)⟩] Negative *)
    | CutComatch : signature * 'ctx branch_list * ('ctx, 'a) name
      -> 'ctx command  (** [⟨cocase \{D₁(Γ₁) ⇒ s₁; …\} | α⟩] Negative *)
    | LetComatch : signature * 'ctx branch_list * ('t * 'ctx) command
      -> 'ctx command  (** [⟨cocase \{D₁(Γ₁) ⇒ s₁; …\} | μ̃x.s⟩]  Negative *)
    | CutDestructor : signature * ('ctx, 'a) name * int * ('ctx ex_name, 'ps) env 
      -> 'ctx command  (** [⟨x | Dₙ(y₁, …, yₖ)⟩] Negative *)
    | End : 'ctx command  (** Terminal / halt *)

  (** List of branches *)
  and 'ctx branch_list =
    | BLNil : 'ctx branch_list
    | BLCons : ('ctx, 'ps) branch * 'ctx branch_list -> 'ctx branch_list

  (** Branch with parameter context *)
  and ('ctx, 'ps) branch =
    | Clause : ('ps, 'ctx, 'extended) append * 'extended command -> ('ctx, 'ps) branch

  (** Rename an existentially wrapped name *)
  let rename_ex : type xs ys. (xs, ys) sub -> xs ex_name -> ys ex_name =
    fun h (ExName n) -> ExName (rename h n)

  (** Lift substitution under append witnesses *)
  let rec lift_sub_with_append : type ps xs ys ps_xs ps_ys.
      (ps, xs, ps_xs) append ->
      (ps, ys, ps_ys) append ->
      (xs, ys) sub ->
      (ps_xs, ps_ys) sub =
    fun app1 app2 h ->
      match app1, app2 with
      | AppNil, AppNil -> h
      | AppCons rest1, AppCons rest2 -> Lift (lift_sub_with_append rest1 rest2 h)

  (** Rename a command under a substitution *)
  let rec rename_command : type xs ys. (xs, ys) sub -> xs command -> ys command =
    fun h cmd ->
      match cmd with
      | LetConstructor (sig_, n, vs, s) ->
        LetConstructor (sig_, n, transform (rename_ex h) vs, rename_command (Lift h) s)
      | LetMatch (sig_, m, s) ->
        LetMatch (sig_, rename_branches h m, rename_command (Lift h) s)
      | LetComatch (sig_, m, s) ->
        LetComatch (sig_, rename_branches h m, rename_command (Lift h) s)
      | LetDestructor (sig_, n, vs, s) ->
        LetDestructor (sig_, n, transform (rename_ex h) vs, rename_command (Lift h) s)
      | CutConstructor (sig_, n, vs, a) ->
        CutConstructor (sig_, n, transform (rename_ex h) vs, rename h a)
      | CutMatch (sig_, a, m) ->
        CutMatch (sig_, rename h a, rename_branches h m)
      | CutComatch (sig_, m, a) ->
        CutComatch (sig_, rename_branches h m, rename h a)
      | CutDestructor (sig_, a, n, vs) ->
        CutDestructor (sig_, rename h a, n, transform (rename_ex h) vs)
      | End -> End

  and rename_branch : type xs ys ps.
      (xs, ys) sub -> (xs, ps) branch -> (ys, ps) branch =
    fun h (Clause (app, s)) ->
      let ExAppTo app' = rebind_append app in
      Clause (app', rename_command (lift_sub_with_append app app' h) s)

  and rename_branches : type xs ys.
      (xs, ys) sub -> xs branch_list -> ys branch_list =
    fun h branches ->
      match branches with
      | BLNil -> BLNil
      | BLCons (b, rest) -> BLCons (rename_branch h b, rename_branches h rest)
end

(* ========================================================================= *)
(* Fresh Names Generation                                                    *)
(* ========================================================================= *)

(** Generate fresh names for parameters (existentially wrapped) *)
let rec fresh_names : type ps ctx ps_ctx.
  (ps, ctx, ps_ctx) append -> (ps_ctx Target.ex_name, ps) env =
  fun app ->
    match app with
    | AppNil -> Nil
    | AppCons rest ->
      Cons (Target.ExName Z, transform (Target.rename_ex Weak) (fresh_names rest))

(* ========================================================================= *)
(* Module Types for Higher-Rank Polymorphism                                 *)
(* ========================================================================= *)

(** Module type for branch body builder (polymorphic in ps) *)
module type BRANCH_BODY_BUILDER = sig
  type ctx
  val build : 'ps 'ps_ctx.
    ('ps, ctx, 'ps_ctx) append -> int -> 'ps_ctx Target.command
end

(** Module type for bind_term continuation (polymorphic in zs) *)
module type BIND_CONT = sig
  type base_ctx
  val cont : 'zs 'a. (base_ctx, 'zs) sub -> ('zs, 'a) name -> 'zs Target.command
end

(** Module type for bind_terms continuation - uses existential for result env *)
module type BIND_TERMS_CONT = sig
  type base_ctx
  val cont : 'zs 'ps.
    (base_ctx, 'zs) sub -> ('zs Target.ex_name, 'ps) env -> 'zs Target.command
end

(* ========================================================================= *)
(* Transformation                                                            *)
(* ========================================================================= *)

module Transform = struct
  open Source

  (** Build a substitution from (ps ++ ctx) to ctx that replaces each ps variable
      with the corresponding name from the environment.
      Given: env of ctx-names for each ps position
      Returns: sub from (ps ++ ctx) to ctx
      Uses Obj.magic because the existential types in ExName don't unify
      with the append witness structure, but are semantically correct. *)
  let rec substitute_many : type ps ctx ps_ctx.
      (ps, ctx, ps_ctx) append -> (ctx Target.ex_name, ps) env -> (ps_ctx, ctx) sub =
    fun app vs ->
      match app, vs with
      | AppNil, Nil -> Keep
      | AppCons rest_app, Cons (Target.ExName v, rest_vs) ->
          (* ps = p * ps', ps_ctx = p * ps'_ctx where ps'_ctx = ps' ++ ctx
             We have: substitute v : (p * ctx, ctx) sub
                      substitute_many rest_app rest_vs : (ps'_ctx, ctx) sub
             We need: (p * ps'_ctx, ctx) sub
             So: first apply (Lift (substitute_many ...)) : (p * ps'_ctx, p * ctx)
                 then apply (substitute v) : (p * ctx, ctx) *)
          Comp (Lift (substitute_many rest_app rest_vs), Obj.magic (substitute v))

  (** Lookup branch by index and inline with substitution.
      Takes an environment of argument variables and substitutes them for
      the branch parameters. Uses Obj.magic to handle existential type 
      mismatches between the branch's append witness and the provided one. *)
  let rec lookup_branch_body : type ctx ps.
    ctx Target.branch_list -> int -> (ctx Target.ex_name, ps) env -> ctx Target.command =
    fun branches n vs ->
      match branches, n with
      | Target.BLCons (Target.Clause (app, body), _), 0 -> 
          (* body : ps_ctx Target.command where ps_ctx = ps ++ ctx
             vs : (ctx Target.ex_name, ps) env
             We need to substitute ps variables with vs to get ctx Target.command *)
          let sub = substitute_many app (Obj.magic vs) in
          Obj.magic (Target.rename_command sub body)
      | Target.BLCons (_, rest), n -> lookup_branch_body rest (n - 1) vs
      | Target.BLNil, _ -> Target.End

  (** Build branch list from signature using a polymorphic builder *)
  let build_branches_from_sig (type ctx) (sig_ : signature) 
      (module B : BRANCH_BODY_BUILDER with type ctx = ctx) :
      ctx Target.branch_list =
    let rec go idx = function
      | [] -> Target.BLNil
      | ps :: rest ->
        let ExAppBase app = make_append_with_base ps in
        let body = B.build app idx in
        Target.BLCons (Target.Clause (app, body), go (idx + 1) rest)
    in
    go 0 sig_

  (** Transform source branches to target branches *)
  let rec transform_source_branches : type xs ys.
    xs Source.branch_list -> (xs, ys) sub -> ys Target.branch_list =
    fun branches h ->
      match branches with
      | BLNil -> Target.BLNil
      | BLCons (Clause (app, body), rest) ->
        let ExAppTo app' = rebind_append app in
        let lifted_h = Target.lift_sub_with_append app app' h in
        let transformed_body = transform_command body lifted_h in
        Target.BLCons (Target.Clause (app', transformed_body), 
                       transform_source_branches rest h)

  (** Bind a single term using packed module for continuation *)
  and bind_term : type xs ys.
    xs Source.term -> (xs, ys) sub -> (module BIND_CONT with type base_ctx = ys) ->
    ys Target.command =
    fun term h (module K) ->
      match term with
      | Variable x ->
        K.cont Keep (rename h x)

      | Constructor (sig_, n, args) ->
        bind_terms (term_list_to_list args) h
          (module struct
            type base_ctx = ys
            let cont : type zs ps.
                (base_ctx, zs) sub -> (zs Target.ex_name, ps) env -> zs Target.command =
              fun i vs -> Target.LetConstructor (sig_, n, vs, K.cont (Comp (i, Weak)) Z)
          end)

      | Match (sig_, bs) ->
        Target.LetMatch (sig_, transform_source_branches bs h, K.cont Weak Z)

      | Comatch (sig_, bs) ->
        Target.LetComatch (sig_, transform_source_branches bs h, K.cont Weak Z)

      | Destructor (sig_, n, args) ->
        bind_terms (term_list_to_list args) h
          (module struct
            type base_ctx = ys
            let cont : type zs ps.
                (base_ctx, zs) sub -> (zs Target.ex_name, ps) env -> zs Target.command =
              fun i vs -> Target.LetDestructor (sig_, n, vs, K.cont (Comp (i, Weak)) Z)
          end)

      | MuLhsPos (sig_, s) ->
        Target.LetMatch (sig_,
          build_branches_from_sig sig_
            (module struct
              type ctx = ys
              let build : type ps ps_ctx.
                  (ps, ctx, ps_ctx) append -> int -> ps_ctx Target.command =
                fun ps_app n ->
                  let fresh = fresh_names ps_app in
                  Target.LetConstructor (sig_, n, fresh,
                    K.cont (Comp (weak_many ps_app, Weak)) Z)
            end),
          transform_command s (Lift h))

      | MuRhsPos (sig_, s) ->
        Target.LetMatch (sig_,
          build_branches_from_sig sig_
            (module struct
              type ctx = ys
              let build : type ps ps_ctx.
                  (ps, ctx, ps_ctx) append -> int -> ps_ctx Target.command =
                fun ps_app n ->
                  let fresh = fresh_names ps_app in
                  Target.LetConstructor (sig_, n, fresh,
                    transform_command s (Lift (Comp (h, weak_many ps_app))))
            end),
          K.cont Weak Z)

      | MuLhsNeg (sig_, s) ->
        Target.LetComatch (sig_,
          build_branches_from_sig sig_
            (module struct
              type ctx = ys
              let build : type ps ps_ctx.
                  (ps, ctx, ps_ctx) append -> int -> ps_ctx Target.command =
                fun ps_app n ->
                  let fresh = fresh_names ps_app in
                  Target.LetDestructor (sig_, n, fresh,
                    transform_command s (Lift (Comp (h, weak_many ps_app))))
            end),
          K.cont Weak Z)

      | MuRhsNeg (sig_, s) ->
        Target.LetComatch (sig_,
          build_branches_from_sig sig_
            (module struct
              type ctx = ys
              let build : type ps ps_ctx.
                  (ps, ctx, ps_ctx) append -> int -> ps_ctx Target.command =
                fun ps_app n ->
                  let fresh = fresh_names ps_app in
                  Target.LetDestructor (sig_, n, fresh,
                    K.cont (Comp (weak_many ps_app, Weak)) Z)
            end),
          transform_command s (Lift h))

  (** Bind multiple terms *)
  and bind_terms : type xs ys.
    xs Source.term list -> (xs, ys) sub -> 
    (module BIND_TERMS_CONT with type base_ctx = ys) ->
    ys Target.command =
    fun terms h (module K) ->
      match terms with
      | [] -> K.cont Keep Nil
      | a :: rest ->
        bind_term a h
          (module struct
            type base_ctx = ys
            let cont : type zs a. (base_ctx, zs) sub -> (zs, a) name -> zs Target.command =
              fun i v ->
                bind_terms rest (Comp (h, i))
                  (module struct
                    type base_ctx = zs
                    let cont : type ws ps.
                        (base_ctx, ws) sub -> (ws Target.ex_name, ps) env -> ws Target.command =
                      fun j vs ->
                        K.cont (Comp (i, j)) (Cons (Target.rename_ex j (Target.ExName v), vs))
                  end)
          end)

  (** Main transformation function *)
  and transform_command : type xs ys.
    xs Source.command -> (xs, ys) sub -> ys Target.command =
    fun cmd h ->
      match cmd with
      | CutPos (sig_, Variable x, Variable y) ->
        Target.CutMatch (sig_, rename h x,
          build_branches_from_sig sig_
            (module struct
              type ctx = ys
              let build : type ps ps_ctx.
                  (ps, ctx, ps_ctx) append -> int -> ps_ctx Target.command =
                fun ps_app n ->
                  let fresh = fresh_names ps_app in
                  Target.CutConstructor (sig_, n, fresh,
                    rename (Comp (h, weak_many ps_app)) y)
            end))

      | CutPos (sig_, Variable x, Match (_, bs)) ->
        Target.CutMatch (sig_, rename h x, transform_source_branches bs h)

      | CutPos (_, Variable x, MuRhsPos (_, r)) ->
        (* The existential types from Variable and MuRhsPos are semantically equal *)
        transform_command (Obj.magic r) (Comp (substitute x, h))

      | CutPos (sig_, Constructor (_, n, args), Variable y) ->
        bind_terms (term_list_to_list args) h
          (module struct
            type base_ctx = ys
            let cont : type zs ps.
                (base_ctx, zs) sub -> (zs Target.ex_name, ps) env -> zs Target.command =
              fun i vs -> Target.CutConstructor (sig_, n, vs, rename (Comp (h, i)) y)
          end)

      | CutPos (_sig_, Constructor (_, n, args), Match (_, bs)) ->
        bind_terms (term_list_to_list args) h
          (module struct
            type base_ctx = ys
            let cont : type zs ps.
                (base_ctx, zs) sub -> (zs Target.ex_name, ps) env -> zs Target.command =
              fun i vs ->
                (* Transform branches and lookup the n-th one *)
                let branches = transform_source_branches bs (Comp (h, i)) in
                lookup_branch_body branches n vs
          end)

      | CutPos (sig_, Constructor (_, n, args), MuRhsPos (_, r)) ->
        bind_terms (term_list_to_list args) h
          (module struct
            type base_ctx = ys
            let cont : type zs ps.
                (base_ctx, zs) sub -> (zs Target.ex_name, ps) env -> zs Target.command =
              fun i vs ->
                Target.LetConstructor (sig_, n, vs, transform_command r (Lift (Comp (h, i))))
          end)

      | CutPos (_, MuLhsPos (_, s), Variable y) ->
        (* The existential types from MuLhsPos and Variable are semantically equal *)
        transform_command s (Comp (substitute (Obj.magic y), h))

      | CutPos (sig_, MuLhsPos (_, s), Match (_, bs)) ->
        Target.LetMatch (sig_, transform_source_branches bs h,
          transform_command s (Lift h))

      | CutPos (sig_, MuLhsPos (_, s), MuRhsPos (_, r)) ->
        Target.LetMatch (sig_,
          build_branches_from_sig sig_
            (module struct
              type ctx = ys
              let build : type ps ps_ctx.
                  (ps, ctx, ps_ctx) append -> int -> ps_ctx Target.command =
                fun ps_app n ->
                  let fresh = fresh_names ps_app in
                  Target.LetConstructor (sig_, n, fresh,
                  transform_command r (Lift (Comp (h, weak_many ps_app))))
            end),
          transform_command s (Lift h))

      | CutNeg (sig_, Variable x, Variable y) ->
        Target.CutComatch (sig_,
          build_branches_from_sig sig_
            (module struct
              type ctx = ys
              let build : type ps ps_ctx.
                  (ps, ctx, ps_ctx) append -> int -> ps_ctx Target.command =
                fun ps_app n ->
                  let fresh = fresh_names ps_app in
                  Target.CutDestructor (sig_,
                    rename (Comp (h, weak_many ps_app)) x, n, fresh)
            end),
          rename h y)

      | CutNeg (sig_, Variable x, Destructor (_, n, args)) ->
        bind_terms (term_list_to_list args) h
          (module struct
            type base_ctx = ys
            let cont : type zs ps.
                (base_ctx, zs) sub -> (zs Target.ex_name, ps) env -> zs Target.command =
              fun i vs -> Target.CutDestructor (sig_, rename (Comp (h, i)) x, n, vs)
          end)

      | CutNeg (_, Variable x, MuRhsNeg (_, r)) ->
        (* The existential types from Variable and MuRhsNeg are semantically equal *)
        transform_command (Obj.magic r) (Comp (substitute x, h))

      | CutNeg (sig_, Comatch (_, bs), Variable y) ->
        Target.CutComatch (sig_, transform_source_branches bs h, rename h y)

      | CutNeg (_sig_, Comatch (_, bs), Destructor (_, n, args)) ->
        bind_terms (term_list_to_list args) h
          (module struct
            type base_ctx = ys
            let cont : type zs ps.
                (base_ctx, zs) sub -> (zs Target.ex_name, ps) env -> zs Target.command =
              fun i vs ->
                (* Transform branches and lookup the n-th one *)
                let branches = transform_source_branches bs (Comp (h, i)) in
                lookup_branch_body branches n vs
          end)

      | CutNeg (sig_, Comatch (_, bs), MuRhsNeg (_, r)) ->
        Target.LetComatch (sig_, transform_source_branches bs h,
          transform_command r (Lift h))

      | CutNeg (_, MuLhsNeg (_, s), Variable y) ->
        (* The existential types from MuLhsNeg and Variable are semantically equal *)
        transform_command s (Comp (substitute (Obj.magic y), h))

      | CutNeg (sig_, MuLhsNeg (_, s), Destructor (_, n, args)) ->
        bind_terms (term_list_to_list args) h
          (module struct
            type base_ctx = ys
            let cont : type zs ps.
                (base_ctx, zs) sub -> (zs Target.ex_name, ps) env -> zs Target.command =
              fun i vs ->
                Target.LetDestructor (sig_, n, vs,
                  transform_command s (Lift (Comp (h, i))))
          end)

      | CutNeg (sig_, MuLhsNeg (_, s), MuRhsNeg (_, r)) ->
        Target.LetComatch (sig_,
          build_branches_from_sig sig_
            (module struct
              type ctx = ys
              let build : type ps ps_ctx.
                  (ps, ctx, ps_ctx) append -> int -> ps_ctx Target.command =
                fun ps_app n ->
                  let fresh = fresh_names ps_app in
                  Target.LetDestructor (sig_, n, fresh,
                    transform_command s (Lift (Comp (h, weak_many ps_app))))
            end),
          transform_command r (Lift h))

      | End -> Target.End

      | CutPos (_, _, _) -> 
          failwith "ill-typed: CutPos requires (Variable|Constructor|MuLhsPos) on LHS and (Variable|Match|MuRhsPos) on RHS"
      | CutNeg (_, _, _) -> 
          failwith "ill-typed: CutNeg requires (Variable|Comatch|MuLhsNeg) on LHS and (Variable|Destructor|MuRhsNeg) on RHS"
end

(**
   {1 Polarity Preservation}

   There's a natural polarity assignment for Target commands that makes
   the transformation polarity-preserving.

   {2 Polarity Assignment for Target}

   {b Positive commands:}
   - [LetConstructor]  — Binds a constructor (positive intro)
   - [LetMatch]        — Binds a match (positive elim)
   - [CutConstructor]  — Constructor against variable
   - [CutMatch]        — Match against variable

   {b Negative commands:}
   - [LetComatch]      — Binds a comatch (negative intro)
   - [LetDestructor]   — Binds a destructor (negative elim)
   - [CutComatch]      — Comatch against variable
   - [CutDestructor]   — Variable against destructor

   {b Neutral:}
   - [End]             — Terminal

   {2 Why the Transformation Preserves Polarity}

   Looking at [transform_command]:

   {b Source.CutPos (positive)} transforms to:
   - [CutConstructor] when LHS is Constructor, RHS is Variable
   - [CutMatch] when RHS is Match
   - [LetConstructor] + continuation when LHS is Constructor, RHS needs binding
   - [LetMatch] + continuation when LHS is MuLhsPos

   {b Source.CutNeg (negative)} transforms to:
   - [CutComatch] when LHS is Comatch
   - [CutDestructor] when RHS is Destructor, LHS is Variable
   - [LetComatch] + continuation when RHS is MuRhsNeg
   - [LetDestructor] + continuation when RHS is Destructor, LHS needs binding

   {2 The Pattern}

   The polarity is determined by which {i type former} is involved:
   - {b Positive types} (data): Constructors and Matches
   - {b Negative types} (codata): Comatches and Destructors

   The Let-bindings inherit polarity from what they bind, and the Cut-forms
   inherit polarity from their non-variable component. This reflects the
   focusing discipline: positive cuts involve positive connectives,
   negative cuts involve negative connectives.
*)