module AxCutNormalForm

-- Contexts and environments

{-
    We use De Bruijn indices and elements of typing contexts are represented as
    positions in a list.
-}
data Name : List k -> k -> Type where
  Z : Name (x :: xs) x
  S : Name xs x -> Name (y :: xs) x

{-
    Runtime Environments are represented as lists over contexts.
-}
data Env : (k -> Type) -> List k -> Type where
  Nil : Env f []
  (::) : {0 x : k} -> {0 xs : List k} -> {0 f : k -> Type} -> f x -> Env f xs -> Env f (x :: xs)


-- Structural rules for contexts

data Sub : List k -> List k -> Type where
  Keep : Sub xs xs
  Comp : Sub xs ys -> Sub ys zs -> Sub xs zs
  Lift : Sub xs ys -> Sub (z :: xs) (z :: ys)
  Weak : Sub xs (x :: xs)
  Copy : Sub (x :: x :: xs) (x :: xs)
  Swap : Sub (x :: y :: xs) (y :: x :: xs)


weakMany : (ys : List k) -> Sub xs (ys ++ xs)
weakMany [] = Keep
weakMany (y :: ys) = Comp (weakMany ys) Weak

liftMany : (zs : List k) -> Sub xs ys -> Sub (zs ++ xs) (zs ++ ys)
liftMany [] h = h
liftMany (z :: zs) h = Lift (liftMany zs h)

substitute : Name xs t -> Sub (t :: xs) xs
substitute Z = Copy
substitute (S x) = Comp Swap (Lift (substitute x))

substituteMany : Env (Name zs) ts -> Sub (ts ++ zs) zs
substituteMany [] = Keep
substituteMany (v :: vs) = Comp (Lift (substituteMany vs)) (substitute v)


lookup : Env f xs -> Name xs x -> f x
lookup [] Z impossible
lookup [] (S x) impossible
lookup (v :: _) Z = v
lookup (_ :: vs) (S x) = lookup vs x

transform : ({0 x : k} -> f x -> g x) -> Env f xs -> Env g xs
transform t [] = []
transform t (v :: vs) = t v :: transform t vs

concat : {0 xs : List k} -> {0 ys : List k} -> Env f xs -> Env f ys -> Env f (xs ++ ys)
concat [] bs = bs
concat (a :: as) bs = a :: concat as bs

rename : Sub xs ys -> Name xs x -> Name ys x
rename Keep n = n
rename (Comp h i) n = rename i (rename h n)
rename Weak n = S n
rename (Lift h) Z = Z
rename (Lift h) (S y) = S (rename h y)
rename Copy Z = Z
rename Copy (S x) = x
rename Swap Z = S Z
rename Swap (S Z) = Z
rename Swap (S (S x)) = S (S x)

fresh : (xs : List k) -> Env (Name xs) xs
fresh [] = []
fresh (x :: xs) = Z :: transform (rename Weak) (fresh xs)



-- Types

mutual
  data Tpe : Type where
    Pos : Signature -> Tpe
    Neg : Signature -> Tpe

  data ChiralTpe : Type where
    Lhs : Tpe -> ChiralTpe
    Rhs : Tpe -> ChiralTpe

  Signature : Type
  Signature = List (List ChiralTpe)

-- Source language

{-
    We use intrinsic typing, so language constructs are represented by their
    typing derivations. Thus, in `Command` the list `xs` is the typing context.
-}
namespace Source
  mutual
    public export
    data Command : List ChiralTpe -> Type where
      CutPos : {sig : Signature} -> Term xs (Lhs (Pos sig)) -> Term xs (Rhs (Pos sig)) -> Command xs
      CutNeg : {sig : Signature} -> Term xs (Lhs (Neg sig)) -> Term xs (Rhs (Neg sig)) -> Command xs
      End : Command xs

    public export
    data Term : List ChiralTpe -> ChiralTpe -> Type where
      Variable : Name xs t -> Term xs t
      Constructor : Name sig ps -> Env (Term xs) ps -> Term xs (Lhs (Pos sig))
      Match : Env (Branch xs) sig -> Term xs (Rhs (Pos sig))
      Comatch : Env (Branch xs) sig -> Term xs (Lhs (Neg sig))
      Destructor : Name sig ps -> Env (Term xs) ps -> Term xs (Rhs (Neg sig))
      MuLhsPos : Command (Rhs (Pos sig) :: xs) -> Term xs (Lhs (Pos sig))
      MuRhsPos : Command (Lhs (Pos sig) :: xs) -> Term xs (Rhs (Pos sig))
      MuLhsNeg : Command (Rhs (Neg sig) :: xs) -> Term xs (Lhs (Neg sig))
      MuRhsNeg : Command (Lhs (Neg sig) :: xs) -> Term xs (Rhs (Neg sig))

    public export
    data Branch : List ChiralTpe -> List ChiralTpe -> Type where
      Clause : {ps : List ChiralTpe} -> Command (ps ++ xs) -> Branch xs ps


-- Target language

{-
    We use intrinsic typing, so language constructs are represented by their
    typing derivations. Thus, in `Command` the list `xs` is the typing context.
-}
namespace Target
  mutual
    public export
    data Command : List ChiralTpe -> Type where
      LetConstructor : Name sig ps -> Env (Name xs) ps -> Target.Command ((Lhs (Pos sig)) :: xs) -> Command xs
      LetMatch : Env (Target.Branch xs) sig -> Target.Command ((Rhs (Pos sig)) :: xs) -> Command xs
      LetComatch : Env (Target.Branch xs) sig -> Target.Command ((Lhs (Neg sig)) :: xs) -> Command xs
      LetDestructor : Name sig ps -> Env (Name xs) ps -> Target.Command ((Rhs (Neg sig)) :: xs) -> Command xs
      CutConstructor : Name sig ps -> Env (Name xs) ps -> Name xs (Rhs (Pos sig)) -> Command xs
      CutMatch : Name xs (Lhs (Pos sig)) -> Env (Target.Branch xs) sig -> Command xs
      CutComatch : Env (Target.Branch xs) sig -> Name xs (Rhs (Neg sig)) -> Command xs
      CutDestructor : Name xs (Lhs (Neg sig)) -> Name sig ps -> Env (Name xs) ps -> Command xs
      End : Command xs

    public export
    data Branch : List ChiralTpe -> (List ChiralTpe) -> Type where
      Clause : {ps : List ChiralTpe} -> Target.Command (ps ++ xs) -> Branch xs ps

    public export
    renameCommand : Sub xs ys -> Target.Command xs -> Target.Command ys
    renameCommand h (LetConstructor n vs s) = LetConstructor n (transform (rename h) vs) (renameCommand (Lift h) s)
    renameCommand h (LetMatch m s) = LetMatch (renameBranches h m) (renameCommand (Lift h) s)
    renameCommand h (LetComatch m s) = LetComatch (renameBranches h m) (renameCommand (Lift h) s)
    renameCommand h (LetDestructor n vs s) = LetDestructor n (transform (rename h) vs) (renameCommand (Lift h) s)
    renameCommand h (CutConstructor n vs a) = CutConstructor n (transform (rename h) vs) (rename h a)
    renameCommand h (CutMatch a m) = CutMatch (rename h a) (renameBranches h m)
    renameCommand h (CutComatch m a) = CutComatch (renameBranches h m) (rename h a)
    renameCommand h (CutDestructor a n vs) = CutDestructor (rename h a) n (transform (rename h) vs)
    renameCommand h End = End

    public export
    renameBranch : Sub xs ys -> Target.Branch xs ps -> Target.Branch ys ps
    renameBranch h (Clause {ps} s) = Clause (renameCommand (liftMany ps h) s)

    renameBranches : Sub xs ys -> Env (Target.Branch xs) sig -> Env (Target.Branch ys) sig
    renameBranches h [] = []
    renameBranches h (b :: bs) = renameBranch h b :: renameBranches h bs


data Tped : (k -> Type) -> k -> Type where
  TN : {a : k} -> f a -> Tped f a

freshCases : {sig : List (List ChiralTpe)} -> Env (Tped (Name sig)) sig
freshCases {sig = []} = []
freshCases {sig = ps :: tss} = TN Z :: transform (\(TN n) => TN (S n)) freshCases

freshNames : {ps : List ChiralTpe} -> Env (Name (ps ++ ys)) ps
freshNames {ps = []} = []
freshNames {ps = x :: xs} = Z :: transform S freshNames

findTpe : {sig : List (List ChiralTpe)} -> Name sig ts -> Tped (Name sig) ts
findTpe Z = TN Z
findTpe (S x) = case findTpe x of TN y => TN (S y)


-- Transformation

mutual
  total
  transformCommand : Source.Command xs -> Sub xs ys -> Target.Command ys
  transformCommand (CutPos (Variable x) (Variable y)) h =
    CutMatch (rename h x) (transform (\(TN {a=ps} n) => Clause (CutConstructor n freshNames (rename (Comp h (weakMany ps)) y))) freshCases)
  transformCommand (CutPos (Variable x) (Match bs)) h =
    CutMatch (rename h x) (transformBranches bs h)
  transformCommand (CutPos (Variable x) (MuRhsPos r)) h =
    transformCommand r (Comp (substitute x) h)
  transformCommand (CutPos (Constructor n as) (Variable y)) h =
    case findTpe n of
         TN m => bindTerms as h (\i => \vs => CutConstructor m vs (rename (Comp h i) y))
  transformCommand (CutPos (Constructor n as) (Match bs)) h =
    --case lookup bs n of
    --     Clause {ps} s => bindTerms as h (\i => \vs => transformCommand s (Comp (liftMany ps (Comp h i)) (substituteMany vs)))
    case findTpe n of
         TN m => bindTerms as h (\i => \vs => case lookupClause (transformBranches bs (Comp h i)) m of
                                                   Clause {ps} s => renameCommand (Comp (liftMany ps Keep) (substituteMany vs)) s)
  transformCommand (CutPos (Constructor n as) (MuRhsPos r)) h =
    case findTpe n of
         TN m => bindTerms as h (\i => \vs => LetConstructor m vs (transformCommand r (Lift (Comp h i))))
  transformCommand (CutPos (MuLhsPos s) (Variable y)) h =
    transformCommand s (Comp (substitute y) h)
  transformCommand (CutPos (MuLhsPos s) (Match bs)) h =
    LetMatch (transformBranches bs h) (transformCommand s (Lift h))
  transformCommand (CutPos (MuLhsPos s) (MuRhsPos r)) h =
    LetMatch (transform (\(TN {a=ps} n) => Clause (LetConstructor n freshNames (transformCommand r (Lift (Comp h (weakMany ps)))))) freshCases) (transformCommand s (Lift h))
  transformCommand (CutNeg (Variable x) (Variable y)) h =
    CutComatch (transform (\(TN {a=ps} n) => Clause (CutDestructor (rename (Comp h (weakMany ps)) x) n freshNames)) freshCases) (rename h y)
  transformCommand (CutNeg (Variable x) (Destructor n as)) h =
    case findTpe n of
         TN m => bindTerms as h (\i => \vs => CutDestructor (rename (Comp h i) x) m vs)
  transformCommand (CutNeg (Variable x) (MuRhsNeg r)) h =
    transformCommand r (Comp (substitute x) h)
  transformCommand (CutNeg (Comatch bs) (Variable y)) h =
    CutComatch (transformBranches bs h) (rename h y)
  transformCommand (CutNeg (Comatch bs) (Destructor n as)) h =
    --case lookup bs n of
    --     Clause {ps} s => bindTerms as h (\i => \vs => transformCommand s (Comp (liftMany ps (Comp h i)) (substituteMany vs)))
    case findTpe n of
         TN m => bindTerms as h (\i => \vs => case lookupClause (transformBranches bs (Comp h i)) m of
                                                   Clause {ps} s => renameCommand (Comp (liftMany ps Keep) (substituteMany vs)) s)
  transformCommand (CutNeg (Comatch bs) (MuRhsNeg r)) h =
    LetComatch (transformBranches bs h) (transformCommand r (Lift h))
  transformCommand (CutNeg (MuLhsNeg s) (Variable y)) h =
    transformCommand s (Comp (substitute y) h)
  transformCommand (CutNeg (MuLhsNeg s) (Destructor n as)) h =
    case findTpe n of
         TN m => bindTerms as h (\i => \vs => LetDestructor m vs (transformCommand s (Lift (Comp h i))))
  transformCommand (CutNeg (MuLhsNeg s) (MuRhsNeg r)) h =
    LetComatch (transform (\(TN {a=ps} n) => Clause (LetDestructor n freshNames (transformCommand s (Lift (Comp h (weakMany ps)))))) freshCases) (transformCommand r (Lift h))
  transformCommand End h =
    End

  lookupClause : Env (Target.Branch xs) sig -> Name sig ps -> (Target.Branch xs) ps
  lookupClause [] Z impossible
  lookupClause [] (S x) impossible
  lookupClause (b :: _) Z = b
  lookupClause (_ :: bs) (S x) = lookupClause bs x

  transformBranch : Source.Branch xs ps -> Sub xs ys -> Target.Branch ys ps
  transformBranch (Clause {ps} s) h = Clause (transformCommand s (liftMany ps h))

  transformBranches : Env (Source.Branch xs) sig -> Sub xs ys -> Env (Target.Branch ys) sig
  transformBranches [] h = []
  transformBranches (b :: bs) h = transformBranch b h :: transformBranches bs h

  bindTerm : {t : ChiralTpe} -> Source.Term xs t -> Sub xs ys -> ({0 zs : List ChiralTpe} -> Sub ys zs -> Name zs t -> Target.Command zs) -> Target.Command ys
  bindTerm (Variable x) h k =
    k Keep (rename h x)
  bindTerm (Constructor n as) h k =
    case findTpe n of
      TN m => bindTerms as h (\i => \vs => LetConstructor m vs (k (Comp i Weak) Z))
  bindTerm (Match bs) h k =
    LetMatch (transformBranches bs h)
      (k Weak Z)
  bindTerm (Comatch bs) h k =
    LetComatch (transformBranches bs h)
      (k Weak Z)
  bindTerm (Destructor n as) h k =
    case findTpe n of
      TN m => bindTerms as h (\i => \vs => LetDestructor m vs (k (Comp i Weak) Z))
  bindTerm (MuLhsPos s) h k =
    LetMatch (transform (\(TN {a=ps} n) => Clause (LetConstructor n freshNames (k (Comp (weakMany ps) Weak) Z))) freshCases)
      (transformCommand s (Lift h))
  bindTerm (MuRhsPos s) h k =
    LetMatch (transform (\(TN {a=ps} n) => Clause (LetConstructor n freshNames (transformCommand s (Lift (Comp h (weakMany ps)))))) freshCases)
      (k Weak Z)
  bindTerm (MuLhsNeg s) h k =
    LetComatch (transform (\(TN {a=ps} n) => Clause (LetDestructor n freshNames (transformCommand s (Lift (Comp h (weakMany ps)))))) freshCases)
      (k Weak Z)
  bindTerm (MuRhsNeg s) h k =
    LetComatch (transform (\(TN {a=ps} n) => Clause (LetDestructor n freshNames (k (Comp (weakMany ps) Weak) Z))) freshCases)
      (transformCommand s (Lift h))

  bindTerms : {ts : List ChiralTpe} -> Env (Source.Term xs) ts -> Sub xs ys -> ({0 zs : List ChiralTpe} -> Sub ys zs -> Env (Name zs) ts -> Target.Command zs) -> Target.Command ys
  bindTerms [] h k = k Keep []
  bindTerms (a :: as) h k = bindTerm a h (\i => \v => bindTerms as (Comp h i) (\j => \vs => k (Comp i j) (rename j v :: vs)))
