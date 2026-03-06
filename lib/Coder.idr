module AARCH64.Coder

import Types
import AARCH64.Code
import AARCH64.Limited
import AARCH64.Substitution

import Data.Vect
import Data.List
import Control.Monad.State


-- GOTCHAS
-- 0 must not be the address of a block
-- initially heap must point to a fresh block
-- initially free must point to enough space
-- free must be initially filled with 0


positionFromEnd : (as : Arguments d) -> Symbol as a -> Nat
positionFromEnd (b :: []) Z = Z
positionFromEnd (b :: c :: cs) Z = S (positionFromEnd (c :: cs) Z)
positionFromEnd (b :: bs) (S x) = positionFromEnd bs x

unsafeFits : Nat -> Fin 31
unsafeFits n = case natToFin (reserved + n) 31 of
  Just r => r
  Nothing => assert_total (idris_crash "out of registers")

symbolRegister1 : (as : Arguments d) -> Symbol as a -> Register
symbolRegister1 as x = unsafeFits (2 * positionFromEnd as x)

symbolRegister2 : (as : Arguments d) -> Symbol as a -> Register
symbolRegister2 as x = unsafeFits (S (2 * positionFromEnd as x))

freshRegister1 : (as : Arguments d) -> Register
freshRegister1 as = unsafeFits (2 * length as)

freshRegister2 : (as : Arguments d) -> Register
freshRegister2 as = unsafeFits (S (2 * length as))


symbolToNat : Symbol as a -> Nat
symbolToNat Z = 0
symbolToNat (S i) = S (symbolToNat i)


skipIfZero : Register -> List Code -> State Integer (List Code)
skipIfZero this code = do
  freshLab <- get
  _ <- put (1 + freshLab)
  pure (
    CMPI this 0 ::
    BEQ ("lab" ++ show freshLab) ::
    code ++
    LAB ("lab" ++ show freshLab) ::
    [])

ifZeroThenElse : Register -> List Code -> List Code -> State Integer (List Code)
ifZeroThenElse this thn els = do
  freshLabThen <- get
  _ <- put (1 + freshLabThen)
  freshLabElse <- get
  _ <- put (1 + freshLabElse)
  pure (
    CMPI this 0 ::
    BEQ ("lab" ++ show freshLabThen) ::
    els ++
    B ("lab" ++ show freshLabElse) ::
    LAB ("lab" ++ show freshLabThen) ::
    thn ++
    LAB ("lab" ++ show freshLabElse) ::
    [])


shareBlockN : Register -> Nat -> State Integer (List Code)
shareBlockN this k =
  skipIfZero this (
    LDR temp this referenceCountOffset ::
    ADDI temp temp (natToInteger k) ::
    STR temp this referenceCountOffset ::
    [])

shareBlock : Register -> State Integer (List Code)
shareBlock this = shareBlockN this 1

eraseValidObject : Register -> State Integer (List Code)
eraseValidObject this =
  ifZeroThenElse temp (
    STR free this nextElementOffset ::
    MOVR free this ::
    []
    ) (
    SUBI temp temp 1 ::
    STR temp this referenceCountOffset ::
    [])

eraseBlock : Register -> State Integer (List Code)
eraseBlock this = do
  eraseValidObject <- eraseValidObject this
  skipIfZero this (
    LDR temp this referenceCountOffset ::
    eraseValidObject)


shareFields : Register -> Register -> Nat -> State Integer (List Code)
shareFields accu this Z = pure []
shareFields accu this (S i) = do
  shareBlock <- shareBlock accu
  shareFields <- shareFields accu this i
  pure (
    LDR accu this (fieldOffset1 i) ::
    shareBlock ++
    shareFields)

eraseFields : Register -> Register -> Nat -> State Integer (List Code)
eraseFields accu this Z = pure []
eraseFields accu this (S i) = do
  eraseBlock <- eraseBlock accu
  eraseFields <- eraseFields accu this i
  pure (
    LDR accu this (fieldOffset1 i) ::
    eraseBlock ++
    eraseFields)


acquireBlock : Register -> Register -> State Integer (List Code)
acquireBlock accu this = do
  eraseFields <- eraseFields accu heap FieldsPerBlock
  adaptFree <- ifZeroThenElse free (
                 ADDI free heap (fieldOffset1 FieldsPerBlock) ::
                 []
                 ) (
                 MOVI temp 0 ::
                 STR temp heap nextElementOffset ::
                 eraseFields)
  adaptHeap <- ifZeroThenElse heap (
                 MOVR heap free ::
                 LDR free free nextElementOffset ::
                 adaptFree
                 ) (
                 MOVI temp 0 ::
                 STR temp this referenceCountOffset ::
                 [])
  pure (
    MOVR this heap ::
    LDR heap heap nextElementOffset ::
    adaptHeap)

releaseBlock : Register -> Register -> State Integer (List Code)
releaseBlock accu this = do
  shareFields <- shareFields accu this FieldsPerBlock
  adaptHeap <- ifZeroThenElse temp (
                 STR heap this nextElementOffset ::
                 MOVR heap this ::
                 []
                 ) (
                 SUBI temp temp 1 ::
                 STR temp this referenceCountOffset ::
                 -- TODO only share those that are actually loaded
                 shareFields)
  pure (
    LDR temp this referenceCountOffset ::
    adaptHeap)


storeValue : (v : Tpe d) -> (as : Arguments d) -> Register -> (k : Nat) -> List Code
storeValue (Ext t) as into k =
  STR (symbolRegister2 (Ext t :: as) Z) into (fieldOffset2 k) ::
  MOVI temp 0 ::
  STR temp into (fieldOffset1 k) ::
  []
storeValue v as into k =
  STR (symbolRegister2 (v :: as) Z) into (fieldOffset2 k) ::
  STR (symbolRegister1 (v :: as) Z) into (fieldOffset1 k) ::
  []

loadBinder : (x : Tpe d) -> (as : Arguments d) -> Register -> (k : Nat) -> List Code
loadBinder (Ext t) as from k =
  LDR (symbolRegister2 (Ext t :: as) Z) from (fieldOffset2 k) ::
  []
loadBinder x as from k =
  LDR (symbolRegister2 (x :: as) Z) from (fieldOffset2 k) ::
  LDR (symbolRegister1 (x :: as) Z) from (fieldOffset1 k) ::
  []


storeBlock : (as : Arguments d) -> Register -> Nat -> List Code
storeBlock as into k =
  STR (freshRegister1 as) into (fieldOffset1 k) ::
  []

loadBlock : (as : Arguments d) -> Register -> Nat -> List Code
loadBlock as from k =
  LDR (freshRegister1 as) from (fieldOffset1 k) ::
  []


storeZeroes : Register -> Nat -> List Code
storeZeroes into Z =
  []
storeZeroes into (S k) =
  MOVI temp 0 ::
  STR temp into (fieldOffset1 k) ::
  storeZeroes into k

storeValues : (vs : Arguments d) -> (as : Arguments d) -> Register -> Nat -> List Code
storeValues [] as into k =
  storeZeroes into k
storeValues (v :: vs) as into Z =
  -- TODO should not happen
  []
storeValues (v :: vs) as into (S k) =
  storeValue v (vs ++ as) into k ++
  storeValues vs as into k

loadBinders : (xs : Arguments d) -> (as : Arguments d) -> Register -> Nat -> List Code
loadBinders [] as from k =
  []
loadBinders (x :: xs) as from Z =
  -- TODO should not happen
  []
loadBinders (x :: xs) as from (S k) =
  loadBinder x (xs ++ as) from k ++
  loadBinders xs as from k


storeRest : (vs : Arguments d) -> (as : Arguments d) -> State Integer (List Code)
storeRest [] as = do
  pure []
storeRest (v :: vs) as = do
  let vars = take (pred FieldsPerBlock) (v :: vs)
      rest = drop (pred FieldsPerBlock) (v :: vs)
      this = freshRegister1 (rest ++ as)
      accu = freshRegister2 (rest ++ as)
  acquireBlock <- acquireBlock accu this
  storeRest <- storeRest rest as
  pure (
    storeBlock (vars ++ rest ++ as) heap (pred FieldsPerBlock) ++
    storeValues vars (rest ++ as) heap (pred FieldsPerBlock) ++
    acquireBlock ++
    storeRest)

store : (vs : Arguments d) -> (as : Arguments d) -> State Integer (List Code)
store [] as =
  pure (
    MOVI (freshRegister1 as) 0 ::
    [])
store vs as = do
  let vars = take FieldsPerBlock vs
      rest = drop FieldsPerBlock vs
      this = freshRegister1 (rest ++ as)
      accu = freshRegister2 (rest ++ as)
  acquireBlock <- acquireBlock accu this
  storeRest <- storeRest rest as
  pure (
    storeValues vars (rest ++ as) heap FieldsPerBlock ++
    acquireBlock ++
    storeRest)


loadRest : (xs : Arguments d) -> (as : Arguments d) -> State Integer (List Code)
loadRest [] as = do
  pure []
loadRest (x :: xs) as = do
  let vars = take (pred FieldsPerBlock) (x :: xs)
      rest = drop (pred FieldsPerBlock) (x :: xs)
      this = freshRegister1 (rest ++ as)
      accu = freshRegister2 (rest ++ as)
  loadRest <- loadRest rest as
  releaseBlock <- releaseBlock accu this
  pure (
    loadRest ++
    releaseBlock ++
    loadBlock (vars ++ rest ++ as) this (pred FieldsPerBlock) ++
    loadBinders vars (rest ++ as) this (pred FieldsPerBlock))

load : (xs : Arguments d) -> (as : Arguments d) -> State Integer (List Code)
load [] as =
  pure []
load xs as = do
  let vars = take FieldsPerBlock xs
      rest = drop FieldsPerBlock xs
      this = freshRegister1 (rest ++ as)
      accu = freshRegister2 (rest ++ as)
  loadRest <- loadRest rest as
  releaseBlock <- releaseBlock accu this
  pure (
    loadRest ++
    releaseBlock ++
    loadBinders vars (rest ++ as) this FieldsPerBlock)


codeTable : Nat -> Integer -> Integer -> List Code
codeTable 0 _ _ = []
codeTable (S k) labBase labBranch =
  B ("lab" ++ show labBase ++ "b" ++ show labBranch) ::
  codeTable k labBase (1 + labBranch)


isSame : Symbol as a -> Symbol as b -> Maybe (a = b)
isSame Z Z = Just Refl
isSame Z (S x) = Nothing
isSame (S x) Z = Nothing
isSame (S x) (S y) = do
  Refl <- isSame x y
  Just Refl

occurences : Substitution bs cs -> Substitution as cs -> Symbol as a -> List (Symbol bs a)
occurences [] [] z = []
occurences (x :: xs) (y :: ys) z = case isSame y z of
  Nothing => occurences xs ys z
  Just Refl => x :: occurences xs ys z

transpose : {as : Arguments d} -> {bs : Arguments d} -> Substitution as bs -> Table (\b => List (Symbol bs b)) as
transpose xs = transform (occurences identity xs) identity

updateReferenceCount : Register -> Nat -> State Integer (List Code)
updateReferenceCount x Z =
  eraseBlock x
updateReferenceCount x (S Z) =
  pure []
updateReferenceCount x (S (S n)) =
  shareBlockN x (S n)

codeWeakeningContraction : {as : Arguments d} -> Table (\b => List (Symbol bs b)) as -> State Integer (List Code)
codeWeakeningContraction [] =
  pure []
codeWeakeningContraction {as = Ext t :: as} (r :: rs) =
  codeWeakeningContraction {as} rs
codeWeakeningContraction {as = a :: as} (r :: rs) = do
  update <- updateReferenceCount (symbolRegister1 (a :: as) Z) (length r)
  updateRest <- codeWeakeningContraction {as} rs
  pure (
    update ++
    updateRest)

connections : {as : Arguments d} -> {bs : Arguments d} -> Table (\b => List (Symbol bs b)) as -> Vect 31 (List Register)
connections [] =
  replicate 31 []
connections {as = Ext t :: as} {bs} (xs :: xss) =
  replaceAt (symbolRegister2 (Ext t :: as) Z) (map (symbolRegister2 bs) xs) (
  connections {as} {bs} xss)
connections {as = a :: as} {bs} (xs :: xss) =
  replaceAt (symbolRegister1 (a :: as) Z) (map (symbolRegister1 bs) xs) (
  replaceAt (symbolRegister2 (a :: as) Z) (map (symbolRegister2 bs) xs) (
  connections {as} {bs} xss))


mutual
  public export
  codeStatement : {ts : Vect d (Signature d)} -> Statement ts ps as -> State Integer (List Code)
  codeStatement (Substitute {as} {bs} xs s) = do
    let targets = transpose {as} {bs} xs
    weakenContract <- codeWeakeningContraction targets
    rest <- codeStatement s
    pure (
      weakenContract ++
      codeExchange (connections targets) ++
      rest)
  codeStatement (Jump l) = pure (
    B ("lab" ++ show (symbolToNat l)) ::
    [])
  codeStatement (Let {t} {as} {bs} i s) = do
    let tag = symbolRegister2 (Pro t :: as) Z
    stores <- store bs as
    rest <- codeStatement s
    pure (
      stores ++
      MOVI tag (jumpLength (symbolToNat i)) ::
      rest)
  codeStatement (Switch {t} {as} ss) = do
    let tag = symbolRegister2 (Pro t :: as) Z
    freshLab <- get
    _ <- put (1 + freshLab)
    code <- codeClauses as (index t ts) ss freshLab 0
    let numBranches = length code
    pure (
      ADR temp ("lab" ++ show freshLab) ::
      (if numBranches <= 1
        then []
        else ADD temp temp tag :: []) ++
      BR temp ::
      LAB ("lab" ++ show freshLab) ::
      (if numBranches <= 1
        then []
        else codeTable numBranches freshLab 0) ++
      concat code)
  codeStatement (New {t} {as} {bs} ss s) = do
    let tab = symbolRegister2 (Con t :: as) Z
    stores <- store bs as
    freshLab <- get
    _ <- put (1 + freshLab)
    rest <- codeStatement s
    code <- codeMethods bs (index t ts) ss freshLab 0
    let numBranches = length code
    pure (
      stores ++
      ADR tab ("lab" ++ show freshLab) ::
      rest ++
      LAB ("lab" ++ show freshLab) ::
      (if numBranches <= 1
        then []
        else codeTable numBranches freshLab 0) ++
      concat code)
  codeStatement (Invoke {t} {as} i) = do
    let tab = symbolRegister2 (Con t :: as) Z
    pure (
      if length (index t ts) <= 1
        then BR tab ::
             []
        else ADDI temp tab (jumpLength (symbolToNat i)) ::
             BR temp ::
             [])
  codeStatement (Extern (Restart) [] []) = pure (
    B "lab0" ::
    [])
  codeStatement (Extern (Return) [x] []) = pure (
    MOVR return2 (symbolRegister2 as x) ::
    B "cleanup" ::
    [])
  codeStatement (Extern (Literal n) [] [s]) = do
    code <- codeStatement s
    pure(
      MOVI (symbolRegister2 (Ext "Int" :: as) Z) n ::
      code)
  codeStatement (Extern Add [x, y] [s]) = do
    code <- codeStatement s
    pure(
      ADD (symbolRegister2 (Ext "Int" :: as) Z) (symbolRegister2 as x) (symbolRegister2 as y) ::
      code)
  codeStatement (Extern Mul [x, y] [s]) = do
    code <- codeStatement s
    pure(
      MUL (symbolRegister2 (Ext "Int" :: as) Z) (symbolRegister2 as x) (symbolRegister2 as y) ::
      code)
  codeStatement (Extern Rem [x, y] [s]) = do
    code <- codeStatement s
    pure(
      SDIV temp (symbolRegister2 as x) (symbolRegister2 as y) ::
      MSUB (symbolRegister2 (Ext "Int" :: as) Z) temp (symbolRegister2 as y) (symbolRegister2 as x) ::
      code)
  codeStatement (Extern IfZero [x] [z, s]) = do
    freshLab <- get
    _ <- put (1 + freshLab)
    elseBranch <- codeStatement s
    thenBranch <- codeStatement z
    pure(
      CMPI (symbolRegister2 as x) 0 ::
      BEQ ("lab" ++ show freshLab) ::
      elseBranch ++
      LAB ("lab" ++ show freshLab) ::
      thenBranch)
  codeStatement (Extern IfEqual [x, y] [z, s]) = do
    freshLab <- get
    _ <- put (1 + freshLab)
    elseBranch <- codeStatement s
    thenBranch <- codeStatement z
    pure(
      CMPR (symbolRegister2 as x) (symbolRegister2 as y) ::
      BEQ ("lab" ++ show freshLab) ::
      elseBranch ++
      LAB ("lab" ++ show freshLab) ::
      thenBranch)
  codeStatement (Extern IfLess [x, y] [z, s]) = do
    freshLab <- get
    _ <- put (1 + freshLab)
    elseBranch <- codeStatement s
    thenBranch <- codeStatement z
    pure(
      CMPR (symbolRegister2 as x) (symbolRegister2 as y) ::
      BLT ("lab" ++ show freshLab) ::
      elseBranch ++
      LAB ("lab" ++ show freshLab) ::
      thenBranch)
  codeStatement (Extern _ _ _) = do
    -- TODO how to convince Idris 2?
    believe_me "total"

  codeClause : {ts : Vect d (Signature d)} -> (as : Arguments d) -> (cs : Arguments d) -> Statement ts ps (cs ++ as) -> State Integer (List Code)
  codeClause as cs s = do
    loads <- load cs as
    code <- codeStatement s
    pure (
      loads ++
      code)

  codeMethod : {ts : Vect d (Signature d)} -> (as : Arguments d) -> (cs : Arguments d) -> Statement ts ps (as ++ cs) -> State Integer (List Code)
  codeMethod as cs s = do
    loads <- load as cs
    code <- codeStatement s
    pure (
      loads ++
      code)

  codeClauses : {ts : Vect d (Signature d)} -> (as : Arguments d) -> (us : Signature d) -> Clauses ts ps as us -> Integer -> Integer -> State Integer (Vect (length us) (List Code)) 
  codeClauses as [] [] _ _ = pure []
  codeClauses as (cs :: us) (s :: ss) baseLab branchLab = do
    clause <- codeClause as cs s
    table <- codeClauses as us ss baseLab (1 + branchLab)
    pure (
      (LAB ("lab" ++ show baseLab ++ "b" ++ show branchLab) :: clause) ::
      table)

  codeMethods : {ts : Vect d (Signature d)} -> (as : Arguments d) -> (us : Signature d) -> Methods ts ps as us -> Integer -> Integer -> State Integer (Vect (length us) (List Code))
  codeMethods as [] [] _ _ = pure []
  codeMethods as (cs :: us) (s :: ss) baseLab branchLab = do
    method <- codeMethod as cs s
    table <- codeMethods as us ss baseLab (1 + branchLab)
    pure (
      (LAB ("lab" ++ show baseLab ++ "b" ++ show branchLab) :: method) ::
      table)


public export
translate : {ts : Vect d (Signature d)} -> Table (Statement ts ps) os -> State Integer (Vect (length os) (List Code)) 
translate [] = pure []
translate (s :: ls) = do
  code <- codeStatement s
  rest <- translate ls
  pure (code :: rest)


public export
assemble : Nat -> Vect n (List Code) -> List Code
assemble l [] = []
assemble l (is :: ss) = (LAB ("lab" ++ show l) :: is) ++ assemble (S l) ss


public export
compile : {ps : List (Arguments d)} -> {ts : Vect d (Signature d)} -> Program ts ps -> (List Code, Nat)
compile program = do
  let mainArgs = case head' ps of
                   Nothing => assert_total (idris_crash "there is no program")
                   Just mainArgs => mainArgs
      sections = evalState (natToInteger (length program)) (translate program)
  (assemble 0 sections, length mainArgs)
