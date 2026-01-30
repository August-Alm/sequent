
signature FOLDABLE
{
  type t: * -> *
  fold: [s] [a] (s -> a -> s) -> s -> t a -> s
}

module List: FOLDABLE
{

  data list: type -> type where {
    nil: [a] list(a);
    cons: [a] a -> list(a) -> list(a)
  }

  type t = list
  
  fold[s][a](foo: s -> a -> s)(state: s)(xs: list(a)) =
    match xs with {
      nil -> s;
      cons[a](x)(xs) -> fold[s][a](foo)(foo(state)(x))(xs)
    }

}

(length << tail)(z)

let foo{a}(x: a) = t
~
let foo = forall{a: type} fun(x: a) => t


fun{a}(x: a) => x   ~  all{a: type} fun(x: a) => x 
fun{a}(x: a) -> x
fun{a}(x: a). x

/-- The module implements fold for lists by
  the usual function. --/
module List: FOLDABLE
{

  data list: * -> *
    { nil: {a} list(a)
    ; cons: {a} a -> list(a) -> list(a)
    }

  type t = list
  
  fold{s}{a}(foo: s -> a -> s)(state: s)(xs: list(a)) =
    match xs with
    { nil -> s
    ; cons{a}(x)(xs) -> fold{s}{a}(foo)(foo(state)(x))(xs)
    }

}

signature FOLDABLE
{
  type t: type -> type
  val fold: {s: type} {a: type} (s -> a -> s) -> s -> t(a) -> s
}

code Either (A: Type) (B: Type) = {
  Handle {} (Par A B);
}

code monad: (* -> *) -> * where
  return: {m: * -> *} {a: *} monad(m) -> a -> m(a)
  bind: {m: * -> *} {a: *} {b: *} monad(m) -> m(a) -> (a -> m(b)) -> m(b)

data monad: (* -> *) -> * where
  mk_monad: {m: * -> *} {a: *} {b: *}
    

match xs with {
  nil => 0;
  cons{_}(h)(t) => h;
}

new {
  fst(_) => a;
  snd(_) => b
}

data list: * -> * where
  nil: {a} list(a);
  cons: {a} a -> list(a) -> list(a)
end

let fold[a][s](foo: s -> a -> s)(state: s)(xs: list(a)) =
  match xs with {
    nil => state;
    cons[a](x)(xs) => fold[a][s](foo)(foo(state)(x))(xs)
  }
  

(*
Then we can
*)

data list: type -> type
  nil: {a: type} list(a);
  cons: {a: type} a -> list(a) -> list(a);
end

data List(A: Type) where
  Nil: List(A)
  Cons: A -> List(A) -> List(A)

data Type(A: Type) where
  Num: Int -> Type
  Arrow: Type(A) -> Type(B) -> Type(A -> B)

data Expr(A: Type) where
  Lit: Int -> Expr(Int)
  Var: String -> Type(A) -> Expr(A)
  Lam: String -> Type(A) -> Expr(B) -> Expr(A -> B)
  App: Expr(A -> B) -> Expr(A) -> Expr(B)

codata Stream(A: Type) where
  Head: Stream(A) -> A
  Tail: Stream(A) -> Stream(A)

data typ(_: type) where
  tint: typ(int)
  tfun: {a: type} {b: type} -> typ(a) -> typ(b) -> typ(a -> b)

data expr(_: type) where
  var: {a: type} expr(a)
  lam: {a: type} {b: type} typ(a) -> expr(b) -> expr(a -> b)
  app: {a: type} {b: type} expr(a -> b) -> expr(a) -> expr(b)

data typ(a: type) where
  tint: typ(int)
  tfun{a: type}{b: type}(typ(a))(typ(b)): typ(a -> b)

data expr(_: type) where
  var{a: type}: expr(a)
  lam{a: type}{b: type}(typ(a))(expr(b)): expr(a -> b)
  app{a: type}{b: type}(expr(a -> b))(expr(a)): expr(b)

repeat(x: A) = new Stream(A) { _.Head = x; this.Tail = this }

repeat(x: A) = new { Head = x; Tail(this) = this }

repeat(x: a) = new { head => x; tail => repeat(x) }

code pair(a: type)(b: type) where
  fst: pair(a)(b) -> a
  snd: pair(a)(b) -> b

to_pair{a: type}{b: type}(xy: tuple(a)(b)): pair(a)(b) =
  match xy with
  tuple(x)(y) => new {fst => x, snd => y}

to_tuple{a: type}{b: type}(p: pair(a)(b)): tuple(a)(b) =
  tuple(fst(p))(snd(p))

let mult{T: Type}(z: T)(u: T)(m: T -> T -> T)(xs: List(T)) =
  block a { loop{T}(z)(u)(m)(xs)(a) }

and loop{T: Type}(z: T)(u: T)(m: T -> T -> T)(xs: List(T))(a: label T) =
  match xs with
  | Nil => u
  | Cons(x)(xs) =>
    if x = z then goto(z)(a) else m(x)(loop{T}(z)(m)(xs)(a))

fold{S: Type}{A: Type}(foo: S -> A -> S)(state: S)(xs: List(A)): S =
  match xs with
  List.nil => state
  List.cons(x)(xs) => fold{S}{A}(foo)(foo(state))(xs)

fresh_var(avoid: List(String)): String =
  let gen(idx: Int) =
    let candidate = String.concat("_x")(String.of_int(idx))
    if List.mem(candidate)(avoid) then gen(idx + 1) else candidate
  gen(0)

fold{s: type}{a: type}(foo: s -> a -> s)(state: s)(xs: list(a)): s =
  match xs with
    nil => state
    cons(x)(xs) => fold{s}{a}(foo)(foo(state))(xs)
  end


fold{s: type}{a: type}(foo: s -> a -> s)(state: s)(xs: list(a)): s =
  match xs {
    nil => state;
    cons(x)(xs) => fold{s}{a}(foo)(foo(state))(xs);
  }

fresh_var(avoid: list(string)): string =
  let gen(idx: int) =
    let candidate = String.concat("_x")(String.of_int(idx))
    if List.mem(candidate)(avoid) then gen(idx + 1) else candidate
  gen(0)

fold: {S: Type}{A: Type}((S -> A -> S) -> S -> List(A) -> S)
fold{S}{A}(foo)(state)(xs) =
  match xs with
  Nil => state
  Cons(x)(xs) => fold{S}{A}(foo)(foo(state))(xs)

fresh_var: List(String) -> String
fresh_var(avoid) =
  let gen(idx) =
    let candidate = String.concat("_x")(String.of_int(idx))
    if List.mem(candidate)(avoid) then gen(idx + 1) else candidate
  gen(0)

List: Type -> Type
List(A) = data
  Nil: List(A)
  Cons: A -> List(A) -> List(A)

data Type(A: Type) where
  Num: Type(Int)
  Arrow(Type(A), Type(B)): Type(A -> B)

data Expr(A: Type) where
  Lit(Int): Expr(Int)
  Var(String, Type(A)): Expr(A)
  Lam(String, Type(A), Expr(B)): Expr(A -> B)
  App(Expr(A -> B), Expr(A)): Expr(B)

codata Stream(A: Type) where
  head(Stream(A)): A
  tail(Stream(A)): Stream(A)

List :: (Type -> Type) =
  lam (A) (data
    (Nil ::               (List A))
    ((Cons A (List A)) :: (List A)))

Stream :: (Type -> Type) =
  lam (A) (codata
    ((Head (Stream A)) :: A)
    ((Tail (Stream A)) :: (Stream A)))

fold {S: Type} {A: Type} (foo: S -> A -> S) (state: S) (xs: (List A)) =
  case xs of
  | Nil => state
  | (Cons x xs) => (fold {S} {A} (foo state) xs)

def fold :: {S :: Type} {A :: Type} (S -> A -> S) -> S -> (List A) -> S =
  lam {S} {A} (foo state xs) (case xs
    (Nil state)
    ((Cons x xs) (fold {S} {A} (foo state) xs)))

def fresh-var :: (List String) -> String =
  lam (avoid)
    let gen = lam (counter)
      let candidate = (String.concat "_x" (String.of-int counter))
      if (List.mem candidate avoid)
      then (gen (+ 1 counter))
      else candidate
    (gen 0)

data List (A: Type) =
  | Nil: (List A)
  | Cons: A -> (List A) -> (List A)

codata Stream (A: Type) =
  { Head: (Stream A) -> A
    Tail: (Stream A) -> (Stream A) }

let repeat x = new (Stream Int) { this.Head = 1; this.Tail () = repeat x }

let fold {S A: Type} (f: (Fn S A S)) (s: S) (xs: (List A)) =
  (case xs
  (Nil         s)
  ((Cons x xs) (fold {S} {A} (f s) xs)))

(fesh-var (avoid (List String)) =
  let gen (counter Int) =
    let candidate = (String.concat "_x" (String.of-int counter))
    if (List.mem candidate avoid)
)

fold {s a type} (foo (fn s a s)) (state s) (xs (list a)) =
  (case xs
  (Nil         s)
  ((Cons x xs) (fold {s a} (foo state) xs)))

fresh-var (avoid (list string)) =
  (let gen (counter int) =
    (let canditate = (String.concat "_x" (string-of-int counter))
    (if (List.mem candidate avoid)
      (gen (+ counter 1))
      candidate))
  (gen 0))

data list (a: type) where
  Nil {}  ()           (list a) ()
  Cons {} (a (list a)) (list a) ()

codata forall (f: type -> type) where
  Instantiate {x} () (f x) ()

codata par (a: type) (b: type) where
  Handle {} () (par a b) (a b)

let fold {s: type} {a: type} (foo: s -> a -> s) (state: s) (xs: (list a)) =
  (match xs with
  (Nil state)
  ((Cons x xs) (fold{s}{a} (foo state) xs)))

let fesh_var (avoid: (list string)) =
  let gen (counter: int) =
    let candidate = (String.concat "_x" (String.of_int counter))
    if (List.mem candidate avoid) then (gen (+ counter 1))
    else candidate
  gen 0

let mult(xs: List(Int)) =
  block a { loop(xs)(a) }

and loop(xs: List(Int))(a: label Int) =
  match xs with
  | Nil => 1
  | Cons(x)(xs) =>
    if x = 0 then goto(0)(a) else x * loop(xs)(a)


var ::= "alphanumeric, lower case, starting with a letter, maybe containing _"

xtor ::= "alphanumeric, beginning with upper case letter"

int ::= "integer literal, ..., -1, 0, 1, 2, .."

type_ref ::=
    type_name
  | (label type_ref)
  | (type_ref type_ref)
  | type_ref -> type_ref
  | (type_ref) -> type_ref

var_dec ::= (var: type_ref) | ()

var_decs ::= var_dec | var dec var_decs

terms ::= term | term terms

case ::= xtor => term

term ::=
    ()
  | var 
  | int 
  | let var = term term
  | let var_decs = term term
  | fun var_decs -> term
  | (term terms)
  |

Conversion of Lang terms to Core term. First in pseudo-code:

let rec conv (tm: term) : producer =
  match tm with
  | TmInt n -> Int n
  | TmVar x -> Var x
  | TmSym sym ->
    (* Not sure what to do! If the symbol references a top-level
      function definition, and that definition is applied, we want
      to convert to a function call. *)

  | TmApp (t, u) ->
    match infer_typ t with
    | TyFun(a, b) ->
      let x = Ident.fresh () in
      (* Use the $apply destructor of the primitive $fun codata type *)
      μx.< conv t | $apply{a}{b}(x, conv u) >
    |  _ -> error

  | TmIns (t, ty) ->
    match infer_typ t with
    | TyAll((a, k), body) ->
      let a = Ident.fresh () in
      (* Use the $inst destructor of the primitive $forall codata type *)
      μa.< conv t | $inst{Convert.type body}{ty}(a) >
    | _ -> error

  | TmLam (x, Some a, t) ->
    let b = infer_typ t in
    let y = Ident.fresh () in
    new $fun{a}{b} { $apply{a}{b}(x, y) => < conv t | y >) }

  | TmAll ((a, k), t) ->
    let b = infer_typ t in
    let y = Ident.fresh () in
    new $forall {k} { $inst{a: k}(y) => < conv t | y > }

  (* let x = t in u *)
  | TmLet (x, t, u) ->
    let y = Ident.fresh () in
    μy.< conv t | μ̃x.< conv u | y > >

  (* match t with { clauses } *)
  | TmMatch (t, clauses) ->
    (* if clauses = { ctor_i{yj's}(tk's) => r_i };
      using that data type convert to essentially
      the same with Convert.type *)
    let y = Ident.fresh () in
    μy.< conv t | ctor_i{yj's}(tk's)(y) => < conv r_i | y >

  | TmNew clauses ->
    (* if clauses = { dtor_i{yj's}(tk's) => r_i };
      using that the codata type convert with Convert.type
      to get an extra consumer argument *)
    let y_i's = Ident.fresh ()'s in
    cocase { dtor_i{yj's}(tk's)(y_i) => < conv r_i | y_i > }

  (* ctor{ai's}(ti's); type and term arguments *)
  | TmCtor (ctor, ai's, ti's) ->
    (* data types convert to essentially themselves *)
    ctor{(Convert.type ai)'s}((conv ti)'s)

  (* dtor{ai's}(ti's); type and term arguments *)
  | TmDtor (ai's, ti's) ->
    (* using how codata types convert *)
    let self = head ti's in
    let ti's = tail ti's in
    let y = Ident.fresh () in
    μy.< conv self | dtor{(Convert.type ai)'s}((conv ti)'s)(y) > 



 μx.⟨t|μ̃y.⟨u|x⟩⟩