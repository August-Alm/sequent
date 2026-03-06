module AARCH64.Limited

import Types

import Data.Fin
import Data.Vect


public export
data Import : Arguments d -> Signature d -> Type where
  Restart : Import [] []
  Return : Import [Ext "Int"] []
  Literal : Integer -> Import [] [[Ext "Int"]]
  Add : Import [Ext "Int", Ext "Int"] [[Ext "Int"]]
  Mul : Import [Ext "Int", Ext "Int"] [[Ext "Int"]]
  Rem : Import [Ext "Int", Ext "Int"] [[Ext "Int"]]
  IfZero : Import [Ext "Int"] [[], []]
  IfEqual : Import [Ext "Int", Ext "Int"] [[], []]
  IfLess : Import [Ext "Int", Ext "Int"] [[], []]

public export
Tag : Signature d -> Arguments d -> Type
Tag ts us = Symbol ts us

public export
Substitution : Arguments d -> Arguments d -> Type
Substitution as bs = Table (Symbol as) bs

mutual
  public export
  data Statement : Vect d (Signature d) -> List (Arguments d) -> List (Tpe d) -> Type where
    Substitute : {as : Arguments d} -> {bs : Arguments d} -> Substitution as bs -> Statement ts ps bs -> Statement ts ps as
    Jump : Symbol ps as -> Statement ts ps as
    Let : {t : Fin d} -> {as : Arguments d} -> {bs : Arguments d} -> Tag (index t ts) bs -> Statement ts ps (Pro t :: as) -> Statement ts ps (bs ++ as)
    Switch : {t : Fin d} -> {as : Arguments d} -> Clauses ts ps as (index t ts) -> Statement ts ps (Pro t :: as)
    New : {t : Fin d} -> {as : Arguments d} -> {bs : Arguments d} -> Methods ts ps bs (index t ts) -> Statement ts ps (Con t :: as) -> Statement ts ps (bs ++ as)
    Invoke : {t : Fin d} -> {as : Arguments d} -> Tag (index t ts) as -> Statement ts ps (Con t :: as)
    Extern : {as : Arguments d} -> {bs : Arguments d} -> {qs : Signature d} -> Import bs qs -> Substitution as bs -> Clauses ts ps as qs -> Statement ts ps as

  public export
  Clause : (ts : Vect d (Signature d)) -> List (Arguments d) -> Arguments d -> Arguments d -> Type
  Clause ts ps as cs = Statement ts ps (cs ++ as)

  public export
  Method : (ts : Vect d (Signature d)) -> List (Arguments d) -> Arguments d -> Arguments d -> Type
  Method ts ps as cs = Statement ts ps (as ++ cs)

  public export
  Clauses : (ts : Vect d (Signature d)) -> List (Arguments d) -> Arguments d -> Signature d -> Type
  Clauses ts ps as us = Table (Clause ts ps as) us

  public export
  Methods : (ts : Vect d (Signature d)) -> List (Arguments d) -> Arguments d -> Signature d -> Type
  Methods ts ps as us = Table (Method ts ps as) us


public export
Program : (ts : Vect d (Signature d)) -> List (Arguments d) -> Type
Program ts ps = Table (Statement ts ps) ps

