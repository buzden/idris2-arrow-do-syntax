module Syntax.ArrowDo

import Control.Arrow

import Language.Reflection

%default total

data ArrowDo : (Type -> Type -> Type) -> Type -> Type

(>>=) : ArrowDo arr a -> (a -> ArrowDo arr b) -> ArrowDo arr b

(>>) : ArrowDo arr Unit -> ArrowDo arr b -> ArrowDo arr b

pure : Arrow arr => a -> ArrowDo arr a

infix 0 -<

(-<) : arr a b -> a -> ArrowDo arr b

-- A point where all parallel computations must be joined
fence : ArrowDo arr Unit

--- Usage examples ---

-- I guess, we'll need `arr`, `a` and `b` be runtime arguments of macro-functions.
-- Q: How to require ArrowChoice when needed?

%language ElabReflection

%macro
arrDoDirect : Arrow arr => (a -> ArrowDo arr b) -> Elab $ arr a b
arrDoDirect f = do
  logSugaredTerm "arrowdo" 0 "f" !(quote f)
  fail "Arrow-do syntax is not implemented yet"

failing "not implemented yet"

  x : Arrow arr => arr Nat String -> arr String Bool -> arr Nat Bool
  x ns sb = arrDoDirect $ \n => do
    s <- ns -< n + 1
    b <- sb -< s
    fence
    pure b

%macro
arrDoQuoted : Arrow arr => TTImp -> Elab $ arr a b
arrDoQuoted expr = do
  logSugaredTerm "arrowdo" 0 "f" expr
  fail "Arrow-do syntax is not implemented yet"

failing "not implemented yet"

  y : Arrow arr => arr Nat String -> arr String Bool -> arr Nat Bool
  y ns sb = arrDoQuoted {arr} `( \n => do
    s <- ns -< n + 1
    b <- sb -< s
    fence
    pure b
  )
