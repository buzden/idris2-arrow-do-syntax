module Syntax.ArrowDo

import Control.Arrow

import Language.Reflection

%default total

%language ElabReflection

namespace InputAsLambda

  data ArrowDo : (Type -> Type -> Type) -> Type -> Type

  (>>=) : ArrowDo arr a -> (a -> ArrowDo arr b) -> ArrowDo arr b

  (>>) : ArrowDo arr Unit -> ArrowDo arr b -> ArrowDo arr b

  prefix 0 <-=

  (<-=) : Arrow arr => a -> ArrowDo arr a

  infix 0 -<

  (-<) : arr a b -> a -> ArrowDo arr b

  -- A point where all parallel computations must be joined
  fence : ArrowDo arr Unit

  --- Usage examples ---

  -- I guess, we'll need `arr`, `a` and `b` be runtime arguments of macro-functions.
  -- Q: How to require ArrowChoice when needed?

  arrDoImpl : Arrow arr => TTImp -> Elab $ arr a b
  arrDoImpl expr = do
    logSugaredTerm "arrowdo" 0 "f" expr
    _ <- check {expected = a -> Syntax.ArrowDo.InputAsLambda.ArrowDo arr b} expr
    fail "Arrow-do syntax is not implemented yet"

  %macro
  arrDoQuoted : Arrow arr => TTImp -> Elab $ arr a b
  arrDoQuoted = arrDoImpl

  failing "not implemented yet"

    y : Arrow arr => arr Nat String -> arr String Bool -> arr Nat Bool
    y ns sb = arrDoQuoted {arr} `( \n => do
      s <- ns -< n + 1
      b <- sb -< s
      fence
      <-= b
    )

  %macro
  arrDoDirect : Arrow arr => (a -> ArrowDo arr b) -> Elab $ arr a b
  arrDoDirect f = arrDoImpl !(quote f)

  failing "not implemented yet"

    x : Arrow arr => arr Nat String -> arr String Bool -> arr Nat Bool
    x ns sb = arrDoDirect $ \n => do
      s <- ns -< n + 1
      b <- sb -< s
      fence
      <-= b

namespace InputAsFunction

  data ArrowDo : (Type -> Type -> Type) -> Type -> Type -> Type

  (>>=) : ArrowDo arr i a -> (a -> ArrowDo arr i b) -> ArrowDo arr i b

  (>>) : ArrowDo arr i Unit -> ArrowDo arr i b -> ArrowDo arr i b

  prefix 0 <-=

  (<-=) : Arrow arr => a -> ArrowDo arr i a

  infix 0 -<

  (-<) : arr a b -> a -> ArrowDo arr i b

  input : Arrow arr => ArrowDo arr i i

  -- A point where all parallel computations must be joined
  fence : ArrowDo arr i Unit

  --- Usage examples ---

  arrDoImpl : Arrow arr => TTImp -> Elab $ arr a b
  arrDoImpl expr = do
    logSugaredTerm "arrowdo" 0 "f" expr
    fail "Arrow-do syntax is not implemented yet"

  %macro
  arrDoDirect : Arrow arr => ArrowDo arr a b -> Elab $ arr a b
  arrDoDirect f = arrDoImpl !(quote f)

  failing "not implemented yet"

    x : Arrow arr => arr Nat String -> arr String Bool -> arr Nat Bool
    x ns sb = arrDoDirect $ do
      n <- input
      s <- ns -< n + 1
      b <- sb -< s
      fence
      <-= b
