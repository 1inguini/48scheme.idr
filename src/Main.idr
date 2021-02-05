module Main

import Pruviloj
import Control.Catchable
import Derive.Show
import Data.Complex
import Data.SortedMap as SortedMap
-- import Scheme.Exception
import Scheme.CatchCollect

%default total
%language ElabReflection

ComplexD : Type
ComplexD = Complex Double

namespace Lisp
  ||| Number Type for LispVal
  data LispNumber
    = Complex (ComplexD)
    | Real Double
    | Integer Integer

  %runElab deriveShow `{LispNumber}

  data LispVal
    = Atom String
    | List (List LispVal)
    | DottedList (List LispVal) LispVal
    | Number LispNumber
    | String String
    | Bool Bool

  implementation Eq LispVal where
    (==) (Lisp.List []) (Lisp.List []) = True
    (==) _ _ = False

  showLispVal : LispVal -> String
  showLispVal (Lisp.Atom atm) = atm
  showLispVal (Lisp.List ls) = "(" <+> unwords (assert_total showLispVal <$> ls) <+> ")"
  showLispVal (Lisp.DottedList ls x) =
    "(" <+> unwords (assert_total showLispVal <$> ls) <+> assert_total (showLispVal x) <+> ")"
  showLispVal (Lisp.Number num) = show num
  showLispVal (Lisp.String str) = "\"" <+> str <+> "\""
  showLispVal (Lisp.Bool True) = "#t"
  showLispVal (Lisp.Bool False) = "#f"

  implementation Show LispVal where
    show = showLispVal

  implementation Semigroup LispVal where
    (<+>) x y = Lisp.List $ toList x <+> toList y
      where
        toList : LispVal -> List LispVal
        toList (Lisp.List ls) = ls
        toList val = [val]

  implementation Monoid LispVal where
    neutral = Lisp.List []

  data LispError' lisp
    = NumArgs Ordering Nat (List lisp)
    | TypeMismatch String lisp
    | BadSpecialForm String lisp
    | UnboundVar String
    | Default String

  LispError : Type
  LispError = LispError' LispVal

  quote : LispVal -> LispVal
  quote ls = Lisp.List [Lisp.Atom "quote", ls]
  
  integer : Integer -> LispVal
  integer = Lisp.Number . Lisp.Integer

%runElab deriveShow `{Ordering}
%runElab deriveShow `{LispError'}

primitivesEnv :
  SortedMap String 
    ({m:Type -> Type} -> (Monad m, Catchable m LispError) => List LispVal -> m LispVal)
primitivesEnv = ?env
-- fromList
--   []

implementation Cast LispNumber ComplexD where
  cast (Lisp.Complex x) = x
  cast (Lisp.Real x) = x :+ 0
  cast (Lisp.Integer x) = cast x :+ 0

lispNumToDouble :
  (Monad m, Catchable m LispError) =>
  LispNumber -> m Double
lispNumToDouble (Lisp.Complex (x :+ 0.0)) = pure x
lispNumToDouble x@(Lisp.Complex _) = throw $ TypeMismatch "Real" (Lisp.Number x)
lispNumToDouble (Lisp.Real x) = pure x
lispNumToDouble (Lisp.Integer x) = pure $ cast x

lispNumToInteger :
  (Monad m, Catchable m LispError) =>
  LispNumber -> m Integer
lispNumToInteger x@(Lisp.Complex _) = throw $ TypeMismatch "Integer" (Lisp.Number x)
lispNumToInteger x@(Lisp.Real _) = throw $ TypeMismatch "Integer" (Lisp.Number x)
lispNumToInteger (Lisp.Integer x) = pure x

namespace repl
  apply : (Monad m, Catchable m LispError) => String -> List LispVal -> m LispVal
  apply {m} fname args with (SortedMap.lookup fname (primitivesEnv))
    | Nothing = throw $ UnboundVar fname
    | Just f = f args

  eval : (Monad m, Catchable m LispError) => LispVal -> m LispVal
  eval (Lisp.List [Lisp.Atom "quote", ls]) = pure ls
  eval (Lisp.List (Lisp.Atom func :: args)) = do
    args' <- traverse (assert_total eval) args
    apply func args'
  eval val = pure val

-- test : List $ CatchCollect {m = Either LispError} {n = Either (ls: List LispError ** NonEmpty ls)} LispVal
-- test = eval <$> 
--   [ Lisp.quote $ Lisp.List [Lisp.String "aaa", Lisp.String "bbb"]
--   , Lisp.List [Lisp.Atom "+", Lisp.List [Lisp.String "aaa", Lisp.String "bbb"]] ]

main : IO ()
main = ?main

   -- do
   --  x <- MkErrCollector ["error : 1"] "1" `catch` \errs => do
   --    y <- throw ["error thrown"]
   --    z <- MkErrCollector ["error : 2"] "2"
   --    w <- throw (the (List String) errs)
   --    pure $ y <+> z <+> w
   --  pure $ x
