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

||| Number Type for LispVal
data LispNumber
  = LComplex (ComplexD)
  | LReal Double
  | LInteger Integer

%runElab deriveShow `{LispNumber}

data LispVal
  = LAtom String
  | LList (List LispVal)
  | LDottedList (List LispVal) LispVal
  | LNumber LispNumber
  | LString String
  | LBool Bool

implementation Eq LispVal where
  (==) (LList []) (LList []) = True
  (==) _ _ = False

showLispVal : LispVal -> String
showLispVal (LAtom atm) = atm
showLispVal (LList ls) = "(" <+> unwords (assert_total showLispVal <$> ls) <+> ")"
showLispVal (LDottedList ls x) =
  "(" <+> unwords (assert_total showLispVal <$> ls) <+> assert_total (showLispVal x) <+> ")"
showLispVal (LNumber num) = show num
showLispVal (LString str) = "\"" <+> str <+> "\""
showLispVal (LBool True) = "#t"
showLispVal (LBool False) = "#f"

implementation Show LispVal where
  show = showLispVal

implementation Semigroup LispVal where
  (<+>) x y = LList $ toList x <+> toList y
    where
      toList : LispVal -> List LispVal
      toList (LList ls) = ls
      toList val = [val]

implementation Monoid LispVal where
  neutral = LList []

data LispError' lisp
  = NumArgs Ordering Nat (List lisp)
  | TypeMismatch String lisp
  | BadSpecialForm String lisp
  | UnboundVar String
  | Default String

%runElab deriveShow `{Ordering}
%runElab deriveShow `{LispError'}

LispError : Type
LispError = LispError' LispVal

primitivesEnv :
  SortedMap String ((Monad m, Catchable m LispError) => List LispVal -> m LispVal)
primitivesEnv = ?env
-- fromList
--   []

implementation Cast LispNumber ComplexD where
  cast (LComplex x) = x
  cast (LReal x) = x :+ 0
  cast (LInteger x) = cast x :+ 0

lispNumToDouble :
  (Monad m, Catchable m LispError) =>
  LispNumber -> m Double
lispNumToDouble (LComplex (x :+ 0.0)) = pure x
lispNumToDouble x@(LComplex _) = throw $ TypeMismatch "Real" (LNumber x)
lispNumToDouble (LReal x) = pure x
lispNumToDouble (LInteger x) = pure $ cast x

lispNumToInteger :
  (Monad m, Catchable m LispError) =>
  LispNumber -> m Integer
lispNumToInteger x@(LComplex _) = throw $ TypeMismatch "Integer" (LNumber x)
lispNumToInteger x@(LReal _) = throw $ TypeMismatch "Integer" (LNumber x)
lispNumToInteger (LInteger x) = pure x

namespace repl
  apply : (Monad m, Catchable m LispError) => String -> List LispVal -> m LispVal
  apply {m} fname args with (SortedMap.lookup fname (primitivesEnv {m}))
    | Nothing = throw $ UnboundVar fname
    | Just f = f args

  eval : (Monad m, Catchable m LispError) => LispVal -> m LispVal
  eval (LList [LAtom "quote", ls]) = pure ls
  eval (LList (LAtom func :: args)) = do
    args' <- traverse (assert_total eval) args
    apply func args'
  eval val = pure val

main : IO ()
main = do
  printLn $
    the (Either LispError LispVal) $ eval $
      LList [LAtom "quote", LList [LString "aaa", LString "bbb"]]
   -- do
   --  x <- MkErrCollector ["error : 1"] "1" `catch` \errs => do
   --    y <- throw ["error thrown"]
   --    z <- MkErrCollector ["error : 2"] "2"
   --    w <- throw (the (List String) errs)
   --    pure $ y <+> z <+> w
   --  pure $ x
