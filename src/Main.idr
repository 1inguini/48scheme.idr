module Main

import Pruviloj
import Derive.Show
import Data.Complex
import Data.SortedMap as SortedMap
import Scheme.Exception

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

data LispError lisp
  = NumArgs Ordering Nat (List lisp)
  | TypeMismatch String lisp
  | BadSpecialForm String lisp
  | UnboundVar String
  | Default String

%runElab deriveShow `{Ordering}
%runElab deriveShow `{LispError}

LispErrors : Type
LispErrors = List $ LispError LispVal

record ErrCollector e a where
  constructor MkErrCollector
  errors : List e
  result : a

LispErrCollector : Type -> Type
LispErrCollector = ErrCollector (LispError LispVal)

runErrCollector : (Monad m, Throwable (List e) (m a)) =>  ErrCollector e a -> m a
runErrCollector (MkErrCollector [] x) = pure x
runErrCollector (MkErrCollector errs _) = throw errs

implementation (Monoid e, Show e, Show a) => Show (ErrCollector e a) where
  show (MkErrCollector errs res) = "MkErrCollector " <+> show errs <+> " " <+> show res

implementation Functor (ErrCollector e) where
  map f (MkErrCollector errs x) = MkErrCollector errs $ f x

implementation Applicative (ErrCollector e) where
  pure x = MkErrCollector neutral x
  (<*>) (MkErrCollector errs0 f) (MkErrCollector errs1 x) =
    MkErrCollector (errs0 <+> errs1) $ f x

implementation Monad (ErrCollector e) where
  (>>=) (MkErrCollector errs x) f = record { errors $= (errs <+>) } $ f x

implementation Monoid a => Throwable (List e) (ErrCollector e a) where
  throw errs = MkErrCollector errs neutral

implementation Monoid a => Catchable (List e) (ErrCollector e a) where
  catch (MkErrCollector err x) f = f err
  catch (MkErrCollector [] x) f = MkErrCollector [] x

primitivesEnv :
  (Monad m, Throwable LispErrors (m LispVal)) => 
  SortedMap String (List LispVal -> m LispVal)
primitivesEnv = ?env
-- fromList $
--   []

apply : (Monad m, Throwable LispErrors (m LispVal)) => String -> List LispVal -> m LispVal
apply fname args with (SortedMap.lookup fname primitivesEnv)
  | Nothing = throw $ the LispErrors [UnboundVar fname]
  | Just f = f args
  
eval : (Monad m, Throwable LispErrors (m LispVal)) => LispVal -> m LispVal
eval (LList [LAtom "quote", ls]) = pure ls
eval (LList (LAtom func :: args)) = do
  args' <- traverse (assert_total eval) args
  apply func args'
eval val = pure val

main : IO ()
main = do
  printLn $ the (Either LispErrors LispVal) $ runErrCollector $
    eval {m = LispErrCollector} $
      LList [LAtom "quote", LList [LString "aaa", LString "bbb"]]
   -- do
   --  x <- MkErrCollector ["error : 1"] "1" `catch` \errs => do
   --    y <- throw ["error thrown"]
   --    z <- MkErrCollector ["error : 2"] "2"
   --    w <- throw (the (List String) errs)
   --    pure $ y <+> z <+> w
   --  pure $ x
