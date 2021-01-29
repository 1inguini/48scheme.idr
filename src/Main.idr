module Main

import Data.Complex
import Scheme.Exception

%default total

ComplexD : Type
ComplexD = Complex Double

||| Number Type for LispVal
data LispNumber
  = Complex (ComplexD)
  | Real Double
  | Integer Integer

data LispVal
  = Atom String
  | List (List LispVal)
  | DottedList (List LispVal) LispVal
  | Number LispNumber
  | String String
  | Bool Bool

data LispError
  = NumArgs Ordering Nat (List LispVal)
  | TypeMismatch String LispVal
  | BadSpecialForm String LispVal
  | UnboundVar String
  | Default String

record ErrCollector e a where
  constructor MkErrCollector
  errors : Monoid e => e
  result : a

runErrCollector : (Monoid e, Eq e, Monad m, Throwable e (m a)) =>  ErrCollector e a -> m a
runErrCollector (MkErrCollector errs x) with (neutral == errs) 
  | True = pure x
  | False = throw errs

implementation (Monoid e, Show e, Show a) => Show (ErrCollector e a) where
  show (MkErrCollector errs res) = "MkErrCollector " <+> show errs <+> " " <+> show res

implementation Functor (ErrCollector e) where
  map f (MkErrCollector errs x) = MkErrCollector errs $ f x

implementation Monoid e => Applicative (ErrCollector e) where
  pure x = MkErrCollector neutral x
  (<*>) (MkErrCollector errs0 f) (MkErrCollector errs1 x) =
    MkErrCollector (errs0 <+> errs1) $ f x

implementation Monoid e => Monad (ErrCollector e) where
  (>>=) (MkErrCollector errs x) f = record { errors $= (errs <+>) } $ f x

implementation (Monoid e, Monoid a) => Throwable e (ErrCollector e a) where
  throw err = MkErrCollector err neutral

implementation (Eq e, Monoid e, Monoid a) => Catchable e (ErrCollector e a) where
  catch (MkErrCollector err x) f with (neutral == err) 
    | True = MkErrCollector err x
    | False = f err

main : IO ()
main = do
  printLn $ the (Either (List String) String) $ runErrCollector $ do
    x <- MkErrCollector ["error : 1"] "1" `catch` \errs => do
      y <- throw ["error thrown"]
      z <- MkErrCollector ["error : 2"] "2"
      w <- throw (the (List String) errs)
      pure $ y <+> z <+> w
    pure $ x
