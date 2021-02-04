module Main

import Pruviloj
import Derive.Show
import Control.Catchable
import Control.Monad.Trans
import Control.Monad.Identity
import Control.Monad.Writer as Writer
import Data.Complex
import Data.SortedMap as SortedMap
-- import Scheme.Exception

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

LispErrors : Type
LispErrors = List LispError

data ViewCatchable : (im : Monad m, ic : Catchable m t) => m a -> Type where
  Thrown : (err : t) -> ViewCatchable @{im} @{ic} {m} {t} (throw {m} {a} err)
  Success : (x : a) -> ViewCatchable @{im} @{ic} {m} {t} (pure {f=m} {a} x)

data CatchCollect :
  (monadImplM : Monad m, catchableImplM : Catchable m t,
    monadImplN : Monad n, catchableImplN : Catchable n (List t)) =>
  {view : (arb : Type) -> (mx : m arb) -> ViewCatchable {m} {a=arb} mx} ->
  Type -> Type where
  MkCC : m (n a) -> CatchCollect
      @{monadImplM} @{catchableImplM}
      @{monadImplN} @{catchableImplN}
      {m} {n} {t} {view} a

squash :
  (monadImplM : Monad m, catchableImplM : Catchable m t,
    monadImplN : Monad n, catchableImplN : Catchable n (List t)) =>
  {mnx : m (n a)} -> ViewCatchable mnx -> n a
squash {n} {a} (Thrown err) = throw {m = n} {a} [err]
squash (Success nx) = nx

runCatchCollect :
  (monadImplM : Monad m, catchableImplM : Catchable m t,
    monadImplN : Monad n, catchableImplN : Catchable n (List t)) =>
  CatchCollect @{monadImplM} @{catchableImplM} @{monadImplN} @{catchableImplN} {view} a -> n a
runCatchCollect {view} (MkCC mx) = squash $ view (n a) mx

private
toNeverThrow :(monadImplM : Monad m, catchableImplM : Catchable m t,
  monadImplN : Monad n, catchableImplN : Catchable n (List t)) =>
  m (n a) -> m (n a)
toNeverThrow mmx = mmx `catch` \err => pure $ throw [err]

collect : (monadImplM : Monad m, catchableImplM : Catchable m t,
  monadImplN : Monad n, catchableImplN : Catchable n (List t)) =>
  m a -> CatchCollect @{monadImplM} @{catchableImplM} @{monadImplN} @{catchableImplN} {view} a
collect mx = MkCC $ toNeverThrow $ pure <$> mx

viewEither : (mx : Either t a) -> ViewCatchable mx
viewEither {t} (Left err) = Thrown {t} err
viewEither (Right x) = Success x

implementation Functor (CatchCollect @{monadImplM} @{catchableImplM} @{monadImplN} @{catchableImplN} {view}) where
  map f (MkCC mmx) = MkCC $ map (map f) mmx

implementation Applicative (CatchCollect @{monadImplM} @{catchableImplM} @{monadImplN} @{catchableImplN} {view}) where
  pure x = MkCC $ pure $ pure x
  (<*>) (MkCC mmfThrowable) (MkCC mmxThrowable) =
    let
      mmf = toNeverThrow mmfThrowable
      mmx = toNeverThrow mmxThrowable
    in MkCC (do
      mf <- mmf
      mx <- mmx
      pure (do
        f <- mf `catch` \errsF =>
          (map (errsF <+>) (catch (const neutral <$> mx) pure) >>= throw)
        x <- mx
        pure $ f x))

test : CatchCollect {m = Either String} {n = Either (List String)} Nat
test = (\x,y,z => sum [x,y,z])
  <$> collect (throw "err0")
  <*> collect (pure 12)
  <*> collect (throw "err2")

-- primitivesEnv :
--   (Monad m, Catchable (m LispVal) LispErrors) =>
--   SortedMap String (List LispVal -> m LispVal)
-- primitivesEnv = ?env
-- -- fromList
-- --   []

-- implementation Cast LispNumber ComplexD where
--   cast (LComplex x) = x
--   cast (LReal x) = x :+ 0
--   cast (LInteger x) = cast x :+ 0

-- lispNumToDouble :
--   (Monad m, Throwable LispErrors (m Double)) =>
--   LispNumber -> m Double
-- lispNumToDouble (LComplex (x :+ 0.0)) = pure x
-- lispNumToDouble x@(LComplex _) = throw [TypeMismatch "Real" (LNumber x)]
-- lispNumToDouble (LReal x) = pure x
-- lispNumToDouble (LInteger x) = pure $ cast x

-- lispNumToInteger :
--   (Monad m, Throwable LispErrors (m Integer)) =>
--   LispNumber -> m Integer
-- lispNumToInteger x@(LComplex _) = throw [TypeMismatch "Integer" (LNumber x)]
-- lispNumToInteger x@(LReal _) = throw [TypeMismatch "Integer" (LNumber x)]
-- lispNumToInteger (LInteger x) = pure x

-- namespace repl
--   apply : (Monad m, Throwable LispErrors (m LispVal)) => String -> List LispVal -> m LispVal
--   apply fname args with (SortedMap.lookup fname primitivesEnv)
--     | Nothing = throw $ the LispErrors [UnboundVar fname]
--     | Just f = f args

--   eval : (Monad m, Throwable LispErrors (m LispVal)) => LispVal -> m LispVal
--   eval (LList [LAtom "quote", ls]) = pure ls
--   eval (LList (LAtom func :: args)) = do
--     args' <- traverse (assert_total eval) args
--     apply func args'
--   eval val = pure val

-- main : IO ()
-- main = do
--   printLn $ runLispThrowable {m = Either LispErrors} $
--     the (LispThrowable LispVal) $ eval $
--       LList [LAtom "quote", LList [LString "aaa", LString "bbb"]]
--    -- do
--    --  x <- MkErrCollector ["error : 1"] "1" `catch` \errs => do
--    --    y <- throw ["error thrown"]
--    --    z <- MkErrCollector ["error : 2"] "2"
--    --    w <- throw (the (List String) errs)
--    --    pure $ y <+> z <+> w
--    --  pure $ x
