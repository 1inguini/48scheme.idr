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

data CatchCollect : -- {c : Type -> Type -> Type} ->
  (monadImplM : Monad m, catchableImplM : Catchable m t,
    monadImplN : Monad n, catchableImplN : Catchable n (List t)) =>
  -- (t : Type) ->
  -- {auto monadImpl : {a : Type} -> Monad (c a)} ->
  -- {auto catchableImpl : {a : Type} -> Catchable (c a) a} ->
  -- {squash : c t (c (List t) a) -> c (List t) a} ->
  (a : Type) -> Type where
  MkCC : m (n a) -> CatchCollect @{monadImplM} @{catchableImplM} @{monadImplN} @{catchableImplN} {m} {n} {t} a

-- runCatchCollect :
--   {c : Ty2} ->
--   (Monad (c t), Catchable (c t) t, Monad (c (List t)), Catchable (c (List t)) (List t)) =>
--   CatchCollect c t a -> c (List t) a
-- runCatchCollect (MkCC mx) = mx

-- private
-- toNeverThrow :
--   {c : Ty2} ->
--   (Monad (c t), Catchable (c t) t, Monad (c (List t)), Catchable (c (List t)) (List t)) =>
--   c t (c (List t) a) -> c t (c (List t) a)
-- toNeverThrow mmx = mmx `catch` \err => pure $ throw [err]

collect : (monadImplM : Monad m, catchableImplM : Catchable m t,
  monadImplN : Monad n, catchableImplN : Catchable n (List t)) =>
  m a -> CatchCollect @{monadImplM} @{catchableImplM} @{monadImplN} @{catchableImplN} a
collect mx = MkCC $ pure <$> mx

data ViewCatchable : (im : Monad m, ic : Catchable m t) => m a -> Type where
  Thrown : (err : t) -> ViewCatchable @{im} @{ic} {m} {t} (throw {m} {a} err)
  Success : (x : a) -> ViewCatchable @{im} @{ic} {m} {t} (pure {f=m} {a} x)

viewEither : (mx : Either t a) -> ViewCatchable mx
viewEither {t} (Left err) = Thrown {t} err
viewEither (Right x) = Success x

squash : {c : Type -> Type -> Type} -> {t : Type} -> {a : Type} ->
  ({t : Type} -> Monad (c t), {t : Type} -> Catchable (c t) t) =>
  {mx : c t (c (List t) a)} -> ViewCatchable mx -> c (List t) a
squash {c} {t} {a} (Thrown err) = throw {m = c (List t)} {a} [err]
squash (Success mx) = mx


-- implementation Functor (CatchCollect c t {monadImpl} {catchableImpl}) where
--   map f (MkCC mmx) = MkCC $ map (map f) mmx

-- implementation
--   (Monad (c t), Catchable (c t) t, Monad (c (List t)), Catchable (c (List t)) (List t)) =>
--   Applicative (CatchCollect c t) where
--   pure x = MkCC $ pure $ pure x
--   (<*>) (MkCC mmfThrowable) (MkCC mmxThrowable) =
--     let
--       mmf = toNeverThrow mmfThrowable
--       mmx = toNeverThrow mmxThrowable
--     in MkCC (do
--       mf <- mmf
--       mx <- mmx
--       pure (do
--         f <- mf `catch` \errsF =>
--           (map (errsF <+>) (catch (const neutral <$> mx) pure) >>= throw)
--         x <- mx
--         pure $ f x))

-- test : {runner : runnerTy (Either String) String Nat} -> CatchCollect runner Nat
-- test = (\x,y,z => sum [x,y,z])
--   <$> collect (pure 11)
--   <*> collect (pure 12)
--   <*> collect (pure 13)

-- private
-- Ty2 : Type
-- Ty2 = Type -> Type -> Type

-- record CatchCollect (c : Ty2) (t : Type) (a : Type) where
--   constructor MkCC
--   unCC :
--     (Monad (c t), Catchable (c t) t, Monad (c (List t)), Catchable (c (List t)) (List t)) =>
--     c t (c (List t) a)

-- -- runCatchCollect :
-- --   {c : Ty2} ->
-- --   (Monad (c t), Catchable (c t) t, Monad (c (List t)), Catchable (c (List t)) (List t)) =>
-- --   CatchCollect c t a -> c (List t) a
-- -- runCatchCollect (MkCC mx) = mx

-- private
-- toNeverThrow :
--   {c : Ty2} ->
--   (Monad (c t), Catchable (c t) t, Monad (c (List t)), Catchable (c (List t)) (List t)) =>
--   c t (c (List t) a) -> c t (c (List t) a)
-- toNeverThrow mmx = mmx `catch` \err => pure $ throw [err]

-- collect :
--   {c : Ty2} ->
--   (Monad (c a), Catchable (c t) t, Monad (c (List t)), Catchable (c (List t)) (List t)) =>
--   c t a -> CatchCollect c t a
-- collect mx = MkCC $ toNeverThrow $ pure <$> mx

-- implementation
--   (Monad (c e), Catchable (c t) t, Monad (c (List t)), Catchable (c (List t)) (List t)) =>
--   Functor (CatchCollect c t) where
--   map f (MkCC mmx) = MkCC $ map (map f) mmx

-- implementation
--   (Monad (c t), Catchable (c t) t, Monad (c (List t)), Catchable (c (List t)) (List t)) =>
--   Applicative (CatchCollect c t) where
--   pure x = MkCC $ pure $ pure x
--   (<*>) (MkCC mmfThrowable) (MkCC mmxThrowable) =
--     let
--       mmf = toNeverThrow mmfThrowable
--       mmx = toNeverThrow mmxThrowable
--     in MkCC (do
--       mf <- mmf
--       mx <- mmx
--       pure (do
--         f <- mf `catch` \errsF =>
--           (map (errsF <+>) (catch (const neutral <$> mx) pure) >>= throw)
--         x <- mx
--         pure $ f x))

-- data CatchCollect : (m : Type -> Type) -> (a : Type) -> Type where
--   MkCC : (Monad m, Catchable m (List t)) => m a -> CatchCollect m a

-- implementation (Monad m, Catchable m (List t)) => Functor (CatchCollect m) where
--   map f (MkCC mx) = MkCC $ map f mx

-- implementation (Monad m, Catchable m (List t)) => Applicative (CatchCollect m) where
--   pure x = MkCC $ pure x
--   (<*>) (MkCC mf) (MkCC mx) = MkCC $ do
--     f <- mf `catch` \errsF => do
--       _x <- mx `catch` \errsX =>
--         throw $ errsF <+> errsX
--       throw errsF
--     x <- mx
--     pure $ f x

-- implementation (Monad m, Catchable m (List t)) => Catchable (CatchCollect m) (List t) where
--   throw errs = MkCC $ throw errs
--   catch (MkCC mx) f = MkCC $ mx `catch` \errs =>
--     case f errs of MkCC my => my

-- data CatchCollect : (e : Type) -> (a : Type) -> Type where
--   CCThrow : a -> e -> CatchCollect e a
--   CCWriter : WriterT (List e) Identity a -> CatchCollect e a

-- implementation Functor (CatchCollect e) where
--   map f (CCThrow x err) = CCThrow (f x) err
--   map f (CCWriter mx) = CCWriter $ map f mx

-- implementation Applicative (CatchCollect e) where
--   pure x = CCWriter $ pure x
--   (<*>) (CCThrow f errOfF) (CCThrow x errOfX) = CCWriter $ tell [errOfF,errOfX] *> pure (f x)
--   (<*>) (CCThrow f errOfF) (CCWriter mx) = CCWriter $ tell [errOfF] *> map f mx
--   (<*>) (CCWriter mf) (CCThrow x errOfX) = CCWriter $ do
--     f <- mf
--     tell [errOfX]
--     pure $ f x
--   (<*>) (CCWriter mf) (CCWriter mx) = CCWriter $ mf <*> mx

-- implementation Monad (CatchCollect e) where
--   (>>=) (CCThrow x errOfX) f with (f x)
--     | (CCThrow y errOfY) = CCWriter $ tell [errOfX, errOfY] *> pure y
--     | (CCWriter my) = CCWriter $ tell [errOfX] *> my
--   (>>=) (CCWriter mx) f with (runWriter mx)
--     | (x, errsOfX) with (f x)
--       | (CCThrow y errOfY) = CCWriter $ tell (errsOfX <+> [errOfY]) *> pure y
--       | (CCWriter my) = CCWriter $ tell errsOfX *> my

-- runLispThrowable :
--   (Monad m, Catchable (m a) LispErrors) =>
--   LispThrowable a -> m a
-- runLispThrowable writer with (runWriter writer)
--   | (x, [])  = pure x
--   | (_, errs) = throw errs

-- implementation Monoid a => Catchable LispThrowable LispErrors where
--   throw errs = tell errs *> pure neutral
--   catch writer f with (runWriter writer)
--     | (x, []) = pure x
--     | (_, err) = f err

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
