module CatchCollect

import Control.Catchable
import Control.Monad.Trans
import Control.Monad.Identity
import Control.Monad.Writer as Writer

%default total

public export
data Result : {m : Type -> Type} -> {t : Type} -> m a -> Type where
  Failure : Catchable m t => Result {m} {t} {a} (throw {m} {t} {a} err)
  Success : Applicative m => Result {m} (pure {f=m} x)

public export
interface (Applicative m, Catchable m t) =>
  Successable (m : Type -> Type) (t : Type) where
    result : (mx : m a) -> Result {m} {t} mx
    throwIsFail : result (throw {a} err) = Failure {m} {t} {err} {a}
    pureIsSuccess : {x : a} -> result (pure x) = Success {m} {x}

public export
implementation Successable (Either t) t where
  result (Left err) = Failure
  result (Right x) = Success
  throwIsFail = Refl
  pureIsSuccess = Refl

public export
data IsSuccess : {m : Type -> Type} -> {t : Type} -> {mx : m a} -> Result {m} {t} mx -> Type where
  ItIsSuccess : Applicative m => IsSuccess {m} (Success {m})

runIsSuccess : Successable m t => (mx : m a) -> {rx : Result {m} {t} mx} -> IsSuccess rx -> a
runIsSuccess {m} (pure x) {rx=Success {m}} ItIsSuccess = x

export
data CatchCollect : (t : Type) -> (a : Type) -> Type where
  MkCC : List t -> a -> CatchCollect t a

-- EitherCollect : Type -> Type -> Type
-- EitherCollect t a = CatchCollect a {t} {m = Either (ts : List t ** NonEmpty ts)}

export
runCatchCollect : (Monad m, Successable m (List t)) =>
  CatchCollect t a -> m a
runCatchCollect (MkCC [] x) = pure x
runCatchCollect (MkCC errs _) = throw errs

private
getInternal : CatchCollect t a -> a
getInternal (MkCC _ x) = x

private
getErrors : CatchCollect t a -> List t
getErrors (MkCC errs _) = errs

-- private
-- cram : (Successable f t, Successable m (ts : List t ** NonEmpty ts)) =>
--   f (m a) -> m a
-- cram {f} {t} fmx with (result {m=f} {t} fmx)
--   cram {f} {t} (throw err) | Failure {f} =
--     runIsSuccess {f} {t} (pure {f} $ throw {m} ([err] ** IsNonEmpty)) ItIsSuccess
--   cram {f} (pure fx) | Success {f} = fx

public export
implementation Functor (CatchCollect t) where
  map f (MkCC errs x) = MkCC errs $ f x

public export
implementation Applicative (CatchCollect t) where
  pure x = MkCC [] x
  (<*>) (MkCC errsF f) (MkCC errsX x) =
    MkCC (errsF <+> errsX) (f x)

public export
implementation Monad (CatchCollect t) where
  (>>=) (MkCC errsX x) f =
    let
      MkCC errsY y = f x
    in MkCC (errsX <+> errsY) y

export
collect : Successable m t => a -> m a -> CatchCollect t a
collect fallback mx with (result {t} mx)
  collect {t} fallback (throw err) | Failure {t} = MkCC [err] fallback
  collect {m} _        (pure  x)   | Success {m} = MkCC [] x

export
collectMonoid : (Successable m t, Monoid a) => m a -> CatchCollect t a
collectMonoid = collect neutral

export
collectCatch : CatchCollect t a -> (List t -> CatchCollect t a) -> CatchCollect t a
collectCatch (MkCC []   x) _ = pure x
collectCatch (MkCC errs _) f = f errs

export
or : CatchCollect t a -> CatchCollect t a -> CatchCollect t a
or ccx ccy = ccx `collectCatch` const ccy

export
collectThrow : a -> t -> CatchCollect t a
collectThrow fallback = collect fallback . Left

export
collectThrowMonoid : Monoid a => t -> CatchCollect t a
collectThrowMonoid = collectThrow neutral

-- private
-- test : CatchCollect {m = Either String} {n = Either (ls : List String ** NonEmpty ls)} Nat
-- test = (\x,y,z => sum [x,y,z])
--   <$> collect (throw "err0")
--   <*> collect (pure 12)
--   <*> collect (throw "err2")

-- private
-- test : CatchCollect Nat
--   {t = String}
--   {m = Either String}
--   {n = Either (ls : List String ** NonEmpty ls)}
-- test =
--   [|
--     (\x,y,z => sum [x,y,z])
--     (collect 0 (throw "err0"))
--     (collect 0 (pure 12))
--     (collect 0 (throw "err2"))
--   |]

private
test : CatchCollect String Nat
test = do
  x <- collect 0 (Left "err0")
  y <- collect 0 (Right 12)
  z <- collect 0 (Left $ show x <+> show y)
  pure $ sum [x,y,z]
