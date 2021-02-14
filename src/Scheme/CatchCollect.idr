module CatchCollect

import Control.Catchable
import Control.Monad.Trans
import Control.Monad.Identity
import Control.Monad.Writer as Writer

%default total

public export
data Result : {f : Type -> Type} -> {t : Type} -> f a -> Type where
  Failure : Catchable f t => Result {f} {t} {a} (throw {m=f} {t} {a} err)
  Success : Applicative f => Result {f} (pure {f} x)

public export
interface (Applicative m, Catchable m t) =>
  Successable (m : Type -> Type) (t : Type) where
    result : (mx : m a) -> Result {f=m} {t} mx
    throwIsFail : result (throw {a} err) = Failure {f=m} {t} {err} {a}
    pureIsSuccess : {x : a} -> result (pure x) = Success {f=m} {x}

public export
implementation Successable (Either t) t where
  result (Left err) = Failure
  result (Right x) = Success
  throwIsFail = Refl
  pureIsSuccess = Refl

public export
data IsSuccess : {f : Type -> Type} -> {t : Type} -> {fx : f a} -> Result {f} {t} fx -> Type where
  ItIsSuccess : Applicative f => IsSuccess {f} (Success {f})

runIsSuccess : Successable f t => (fx : f a) -> {rx : Result {f} {t} fx} -> IsSuccess rx -> a
runIsSuccess {f} (pure x) {rx=Success {f=f}} ItIsSuccess = x

export
data CatchCollect : (Monad m, Successable m (ts : List t ** NonEmpty ts)) =>
  (a : Type) -> Type where
  MkCC : (Monad m, Successable m (ts : List t ** NonEmpty ts)) =>
    (fallback : a) -> (body : m a) -> CatchCollect {m} {t} a

EitherCollect : Type -> Type -> Type
EitherCollect t a = CatchCollect a {t} {m = Either (ts : List t ** NonEmpty ts)}

export
runCatchCollect : (Monad m, Successable m (ts : List t ** NonEmpty ts)) =>
  CatchCollect {m} {t} a -> m a
runCatchCollect (MkCC _ mx) = mx

getFallback : (Monad m, Successable m (ts : List t ** NonEmpty ts)) =>
  CatchCollect {m} {t} a -> a
getFallback (MkCC fallback _) = fallback

private
cram : (Successable f t, Successable m (ts : List t ** NonEmpty ts)) =>
  f (m a) -> m a
cram {f} {t} fmx with (result {m=f} {t} fmx)
  cram {f} {t} (throw err) | Failure {f} =
    runIsSuccess {f} {t} (pure {f} $ throw {m} ([err] ** IsNonEmpty)) ItIsSuccess
  cram {f} (pure fx) | Success {f} = fx

public export
implementation Functor (CatchCollect @{siN} @{miN}) where
  map f (MkCC fallback mx) = MkCC (f fallback) $ map f mx

public export
implementation Applicative (CatchCollect @{siN} @{miN}) where
  pure x = MkCC x $ pure x
  (<*>) (MkCC fallbackF mf) (MkCC fallbackX mx) =
    MkCC (fallbackF fallbackX) (do
      f <- catch {t = (ts : List t ** NonEmpty ts)} mf $ \(errF :: errsF ** _) => (do
        errs <- (const errsF <$> mx) `catch` \(errs ** _) => pure $ errsF <+> errs
        throw (errF :: errs ** the (NonEmpty (errF :: errs)) IsNonEmpty))
      x <- mx
      pure $ f x)

public export
implementation Monad (CatchCollect @{siN} @{miN}) where
  (>>=) {t} (MkCC fallbackX mx) f =
    MkCC (getFallback $ f fallbackX) (do
      x <- catch {t = (ts : List t ** NonEmpty ts)} mx $ \(errX :: errsX ** _) => (do
        errs <- (const errsX <$> runCatchCollect (f fallbackX)) `catch` \(errsY ** _) =>
                          pure $ errsX <+> errsY
        throw (errX :: errs ** the (NonEmpty (errX :: errs)) IsNonEmpty))
      runCatchCollect $ f x)

export
collect : (Successable f t, Monad m, Successable m (ts : List t ** NonEmpty ts)) =>
  a -> f a -> CatchCollect {m} {t} a
collect fallback fx = MkCC fallback $ cram $ map pure fx

export
collectMonoid : (Successable f t, Monad m, Successable m (ts : List t ** NonEmpty ts)) =>
  Monoid a => f a -> CatchCollect {m} {t} a
collectMonoid = collect neutral

export
collectCatch : (Monad m, Successable m (ts : List t ** NonEmpty ts)) =>
  CatchCollect {m} {t} a -> ((ts : List t ** NonEmpty ts) -> CatchCollect {m} {t} a) ->
  CatchCollect {m} {t} a
collectCatch {t} (MkCC _ mx) f with (result {m} {t = (ts : List t ** NonEmpty ts)} mx)
  collectCatch {m} (MkCC _ (throw err)) f | Failure {f=m} = f err
  collectCatch {m} (MkCC _ (pure x)) _    | Success {f=m} = pure x

export
or : (Monad m, Successable m (ts : List t ** NonEmpty ts)) =>
  CatchCollect {m} {t} a -> CatchCollect {m} {t} a -> CatchCollect {m} {t} a
or ccx ccy = ccx `collectCatch` const ccy

export
collectThrow : (Monad m, Successable m (ts : List t ** NonEmpty ts)) =>
  a -> t -> CatchCollect {m} {t} a
collectThrow fallback = collect fallback . Left

export
collectThrowMonoid : (Monad m, Successable m (ts : List t ** NonEmpty ts)) =>
  Monoid a => t -> CatchCollect {m} {t} a
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
test : EitherCollect String Nat
test = do
  x <- collect 0 (Left "err0")
  y <- collect 0 (Right 12)
  z <- collect 0 (Left $ show x <+> show y)
  pure $ sum [x,y,z]
