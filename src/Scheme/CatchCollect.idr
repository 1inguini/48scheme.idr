module CatchCollect

import Control.Catchable
import Control.Monad.Trans
import Control.Monad.Identity
import Control.Monad.Writer as Writer

%default total

export
or : Catchable m t => m a -> m a -> m a
or mx my = mx `catch` const my

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

implementation (Successable m t, Applicative n, Catchable n t) => Cast (m a) (n a) where
  cast {t} mx with (result {t} mx)
    cast {t} (throw err) | Failure {t} = throw err
    cast {m} (pure  x)   | Success {m} = pure x

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
  Errors : (errs : List t) -> {auto atLeastOne : NonEmpty errs} -> CatchCollect t a
  Pure   : a -> CatchCollect t a

export
runCatchCollect : (Applicative m, Catchable m (List t)) => CatchCollect t a -> m a
runCatchCollect (Pure x)      = pure x
runCatchCollect (Errors errs) = throw errs

export
runCatchCollectNonEmpty : (Applicative m, Catchable m (ts : List t ** NonEmpty ts)) => CatchCollect t a -> m a
runCatchCollectNonEmpty (Pure x)                   = pure x
runCatchCollectNonEmpty (Errors errs {atLeastOne}) = throw (errs ** atLeastOne)

-- private
-- getInternal : CatchCollect t a -> a
-- getInternal (MkCC _ x) = x

-- private
-- getErrors : CatchCollect t a -> List t
-- getErrors (MkCC errs _) = errs

-- -- private
-- -- cram : (Successable f t, Successable m (ts : List t ** NonEmpty ts)) =>
-- --   f (m a) -> m a
-- -- cram {f} {t} fmx with (result {m=f} {t} fmx)
-- --   cram {f} {t} (throw err) | Failure {f} =
-- --     runIsSuccess {f} {t} (pure {f} $ throw {m} ([err] ** IsNonEmpty)) ItIsSuccess
-- --   cram {f} (pure fx) | Success {f} = fx

public export
implementation Functor (CatchCollect t) where
  map _ (Errors errs {atLeastOne}) = Errors errs {atLeastOne}
  map f (Pure x) = Pure $ f x

public export
implementation Applicative (CatchCollect t) where
  pure x = Pure x
  (<*>) (Errors (err :: errsF)) (Errors errsX) = Errors $ err :: errsF <+> errsX
  (<*>) (Errors errsF)          (Pure _)       = Errors errsF
  (<*>) (Pure _)                (Errors errsX) = Errors errsX
  (<*>) (Pure f)                (Pure x)       = Pure $ f x

public export
implementation Monad (CatchCollect t) where
  (>>=) (Errors errsX) _ = Errors errsX
  (>>=) (Pure x) f = f x

public export
implementation Catchable (CatchCollect t) t where
  catch     (Errors (err :: _)) f = f err
  catch ccx@(Pure _)            _ = ccx
  throw err = Errors [err]

export
record CatchCollectT (t : Type) (m : Type -> Type) (a : Type) where
  constructor CCT
  runCCT : m (CatchCollect t a)

export
runCatchCollectT : CatchCollectT t m a -> m (CatchCollect t a)
runCatchCollectT = runCCT

public export
implementation Functor f => Functor (CatchCollectT t f) where
  map f = CCT . map (map f) . runCatchCollectT

public export
implementation Applicative f => Applicative (CatchCollectT t f) where
  pure = CCT . pure . pure
  (<*>) (CCT mccf) (CCT mccx) = CCT $ (<*>) <$> mccf <*> mccx

public export
implementation Monad f => Monad (CatchCollectT t f) where
  (>>=) (CCT mccx) f = CCT (do
    ccx <- mccx
    case ccx of
      Errors errs => pure $ Errors errs
      Pure x      => runCatchCollectT $ f x)

public export
implementation MonadTrans (CatchCollectT t) where
  lift = CCT . map Pure

-- export
-- collect : Successable m t => a -> m a -> CatchCollect t a
-- collect fallback mx with (result {t} mx)
--   collect {t} fallback (throw err) | Failure {t} = MkCC [err] fallback
--   collect {m} _        (pure  x)   | Success {m} = MkCC [] x

-- export
-- collectMonoid : (Successable m t, Monoid a) => m a -> CatchCollect t a
-- collectMonoid = collect neutral

-- export
-- collectCatch : CatchCollect t a -> (List t -> CatchCollect t a) -> CatchCollect t a
-- collectCatch (MkCC []   x) _ = pure x
-- collectCatch (MkCC errs _) f = f errs

-- export
-- or : CatchCollect t a -> CatchCollect t a -> CatchCollect t a
-- or ccx ccy = ccx `collectCatch` const ccy

-- export
-- collectThrow : a -> t -> CatchCollect t a
-- collectThrow fallback = collect fallback . Left

-- export
-- collectThrowMonoid : Monoid a => t -> CatchCollect t a
-- collectThrowMonoid = collectThrow neutral

-- -- private
-- -- test : CatchCollect {m = Either String} {n = Either (ls : List String ** NonEmpty ls)} Nat
-- -- test = (\x,y,z => sum [x,y,z])
-- --   <$> collect (throw "err0")
-- --   <*> collect (pure 12)
-- --   <*> collect (throw "err2")

-- -- private
-- -- test : CatchCollect Nat
-- --   {t = String}
-- --   {m = Either String}
-- --   {n = Either (ls : List String ** NonEmpty ls)}
-- -- test =
-- --   [|
-- --     (\x,y,z => sum [x,y,z])
-- --     (collect 0 (throw "err0"))
-- --     (collect 0 (pure 12))
-- --     (collect 0 (throw "err2"))
-- --   |]

-- private
-- test : CatchCollect String Nat
-- test = do
--   x <- collect 0 (Left "err0")
--   y <- collect 0 (Right 12)
--   z <- collect 0 (Left $ show x <+> show y)
--   pure $ sum [x,y,z]
