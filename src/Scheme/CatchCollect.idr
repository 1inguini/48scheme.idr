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
data CatchCollect : (Successable m t, Monad n, Successable n (ts : List t ** NonEmpty ts)) =>
  (a : Type) -> Type where
  MkCC : (Successable m t, Monad n, Successable n (ts : List t ** NonEmpty ts)) =>
    (fallback : a) -> (body : n a) -> CatchCollect {m} {n} {t} a

EitherCollect : Type -> Type -> Type
EitherCollect t a = CatchCollect a
  {t}
  {m = Either t}
  {n = Either (ts : List t ** NonEmpty ts)}

export
runCatchCollect : (Successable m t, Monad n, Successable n (ts : List t ** NonEmpty ts)) =>
  CatchCollect {m} {n} {t} a -> n a
runCatchCollect (MkCC _ mnx) = mnx

getFallback : (Successable m t, Monad n, Successable n (ts : List t ** NonEmpty ts)) =>
  CatchCollect {m} {n} {t} a -> a 
getFallback (MkCC fallback _) = fallback

private
cram : (Successable m t, Successable n (ts : List t ** NonEmpty ts)) =>
  m (n a) -> n a
cram {m} {t} mnx with (result {m} {t} mnx) 
  cram {m} {t} (throw err) | Failure {f=m} = 
    runIsSuccess {f=m} {t} (pure {f=m} $ throw {m=n} ([err] ** IsNonEmpty)) ItIsSuccess
  cram {m} (pure mx) | Success {f=m} = mx
  
export
collect : (Successable m t, Monad n, Successable n (ts : List t ** NonEmpty ts)) =>
  a -> m a -> CatchCollect {m} {n} {t} a
collect fallback fx = MkCC fallback $ cram $ map pure fx

export
collectMonoid : (Successable m t, Monad n, Successable n (ts : List t ** NonEmpty ts)) =>
  Monoid a => m a -> CatchCollect {m} {n} {t} a
collectMonoid = collect neutral

export
collectThrow : (Successable m t, Monad n, Successable n (ts : List t ** NonEmpty ts)) =>
  Monoid a => t -> CatchCollect {m} {n} {t} a
collectThrow = collectMonoid . throw

public export
implementation Functor (CatchCollect @{siN} @{miN} @{siM}) where
  map f (MkCC fallback mx) = MkCC (f fallback) $ map f mx

public export
implementation Applicative (CatchCollect @{siN} @{miN} @{siM}) where
  pure x = MkCC x $ pure x
  (<*>) (MkCC fallbackF nf) (MkCC fallbackX nx) =
    MkCC (fallbackF fallbackX) (do 
      f <- catch {t = (ts : List t ** NonEmpty ts)} nf $ \(errF :: errsF ** _) => (do
        errs <- (const errsF <$> nx) `catch` \(errs ** _) => pure $ errsF <+> errs
        throw (errF :: errs ** the (NonEmpty (errF :: errs)) IsNonEmpty))
      x <- nx
      pure $ f x)

public export
implementation Monad (CatchCollect @{siN} @{miN} @{siM}) where
  (>>=) {m} {t} (MkCC fallbackX nx) f = 
    MkCC (getFallback $ f fallbackX) (do
      x <- catch {t = (ts : List t ** NonEmpty ts)} nx $ \(errX :: errsX ** _) => (do
        errs <- (const errsX <$> runCatchCollect (f fallbackX)) `catch` \(errsY ** _) => 
                          pure $ errsX <+> errsY
        throw (errX :: errs ** the (NonEmpty (errX :: errs)) IsNonEmpty))
      runCatchCollect $ f x)

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
  x <- collect 0 (throw "err0")
  y <- collect 0 (pure 12)
  z <- collect 0 (throw $ show x <+> show y)
  pure $ sum [x,y,z]
