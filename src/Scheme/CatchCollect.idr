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

private
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

-- export
-- collect : (applicativeImplM : Applicative m, catchableImplM : Catchable m t,
--   monadImplN : Monad n, catchableImplN : Catchable n (ls : List t ** NonEmpty ls)) =>
--   a -> m a ->
--   CatchCollect
--     @{applicativeImplM} @{catchableImplM}
--     @{monadImplN} @{catchableImplN}
--     {view} a
-- collect fallback mx =
--   let mfallback = pure fallback 
--   in MkCC mfallback {safety = the (NeverThrow mfallback) IsNeverThrow} $ toNeverThrow $ pure <$> mx

-- collectMonoid : (applicativeImplM : Applicative m, catchableImplM : Catchable m t,
--   monadImplN : Monad n, catchableImplN : Catchable n (ls : List t ** NonEmpty ls)) =>
--   Monoid a =>
--   m a ->
--   CatchCollect
--     @{applicativeImplM} @{catchableImplM}
--     @{monadImplN} @{catchableImplN}
--     {view} a
-- collectMonoid = collect neutral

-- private
-- viewEither : (mx : Either t a) -> ViewCatchable mx
-- viewEither {t} (Left err) = Thrown {t} err
-- viewEither (Right x) = Success x

-- -- public export
-- -- implementation Catchable
-- --   (CatchCollect
-- --     {t=t}
-- --     @{applicativeImplM} @{catchableImplM}
-- --     @{monadImplN} @{catchableImplN}
-- --     {view}) t where
-- --   catch (MkCC mnxThrowable) func =
-- --     let mnx = toNeverThrow mnxThrowable
-- --     in MkCC $ (\nx => catch nx (\(errs ** ok) => runCatchCollect $ func $ last {ok} errs)) <$> mnx
-- --   throw err = MkCC $ pure $ throw ([err] ** IsNonEmpty)

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
-- maybeImpl :
--   (iface : Type) ->
--   {default (| Just %implementation, Nothing |) mmi : Maybe iface} ->
--   Maybe iface
-- maybeImpl _ {mmi} = mmi

-- private
-- exampleOf : (a : Type) ->
--   {default (|
--     Just %implementation,
--     Just 0,
--     Just [],
--     Just neutral,
--     Just default {- Effect.Default.defaut -},
--     Nothing |) mmi : Maybe a} -> Maybe a
-- exampleOf _ {mmi} = mmi

-- private
-- implementation Monad (CatchCollect @{monadImplM} @{catchableImplM} @{monadImplN} @{catchableImplN} {view}) where
--   (>>=) {a} (MkCC mnx) f = MkCC (do
--     nx <- toNeverThrow mnx
--     case exampleOf a of
--       Nothing => pure (nx >>= runCatchCollect . f)
--       Just val => do
--         nyFallback <- toNeverThrow $ unCC $ f val
--         pure (do
--           x <- nx `catch` \(errX :: errsX ** _) => do
--             errs <- (const errsX <$> nyFallback) `catch` \(errs ** _) => pure $ errsX <+> errs
--             throw (errX :: errs ** the (NonEmpty (errX :: errs)) IsNonEmpty)
--           runCatchCollect $ f x))

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
test : CatchCollect Nat
  {t = String}
  {m = Either String}
  {n = Either (ls : List String ** NonEmpty ls)}
test = do
  x <- collect 0 (throw "err0")
  y <- collect 0 (pure 12)
  z <- collect 0 (throw $ show x <+> show y)
  pure $ sum [x,y,z]
