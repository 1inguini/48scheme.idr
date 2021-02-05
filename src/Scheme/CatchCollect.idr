module CatchCollect

import Control.Catchable
import Control.Monad.Trans
import Control.Monad.Identity
import Control.Monad.Writer as Writer

%default total

public export
data ViewCatchable : (monadImpl : Monad m, catchableImpl : Catchable m t) => m a -> Type where
  Thrown : (err : t) -> ViewCatchable @{monadImpl} @{catchableImpl} {m} {t} (throw {m} {a} err)
  Success : (x : a) -> ViewCatchable @{monadImpl} @{catchableImpl} {m} {t} (pure {f=m} {a} x)

export
data CatchCollect :
  (monadImplM : Monad m, catchableImplM : Catchable m t, 
    monadImplN : Monad n, catchableImplN : Catchable n (ts : List t ** NonEmpty ts)) =>
  {view : (arb : Type) -> (mx : m arb) -> ViewCatchable {m=m} {a=arb} mx} ->
  Type -> Type where
  MkCC : m (n a) -> 
    CatchCollect
      @{monadImplM} @{catchableImplM}
      @{monadImplN} @{catchableImplN}
      {m} {n} {t} {view} a

private
squash :
  (monadImplM : Monad m, catchableImplM : Catchable m t,
    monadImplN : Monad n, catchableImplN : Catchable n (ls : List t ** NonEmpty ls)) =>
  {mnx : m (n a)} -> ViewCatchable mnx -> n a
squash {n} {a} (Thrown err) = throw {m = n} {a} ([err] ** IsNonEmpty)
squash (Success nx) = nx

export
runCatchCollect :
  (monadImplM : Monad m, catchableImplM : Catchable m t,
    monadImplN : Monad n, catchableImplN : Catchable n (ls : List t ** NonEmpty ls)) =>
  CatchCollect @{monadImplM} @{catchableImplM} @{monadImplN} @{catchableImplN} {view} a -> n a
runCatchCollect {view} (MkCC mnx) = squash $ view (n a) mnx

private
toNeverThrow :(monadImplM : Monad m, catchableImplM : Catchable m t,
  monadImplN : Monad n, catchableImplN : Catchable n (ls : List t ** NonEmpty ls)) =>
  m (n a) -> m (n a)
toNeverThrow mnx = mnx `catch` \err => pure $ throw ([err] ** IsNonEmpty)

export
collect : (monadImplM : Monad m, catchableImplM : Catchable m t,
  monadImplN : Monad n, catchableImplN : Catchable n (ls : List t ** NonEmpty ls)) =>
  m a ->
  CatchCollect
    @{monadImplM} @{catchableImplM}
    @{monadImplN} @{catchableImplN}
    {view} a
collect mx = MkCC $ toNeverThrow $ pure <$> mx

private
viewEither : (mx : Either t a) -> ViewCatchable mx
viewEither {t} (Left err) = Thrown {t} err
viewEither (Right x) = Success x

public export
implementation Catchable
  (CatchCollect
    {t=t}
    @{monadImplM} @{catchableImplM}
    @{monadImplN} @{catchableImplN}
    {view}) t where
  catch (MkCC mnxThrowable) func = 
    let mnx = toNeverThrow mnxThrowable 
    in MkCC $ (\nx => catch nx (\(errs ** ok) => runCatchCollect $ func $ last {ok} errs)) <$> mnx
  throw err = MkCC $ pure $ throw ([err] ** IsNonEmpty)

public export
implementation Functor (CatchCollect @{monadImplM} @{catchableImplM} @{monadImplN} @{catchableImplN} {view}) where
  map f (MkCC mnx) = MkCC $ map (map f) mnx

public export
implementation Applicative (CatchCollect @{monadImplM} @{catchableImplM} @{monadImplN} @{catchableImplN} {view}) where
  pure x = MkCC $ pure $ pure x
  (<*>) (MkCC mnfThrowable) (MkCC mnxThrowable) =
    let
      mnf = toNeverThrow mnfThrowable
      mnx = toNeverThrow mnxThrowable
    in MkCC (do
      nf <- mnf
      nx <- mnx
      pure (do
        f <- nf `catch` \(errF :: errsF ** _) => (do
          errs <- (const errsF <$> nx) `catch` \(errs ** _) => pure $ errsF <+> errs
          throw (errF :: errs ** the (NonEmpty (errF :: errs)) IsNonEmpty))
        x <- nx
        pure $ f x))

-- private
-- test : CatchCollect {m = Either String} {n = Either (ls : List String ** NonEmpty ls)} Nat
-- test = (\x,y,z => sum [x,y,z])
--   <$> collect (throw "err0")
--   <*> collect (pure 12)
--   <*> collect (throw "err2")

private
test : CatchCollect Nat
  {t = String}
  {m = Either String}
  {n = Either (ls : List String ** NonEmpty ls)}
  {view = \_ => CatchCollect.viewEither}
test =
  [|
    (\x,y,z => sum [x,y,z])
    (collect (throw "err0"))
    (collect (pure 12))
    (collect (throw "err2"))
  |]
