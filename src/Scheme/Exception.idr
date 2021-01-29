module Exception

public export
interface Exception e

public export
interface (Monad m, Exception e) => MonadThrow e (m : Type -> Type) where
  throw : e -> m a

public export
interface MonadThrow e m => MonadCatch e (m : Type -> Type) where
  catch : m a -> (e -> m a) -> m a

public export
implementation Exception e => MonadThrow e Maybe where
  throw _ = Nothing

public export
implementation Exception e => MonadThrow e (Either e) where
  throw = Left

public export
implementation Exception e => MonadCatch e (Either e) where
  catch (Left err) f = f err
  catch (Right x) _ = Right x
