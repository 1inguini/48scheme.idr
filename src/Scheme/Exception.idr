module Exception

public export
interface Throwable e ma where
  throw : e -> ma

public export
interface Throwable e ma => Catchable e ma where
  catch : ma -> (e -> ma) -> ma

public export
implementation Throwable e (Maybe a) where
  throw _ = Nothing

public export
implementation Throwable e (Either e a) where
  throw = Left

public export
implementation Catchable e (Either e a) where
  catch (Left err) f = f err
  catch (Right x) _ = Right x

