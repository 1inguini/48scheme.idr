module Main

import Control.Catchable
import Derive.Eq
import Derive.Show
import Data.Vect
import Data.Primitives.Views
import Data.Complex
import Data.SortedMap
-- import Scheme.Exception
import Scheme.CatchCollect

%default total
%language ElabReflection

private
implementation Semigroup () where
  (<+>) _ _ = ()

private
implementation Monoid () where
 neutral = ()

private
implementation Cast a a where
  cast = id

export
ComplexD : Type
ComplexD = Complex Double

export
implementation Cast Integer ComplexD where
  cast = (:+ 0) . cast

export
implementation Cast Double ComplexD where
  cast = (:+ 0)

%runElab deriveShow `{Ordering}

namespace Lisp

  namespace Number
    ||| Number Type for Lisp.Value
    public export
    data Ty
      = Complex
      | Real
      | Integer

    %runElab deriveEq `{Number.Ty}
    mutual -- parsing fails without this
    %runElab deriveShow `{Number.Ty}

    implementation Ord Number.Ty where
      compare Number.Complex Number.Complex = EQ
      compare Number.Complex y              = GT
      compare Number.Real    Number.Complex = LT
      compare Number.Real    Number.Real    = EQ
      compare Number.Real    Number.Integer = GT
      compare Number.Integer Number.Integer = EQ
      compare Number.Integer y              = LT

    export
    representation : Number.Ty -> Type
    representation Number.Complex = ComplexD
    representation Number.Real    = Double
    representation Number.Integer = Integer

    export
    fallbackFor : (nty : Number.Ty) -> Number.representation nty
    fallbackFor Number.Complex = 0 :+ 0
    fallbackFor Number.Real    = 0
    fallbackFor Number.Integer = 0

  public export
  data Ty
    = Atom
    | List
    | DottedList
    | Number Number.Ty
    | String
    | Bool

  %runElab deriveEq `{Lisp.Ty}
  mutual -- parsing fails without this
  %runElab deriveShow `{Lisp.Ty}
  mutual -- parsing fails without this

--   decEqTy : (x : Lisp.Ty) -> (y : Lisp.Ty) -> Dec (x = y)
--   %runElab deriveDecEq `{decEqTy}

--   implementation DecEq Lisp.Ty where
--     decEq = decEqTy

  mutual
    public export
    data Value : Type where
      ValueOf : (vty : Lisp.Ty) -> (val : representation vty) -> Lisp.Value

    export
    representation : Lisp.Ty -> Type
    representation Lisp.Atom         = String
    representation Lisp.List         = List Lisp.Value
    representation Lisp.DottedList   = (List Lisp.Value, Lisp.Value)
    representation (Lisp.Number nty) = Number.representation nty
    representation Lisp.String       = String
    representation Lisp.Bool         = Bool

  export
  getType : Lisp.Value -> Lisp.Ty
  getType (ValueOf lty _) = lty

  export
  unValue : (wanted : Lisp.Ty) -> (v : Lisp.Value) -> {ok : wanted = getType v} ->
    representation wanted
  unValue wanted {ok} (ValueOf _ x) = rewrite ok in x

  implementation Show Lisp.Value where
    show (ValueOf Lisp.Atom atm) = atm
    show (ValueOf Lisp.List ls) = "(" <+> unwords (assert_total show <$> ls) <+> ")"
    show (ValueOf Lisp.DottedList (ls, x)) =
      concat {t=List} ["(", unwords (assert_total show <$> ls), " . ", assert_total (show x), ")"]
    show (ValueOf (Lisp.Number Number.Complex) num) = show num
    show (ValueOf (Lisp.Number Number.Real) num) = show num
    show (ValueOf (Lisp.Number Number.Integer) num) = show num
    show (ValueOf Lisp.String str) = "\"" <+> str <+> "\""
    show (ValueOf Lisp.Bool True) = "#t"
    show (ValueOf Lisp.Bool False) = "#f"

  implementation Semigroup Lisp.Value where
    (<+>) x y = ValueOf Lisp.List $ toList x <+> toList y
      where
        toList : Lisp.Value -> List Lisp.Value
        toList (ValueOf Lisp.List ls) = ls
        toList val = [val]

  implementation Monoid Lisp.Value where
    neutral = ValueOf Lisp.List []

--   data TypeOf : (v : Lisp.Value) -> (expected : Lisp.Ty) -> Type where
--     IsNot : {expected : Lisp.Ty} -> {vty : Lisp.Ty} -> (no : Not (expected = vty)) -> {x : representation vty} ->
--       TypeOf (ValueOf vty x) expected
--     Is : {vty : Lisp.Ty} -> {x : representation vty} -> TypeOf (ValueOf vty x) vty

--   typeOf : (v : Lisp.Value) -> (expected : Lisp.Ty) -> TypeOf v expected
--   typeOf (ValueOf vty x) expected with (decEq expected vty)
--     | No contra = IsNot contra
--     | Yes prf = rewrite prf in Is


  namespace Util
    atom : String -> Lisp.Value
    atom = ValueOf Lisp.Atom

    list : List Lisp.Value -> Lisp.Value
    list = ValueOf Lisp.List

    dottedList : List Lisp.Value -> Lisp.Value -> Lisp.Value
    dottedList xs x = ValueOf Lisp.DottedList (xs, x)

    integer : Integer -> Lisp.Value
    integer = ValueOf (Lisp.Number Number.Integer)

    real : Double -> Lisp.Value
    real = ValueOf (Lisp.Number Number.Real)

    complex : ComplexD -> Lisp.Value
    complex = ValueOf (Lisp.Number Number.Complex)

    number : (nty : Number.Ty) -> Number.representation nty -> Lisp.Value
    number nty = ValueOf (Lisp.Number nty)

    string : String -> Lisp.Value
    string = ValueOf Lisp.String

    bool : Bool -> Lisp.Value
    bool = ValueOf Lisp.Bool

    quote : Lisp.Value -> Lisp.Value
    quote ls = ValueOf Lisp.List [ValueOf Lisp.Atom "quote", ls]

  namespace Interpreter

    public export
    data Error
      = NumArgs Ordering Nat (List Lisp.Value)
      | TypeMismatch Lisp.Ty (Lisp.Value)
      | BadSpecialForm String (Lisp.Value)
      | UnboundVar String
      | ZeroDivision
      | Default String

    %runElab deriveShow `{Interpreter.Error}

    export
    Errors : Type
    Errors = List Interpreter.Error

    throwTypeMismatchNumber : Catchable m Interpreter.Error => Lisp.Value -> m a
    throwTypeMismatchNumber v =
      or (throw $ TypeMismatch (Lisp.Number Number.Integer) v) $
      or (throw $ TypeMismatch (Lisp.Number Number.Real) v) $
      throw $ TypeMismatch (Lisp.Number Number.Complex) v

    export
    Interpreter : Type -> Type
    Interpreter a = CatchCollect Interpreter.Error a

    export
    numberCastTo : (Applicative m, Catchable m Interpreter.Error) =>
      Number.Ty -> Lisp.Value -> m Lisp.Value
    numberCastTo Number.Complex v@(ValueOf (Lisp.Number Number.Complex) _) = pure v
    numberCastTo Number.Complex   (ValueOf (Lisp.Number Number.Real)    x) = pure $ complex $ cast x
    numberCastTo Number.Complex   (ValueOf (Lisp.Number Number.Integer) x) = pure $ complex $ cast x
    numberCastTo Number.Real    v@(ValueOf (Lisp.Number Number.Complex) _) = throw $ TypeMismatch (Lisp.Number Number.Real) v
    numberCastTo Number.Real    v@(ValueOf (Lisp.Number Number.Real)    _) = pure v
    numberCastTo Number.Real      (ValueOf (Lisp.Number Number.Integer) x) = pure $ real $ cast x
    numberCastTo Number.Integer v@(ValueOf (Lisp.Number Number.Complex) x) = throw $ TypeMismatch (Lisp.Number Number.Integer) v
    numberCastTo Number.Integer v@(ValueOf (Lisp.Number Number.Real)    x) = throw $ TypeMismatch (Lisp.Number Number.Integer) v
    numberCastTo Number.Integer v@(ValueOf (Lisp.Number Number.Integer) _) = pure v
    numberCastTo _ v = throwTypeMismatchNumber v

    export
    valueToNum : (Applicative m, Catchable m Interpreter.Error) =>
      (nty : Number.Ty) -> Lisp.Value -> m (Number.representation nty)
    valueToNum Number.Complex (ValueOf (Lisp.Number Number.Complex) x) = pure x
    valueToNum Number.Complex (ValueOf (Lisp.Number Number.Real)    x) = pure $ cast x
    valueToNum Number.Complex (ValueOf (Lisp.Number Number.Integer) x) = pure $ cast x
    valueToNum Number.Complex v                                        = throw $ TypeMismatch (Lisp.Number Number.Complex) v
    valueToNum Number.Real    (ValueOf (Lisp.Number Number.Real) x)    = pure $ cast x
    valueToNum Number.Real    (ValueOf (Lisp.Number Number.Integer) x) = pure $ cast x
    valueToNum Number.Real    v                                        = throw $ TypeMismatch (Lisp.Number Number.Real) v
    valueToNum Number.Integer (ValueOf (Lisp.Number Number.Real) x)    = pure $ cast x
    valueToNum Number.Integer (ValueOf (Lisp.Number Number.Integer) x) = pure $ cast x
    valueToNum Number.Integer v                                        = throw $ TypeMismatch (Lisp.Number Number.Integer) v

    private
    valueListToNumberRepresentationList : (Applicative m, Catchable m Interpreter.Error) =>
      (nty : Number.Ty) -> List Lisp.Value -> m (List (Number.representation nty))
    valueListToNumberRepresentationList nty vs = traverse (valueToNum nty) vs

    private
    numOpToLispOp : (Monad m, Catchable m Interpreter.Error) =>
      (nty : Number.Ty) -> (let ty = Number.representation nty in ty -> ty -> ty) ->
      Lisp.Value -> Lisp.Value -> m Lisp.Value
    numOpToLispOp nty op vx vy = do
      (x, y) <- MkPair <$> valueToNum nty vx <*> valueToNum nty vy
      pure $ ValueOf (Lisp.Number nty) $ op x y

    private
    numMaybeOpToLispOp : (Monad m, Catchable m Interpreter.Error) =>
      (nty : Number.Ty) ->  (let ty = Number.representation nty in ty -> ty -> Maybe ty) ->
      Lisp.Value -> Lisp.Value -> m Lisp.Value
    numMaybeOpToLispOp nty op vx vy = do
      (x, y) <- MkPair <$> valueToNum nty vx <*> valueToNum nty vy
      maybe (throw ZeroDivision) (pure . ValueOf (Lisp.Number nty)) $ op x y

    export
    opToLispOp : (Monad m, Catchable m Interpreter.Error) =>
      (Maybe (Integer -> Integer -> Integer)) ->
      (Maybe (Double -> Double -> Double)) ->
      (Maybe (ComplexD -> ComplexD -> ComplexD)) ->
      Lisp.Value -> Lisp.Value -> m Lisp.Value
    opToLispOp Nothing    Nothing    Nothing    vx vy = throw $ Default "Bad primitive"
    opToLispOp Nothing    Nothing    (Just opC) vx@(ValueOf (Lisp.Number _) _) vy@(ValueOf (Lisp.Number _) _) = numOpToLispOp Number.Complex opC vx vy
    opToLispOp Nothing    (Just opR) Nothing    vx@(ValueOf (Lisp.Number _) _) vy@(ValueOf (Lisp.Number _) _) = numOpToLispOp Number.Real    opR vx vy
    opToLispOp Nothing    (Just opR) (Just opC) vx@(ValueOf (Lisp.Number _) _) vy@(ValueOf (Lisp.Number _) _) = numOpToLispOp Number.Real    opR vx vy `or`
                                                                                                                numOpToLispOp Number.Complex opC vx vy
    opToLispOp (Just opI) Nothing    Nothing    vx@(ValueOf (Lisp.Number _) _) vy@(ValueOf (Lisp.Number _) _) = numOpToLispOp Number.Integer opI vx vy
    opToLispOp (Just opI) Nothing    (Just opC) vx@(ValueOf (Lisp.Number _) _) vy@(ValueOf (Lisp.Number _) _) = numOpToLispOp Number.Integer opI vx vy `or`
                                                                                                                numOpToLispOp Number.Complex opC vx vy
    opToLispOp (Just opI) (Just opR) Nothing    vx@(ValueOf (Lisp.Number _) _) vy@(ValueOf (Lisp.Number _) _) = numOpToLispOp Number.Integer opI vx vy `or`
                                                                                                                numOpToLispOp Number.Real    opR vx vy
    opToLispOp (Just opI) (Just opR) (Just opC) vx@(ValueOf (Lisp.Number _) _) vy@(ValueOf (Lisp.Number _) _) = numOpToLispOp Number.Integer opI vx vy `or`
                                                                                                               (numOpToLispOp Number.Real    opR vx vy `or`
                                                                                                                numOpToLispOp Number.Complex opC vx vy)
    opToLispOp _ _ _ vx@(ValueOf (Lisp.Number _) _) vy = throwTypeMismatchNumber vy
    opToLispOp _ _ _ vx vy@(ValueOf (Lisp.Number _) _) = throwTypeMismatchNumber vx
    opToLispOp _ _ _ vx vy = (*>) {a = ()} (throwTypeMismatchNumber vx) (throwTypeMismatchNumber vy)

    foldOrUnaryLispBinOp : (Monad m, Catchable m Interpreter.Error) =>
      (Lisp.Value -> Lisp.Value -> m Lisp.Value) -> Lisp.Value ->
      List Lisp.Value -> m Lisp.Value
    foldOrUnaryLispBinOp _ _       []        = throw $ NumArgs GT 1 []
    foldOrUnaryLispBinOp f neutral [x]       = f neutral x
    foldOrUnaryLispBinOp f _       (x :: xs) = foldlM f x xs

    private
    lispBinOp : (Applicative m, Catchable m Interpreter.Error) =>
      (Lisp.Value -> Lisp.Value -> m Lisp.Value) ->
      List.List Lisp.Value -> m Lisp.Value
    lispBinOp f [x, y] = f x y
    lispBinOp _ xs = throw $ NumArgs EQ 2 xs

    private
    natQuotient : Nat -> Nat -> Maybe Nat
    natQuotient dividend Z = Nothing
    natQuotient dividend divisor = Just $ quotHelper divisor 0
      where
        quotHelper : Nat -> Nat -> Nat
        quotHelper accm count =
          if lt accm dividend
          then assert_total $ quotHelper (accm + divisor) (S count)
          else count

    private
    quotient : Integer -> Integer -> Maybe Integer
    quotient _ 0 = Nothing
    quotient dividend divisor with (dividend * divisor < 0)
      | False = cast <$> natQuotient (cast $ abs dividend) (cast $ abs divisor)
      | True = negate . cast <$> natQuotient (cast $ abs dividend) (cast $ abs divisor)

    private
    remainder : Integer -> Integer -> Maybe Integer
    remainder dividend divisor = do
      quot <- quotient dividend divisor
      pure $ dividend - divisor * quot

    private
    modulo : Integer -> Integer -> Maybe Integer
    modulo dividend divisor = do
      rem <- remainder dividend divisor
      pure $ rem + if dividend * divisor < 0 then divisor else 0

    private
    opToValueListOp : (Applicative m, Catchable m Interpreter.Error) =>
      (nty : Number.Ty) -> let ty = Number.representation nty in (ty -> ty -> ty) -> ty -> List Lisp.Value -> m Lisp.Value
    opToValueListOp nty op seed vs = Util.number nty . foldl op seed <$> valueListToNumberRepresentationList nty vs

    makeValueListOp : (Applicative m, Catchable m Interpreter.Error) =>
      (definitions : Vect (S len) (nty : Number.Ty ** let ty = Number.representation nty in (ty -> ty -> ty, ty))) -> List Lisp.Value -> m Lisp.Value
    makeValueListOp definitions vs = foldl1 or $ map (\(nty ** (op, seed)) => opToValueListOp nty op seed vs) definitions

    export
    primitivesEnv : (Monad m, Catchable m Interpreter.Error) =>
      SortedMap String (List Lisp.Value -> m Lisp.Value)
    primitivesEnv = SortedMap.fromList
      [ ("+", makeValueListOp [(Number.Integer ** ((+), 0)), (Number.Real ** ((+), 0)), (Number.Complex ** ((+), 0))])
      , ("*", makeValueListOp [(Number.Integer ** ((*), 1)), (Number.Real ** ((*), 1)), (Number.Complex ** ((*), 1))])
      , ("-", foldOrUnaryLispBinOp (opToLispOp (Just (-)) (Just (-)) (Just (-))) $ integer 0)
      , ("/", foldOrUnaryLispBinOp (opToLispOp Nothing    (Just (/)) (Just (/))) $ integer 1)
      , ("quotient", lispBinOp $ numMaybeOpToLispOp Number.Integer quotient)
      , ("remainder", lispBinOp $ numMaybeOpToLispOp Number.Integer remainder)
      , ("modulo", lispBinOp $ numMaybeOpToLispOp Number.Integer modulo)
      ]

    export
    envLookup : (Monad m, Catchable m Interpreter.Error) =>
      String -> m (List Lisp.Value -> m Lisp.Value)
    envLookup {m} name with (SortedMap.lookup name (primitivesEnv {m}))
      | Nothing = throw $ UnboundVar name
      | Just x = pure x

  namespace repl
    eval : (Monad m, Catchable m Interpreter.Error) =>
      Lisp.Value -> m Lisp.Value
    eval (ValueOf Lisp.List [ValueOf Lisp.Atom "quote", ls]) = pure ls
    eval (ValueOf Lisp.List (ValueOf Lisp.Atom fname :: args)) = do
      f <- envLookup fname
      args' <- traverse (assert_total eval) args
      f args'
    eval val = pure val

private
test : Lisp.Value -> Either Interpreter.Errors Lisp.Value
test = runCatchCollect . eval

private
examples : List Lisp.Value
examples =
  [ Util.atom "quote"
  , Util.quote $ Util.list [Util.string "aaa", Util.string "bbb"]
  , Util.atom "+"
  , Util.list [Util.atom "+", Util.list [Util.string "aaa", Util.string "bbb"]]
  , Util.list [Util.atom "+", Util.string "aaa", Util.string "bbb"]
  , Util.list [Util.atom "+", Util.string "aaa", Util.atom "bbb", Util.string "ccc"]
  , Util.list [Util.atom "+", Util.integer 3, Util.integer 4]
  , Util.list [Util.atom "+", Util.integer 3]
  , Util.list [Util.atom "+"]
  , Util.atom "*"
  , Util.list [Util.atom "*", Util.integer 4]
  , Util.list [Util.atom "*"]
  , Util.atom "-"
  , Util.list [Util.atom "-", Util.string "aaa", Util.atom "bbb", Util.string "ccc"]
  , Util.list [Util.atom "-", Util.integer 3, Util.integer 4]
  , Util.list [Util.atom "-", Util.integer 3, Util.integer 4, Util.integer 5]
  , Util.list [Util.atom "-", Util.integer 3]
  , Util.atom "/"
  , Util.list [Util.atom "/", Util.integer 3, Util.integer 4]
  , Util.list [Util.atom "/", Util.integer 3, Util.integer 4, Util.integer 5]
  , Util.list [Util.atom "/", Util.integer 3]
  , Util.atom "quotient"
  , Util.list [Util.atom "quotient", Util.integer   13,  Util.integer   4]
  , Util.list [Util.atom "quotient", Util.integer (-13), Util.integer   4]
  , Util.list [Util.atom "quotient", Util.integer   13,  Util.integer (-4)]
  , Util.list [Util.atom "quotient", Util.integer (-13), Util.integer (-4)]
  , Util.atom "remainder"
  , Util.list [Util.atom "remainder", Util.integer   13,  Util.integer   4]
  , Util.list [Util.atom "remainder", Util.integer (-13), Util.integer   4]
  , Util.list [Util.atom "remainder", Util.integer   13,  Util.integer (-4)]
  , Util.list [Util.atom "remainder", Util.integer (-13), Util.integer (-4)]
  , Util.atom "modulo"
  , Util.list [Util.atom "modulo", Util.integer   13,  Util.integer   4]
  , Util.list [Util.atom "modulo", Util.integer (-13), Util.integer   4]
  , Util.list [Util.atom "modulo", Util.integer   13,  Util.integer (-4)]
  , Util.list [Util.atom "modulo", Util.integer (-13), Util.integer (-4)]
  ]

-- main : IO ()
-- main = ?main

  --  -- do
  --  --  x <- MkErrCollector ["error : 1"] "1" `catch` \errs => do
  --  --    y <- throw ["error thrown"]
  --  --    z <- MkErrCollector ["error : 2"] "2"
  --  --    w <- throw (the (List String) errs)
  --  --    pure $ y <+> z <+> w
  --  --  pure $ x
