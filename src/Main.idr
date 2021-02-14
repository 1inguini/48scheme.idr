module Main

import Pruviloj
import Control.Catchable
import Derive.Eq
import Derive.Show
import Data.Primitives.Views
import Data.Complex
import Data.So
import Data.SortedMap as SortedMap
-- import Scheme.Exception
import Scheme.CatchCollect

%default total
%language ElabReflection

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

    export
    representation : Number.Ty -> Type
    representation Number.Complex = ComplexD
    representation Number.Real    = Double
    representation Number.Integer = Integer

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

  -- implementation Eq Lisp.Ty where
  --   (==) Lisp.Atom Lisp.Atom = True

  mutual
    public export
    data Value : Type where
      ValueOf : (vty : Lisp.Ty) -> (val : representation vty) -> Lisp.Value

    export
    representation : Lisp.Ty -> Type
    representation Lisp.Atom = String
    representation Lisp.List = List Lisp.Value
    representation Lisp.DottedList = (List Lisp.Value, Lisp.Value)
    representation (Lisp.Number nty) = Number.representation nty
    representation Lisp.String = String
    representation Lisp.Bool = Bool

  implementation Show Lisp.Value where
    show (ValueOf Lisp.Atom atm) = atm
    show (ValueOf Lisp.List ls) = "(" <+> unwords (assert_total show <$> ls) <+> ")"
    show (ValueOf Lisp.DottedList (ls, x)) =
      concat ["(", unwords (assert_total show <$> ls), " . ", assert_total (show x), ")"]
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

--   data ViewValueOf : Lisp.Ty -> Lisp.Value -> Type where
--     IsNot: {expected : Lisp.Ty} -> {vty : Lisp.Ty} -> {x : representation vty} ->
--       {auto isNotExpected : So (expected /= vty)} ->  ViewValueOf expected (ValueOf vty x)
--     Is: {expected : Lisp.Ty} -> {vty : Lisp.Ty} -> {x : representation vty} -> ViewValueOf expected (ValueOf vty x)

--   viewValueOf : (expected : Lisp.Ty) -> (v : Lisp.Value) -> ViewValueOf expected v
--   viewValueOf expected (ValueOf vty _) with (choose $ expected /= vty)
--     | Left prf = IsNot {isNotExpected = prf}
--     | Right _ = Is

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
      | TypeMismatchNumber (Lisp.Value)
      | BadSpecialForm String (Lisp.Value)
      | UnboundVar String
      | ZeroDivision
      | Default String

    %runElab deriveShow `{Interpreter.Error}

    export
    Interpreter :
      (Successable m Interpreter.Error, Monad n, Successable n (ts : List Interpreter.Error ** NonEmpty ts)) =>
      Type -> Type
    Interpreter {m} {n} a = CatchCollect {m} {n} {t = Interpreter.Error} a

    export
    numberCastTo :
      (Successable m Interpreter.Error, Monad n, Successable n (ts : List Interpreter.Error ** NonEmpty ts)) =>
      Number.Ty -> Lisp.Value -> Interpreter {m} {n} Lisp.Value
    numberCastTo Number.Complex v@(ValueOf (Lisp.Number Number.Complex) _) = pure v
    numberCastTo Number.Complex   (ValueOf (Lisp.Number Number.Real)    x) = pure $ complex $ cast x
    numberCastTo Number.Complex   (ValueOf (Lisp.Number Number.Integer) x) = pure $ complex $ cast x
    numberCastTo Number.Real    v@(ValueOf (Lisp.Number Number.Complex) _) = collectThrow $ TypeMismatch (Lisp.Number Number.Real) v
    numberCastTo Number.Real    v@(ValueOf (Lisp.Number Number.Real)    _) = pure v
    numberCastTo Number.Real      (ValueOf (Lisp.Number Number.Integer) x) = pure $ real $ cast x
    numberCastTo Number.Integer v@(ValueOf (Lisp.Number Number.Complex) x) = collectThrow $ TypeMismatch (Lisp.Number Number.Integer) v
    numberCastTo Number.Integer v@(ValueOf (Lisp.Number Number.Real)    x) = collectThrow $ TypeMismatch (Lisp.Number Number.Integer) v
    numberCastTo Number.Integer v@(ValueOf (Lisp.Number Number.Integer) _) = pure v
    numberCastTo _ v = collectThrow $ TypeMismatchNumber v

    export
    valueToComplex : (Applicative m, Catchable m Interpreter.Error) =>
      Lisp.Value -> m ComplexD
    valueToComplex (ValueOf (Lisp.Number Number.Complex) x) = pure x
    valueToComplex (ValueOf (Lisp.Number Number.Real) x) = pure $ cast x
    valueToComplex (ValueOf (Lisp.Number Number.Integer) x) = pure $ cast x
    valueToComplex x = throw $ TypeMismatch (Lisp.Number Number.Complex) x

    export
    valueToDouble : (Applicative m, Catchable m Interpreter.Error) =>
      Lisp.Value -> m Double
    valueToDouble (ValueOf (Lisp.Number Number.Real) x) = pure $ cast x
    valueToDouble (ValueOf (Lisp.Number Number.Integer) x) = pure $ cast x
    valueToDouble x = throw $ TypeMismatch (Lisp.Number Number.Real) x

    export
    valueToInteger : (Applicative m, Catchable m Interpreter.Error) =>
      Lisp.Value -> m Integer
    valueToInteger (ValueOf (Lisp.Number Number.Real) x) = pure $ cast x
    valueToInteger (ValueOf (Lisp.Number Number.Integer) x) = pure $ cast x
    valueToInteger x = throw $ TypeMismatch (Lisp.Number Number.Integer) x

    export
    opToLispOp : (Successable m Interpreter.Error, Monad n, Successable n (ts : List Interpreter.Error ** NonEmpty ts)) =>
      (Maybe (Integer -> Integer -> Integer)) ->
      (Maybe (Double -> Double -> Double)) ->
      (Maybe (ComplexD -> ComplexD -> ComplexD)) ->
      Lisp.Value -> Lisp.Value -> Interpreter {m} {n} Lisp.Value
    --         Integer   Real      ComplexD
    opToLispOp Nothing   Nothing   Nothing   x                                          y                                          = collectThrow $ Default "Bad primitive"
    opToLispOp Nothing   Nothing   (Just op)   (ValueOf (Lisp.Number Number.Complex) x)   (ValueOf (Lisp.Number Number.Complex) y) = pure $ complex $ op x y
    opToLispOp Nothing   Nothing   (Just op)   (ValueOf (Lisp.Number Number.Complex) x)   (ValueOf (Lisp.Number Number.Real)    y) = pure $ complex $ op x (cast y)
    opToLispOp Nothing   Nothing   (Just op)   (ValueOf (Lisp.Number Number.Complex) x)   (ValueOf (Lisp.Number Number.Integer) y) = pure $ complex $ op x (cast y)
    opToLispOp Nothing   Nothing   (Just op)   (ValueOf (Lisp.Number Number.Real)    x)   (ValueOf (Lisp.Number Number.Complex) y) = pure $ complex $ op (cast x) y
    opToLispOp Nothing   Nothing   (Just op)   (ValueOf (Lisp.Number Number.Real)    x)   (ValueOf (Lisp.Number Number.Real)    y) = pure $ complex $ op (cast x) (cast y)
    opToLispOp Nothing   Nothing   (Just op)   (ValueOf (Lisp.Number Number.Real)    x)   (ValueOf (Lisp.Number Number.Integer) y) = pure $ complex $ op (cast x) (cast y)
    opToLispOp Nothing   Nothing   (Just op)   (ValueOf (Lisp.Number Number.Integer) x)   (ValueOf (Lisp.Number Number.Complex) y) = pure $ complex $ op (cast x) y
    opToLispOp Nothing   Nothing   (Just op)   (ValueOf (Lisp.Number Number.Integer) x)   (ValueOf (Lisp.Number Number.Real)    y) = pure $ complex $ op (cast x) (cast y)
    opToLispOp Nothing   Nothing   (Just op)   (ValueOf (Lisp.Number Number.Integer) x)   (ValueOf (Lisp.Number Number.Integer) y) = pure $ complex $ op (cast x) (cast y)
    opToLispOp Nothing   (Just op) Nothing   x@(ValueOf (Lisp.Number Number.Complex) _) y@(ValueOf (Lisp.Number Number.Complex) _) = collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Real) x) *>
                                                                                                                                     collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Real) y)
    opToLispOp Nothing   (Just op) Nothing   x@(ValueOf (Lisp.Number Number.Complex) _)   (ValueOf (Lisp.Number Number.Real)    _) = collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Real) x)
    opToLispOp Nothing   (Just op) Nothing   x@(ValueOf (Lisp.Number Number.Complex) _) y@(ValueOf (Lisp.Number Number.Integer) _) = collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Integer) x) *>
                                                                                                                                     collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Real) y)
    opToLispOp Nothing   (Just op) Nothing     (ValueOf (Lisp.Number Number.Real)    _) y@(ValueOf (Lisp.Number Number.Complex) _) = collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Real) y)
    opToLispOp Nothing   (Just op) Nothing     (ValueOf (Lisp.Number Number.Real)    x)   (ValueOf (Lisp.Number Number.Real)    y) = pure $ real $ op x y
    opToLispOp Nothing   (Just op) Nothing     (ValueOf (Lisp.Number Number.Real)    x)   (ValueOf (Lisp.Number Number.Integer) y) = pure $ real $ op x (cast y)
    opToLispOp Nothing   (Just op) Nothing     (ValueOf (Lisp.Number Number.Integer) _) y@(ValueOf (Lisp.Number Number.Complex) _) = collectThrow (TypeMismatch (Lisp.Number Number.Integer) y)
    opToLispOp Nothing   (Just op) Nothing     (ValueOf (Lisp.Number Number.Integer) x)   (ValueOf (Lisp.Number Number.Real)    y) = pure $ real $ op (cast x) y
    opToLispOp Nothing   (Just op) Nothing     (ValueOf (Lisp.Number Number.Integer) x)   (ValueOf (Lisp.Number Number.Integer) y) = pure $ real $ op (cast x) (cast y)
    opToLispOp Nothing   (Just _)  (Just op)   (ValueOf (Lisp.Number Number.Complex) x)   (ValueOf (Lisp.Number Number.Complex) y) = pure $ complex $ op x y
    opToLispOp Nothing   (Just _)  (Just op)   (ValueOf (Lisp.Number Number.Complex) x)   (ValueOf (Lisp.Number Number.Real)    y) = pure $ complex $ op x (cast y)
    opToLispOp Nothing   (Just _)  (Just op)   (ValueOf (Lisp.Number Number.Complex) x)   (ValueOf (Lisp.Number Number.Integer) y) = pure $ complex $ op x (cast y)
    opToLispOp Nothing   (Just _)  (Just op)   (ValueOf (Lisp.Number Number.Real)    x)   (ValueOf (Lisp.Number Number.Complex) y) = pure $ complex $ op (cast x) y
    opToLispOp Nothing   (Just op) (Just _)    (ValueOf (Lisp.Number Number.Real)    x)   (ValueOf (Lisp.Number Number.Real)    y) = pure $ real $ op x y
    opToLispOp Nothing   (Just op) (Just _)    (ValueOf (Lisp.Number Number.Real)    x)   (ValueOf (Lisp.Number Number.Integer) y) = pure $ real $ op x (cast y)
    opToLispOp Nothing   (Just _)  (Just op)   (ValueOf (Lisp.Number Number.Integer) x)   (ValueOf (Lisp.Number Number.Complex) y) = pure $ complex $ op (cast x) y
    opToLispOp Nothing   (Just op) (Just _)    (ValueOf (Lisp.Number Number.Integer) x)   (ValueOf (Lisp.Number Number.Real)    y) = pure $ real $ op (cast x) y
    opToLispOp Nothing   (Just op) (Just _)    (ValueOf (Lisp.Number Number.Integer) x)   (ValueOf (Lisp.Number Number.Integer) y) = pure $ real $ op (cast x) (cast y)
    opToLispOp (Just _)  Nothing   Nothing   x@(ValueOf (Lisp.Number Number.Complex) _) y@(ValueOf (Lisp.Number Number.Complex) _) = collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Integer) x) *>
                                                                                                                                     collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Integer) y)
    opToLispOp (Just _)  Nothing   Nothing   x@(ValueOf (Lisp.Number Number.Complex) _) y@(ValueOf (Lisp.Number Number.Real)    _) = collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Integer) x) *>
                                                                                                                                     collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Integer) y)
    opToLispOp (Just _)  Nothing   Nothing   x@(ValueOf (Lisp.Number Number.Complex) _)   (ValueOf (Lisp.Number Number.Integer) _) = collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Integer) x)
    opToLispOp (Just _)  Nothing   Nothing   x@(ValueOf (Lisp.Number Number.Real)    _) y@(ValueOf (Lisp.Number Number.Complex) _) = collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Integer) x) *>
                                                                                                                                     collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Integer) y)
    opToLispOp (Just _)  Nothing   Nothing   x@(ValueOf (Lisp.Number Number.Real)    _) y@(ValueOf (Lisp.Number Number.Real)    _) = collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Integer) x) *>
                                                                                                                                     collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Integer) y)
    opToLispOp (Just _)  Nothing   Nothing   x@(ValueOf (Lisp.Number Number.Real)    _)   (ValueOf (Lisp.Number Number.Integer) _) = collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Integer) x)
    opToLispOp (Just _)  Nothing   Nothing     (ValueOf (Lisp.Number Number.Integer) _) y@(ValueOf (Lisp.Number Number.Complex) _) = collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Integer) y)
    opToLispOp (Just _)  Nothing   Nothing     (ValueOf (Lisp.Number Number.Integer) _) y@(ValueOf (Lisp.Number Number.Real)    _) = collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Integer) y)
    opToLispOp (Just op) Nothing   Nothing     (ValueOf (Lisp.Number Number.Integer) x)   (ValueOf (Lisp.Number Number.Integer) y) = pure $ integer $ op x y
    opToLispOp (Just _)  Nothing   (Just op)   (ValueOf (Lisp.Number Number.Complex) x)   (ValueOf (Lisp.Number Number.Complex) y) = pure $ complex $ op x y
    opToLispOp (Just _)  Nothing   (Just op)   (ValueOf (Lisp.Number Number.Complex) x)   (ValueOf (Lisp.Number Number.Real)    y) = pure $ complex $ op x (cast y)
    opToLispOp (Just _)  Nothing   (Just op)   (ValueOf (Lisp.Number Number.Complex) x)   (ValueOf (Lisp.Number Number.Integer) y) = pure $ complex $ op x (cast y)
    opToLispOp (Just _)  Nothing   (Just op)   (ValueOf (Lisp.Number Number.Real)    x)   (ValueOf (Lisp.Number Number.Complex) y) = pure $ complex $ op (cast x) y
    opToLispOp (Just _)  Nothing   (Just op)   (ValueOf (Lisp.Number Number.Real)    x)   (ValueOf (Lisp.Number Number.Real)    y) = pure $ complex $ op (cast x) (cast y)
    opToLispOp (Just _)  Nothing   (Just op)   (ValueOf (Lisp.Number Number.Real)    x)   (ValueOf (Lisp.Number Number.Integer) y) = pure $ complex $ op (cast x) (cast y)
    opToLispOp (Just _)  Nothing   (Just op)   (ValueOf (Lisp.Number Number.Integer) x)   (ValueOf (Lisp.Number Number.Complex) y) = pure $ complex $ op (cast x) y
    opToLispOp (Just _)  Nothing   (Just op)   (ValueOf (Lisp.Number Number.Integer) x)   (ValueOf (Lisp.Number Number.Real)    y) = pure $ complex $ op (cast x) (cast y)
    opToLispOp (Just op) Nothing   (Just _)    (ValueOf (Lisp.Number Number.Integer) x)   (ValueOf (Lisp.Number Number.Integer) y) = pure $ integer $ op x y
    opToLispOp (Just _)  (Just _)  Nothing   x@(ValueOf (Lisp.Number Number.Complex) _) y@(ValueOf (Lisp.Number Number.Complex) _) = collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Real) x) *>
                                                                                                                                     collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Real) y)
    opToLispOp (Just _)  (Just _)  Nothing   x@(ValueOf (Lisp.Number Number.Complex) _) y@(ValueOf (Lisp.Number Number.Real)    _) = collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Real) x)
    opToLispOp (Just _)  (Just _)  Nothing   x@(ValueOf (Lisp.Number Number.Complex) _) y@(ValueOf (Lisp.Number Number.Integer) _) = collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Real) x)
    opToLispOp (Just _)  (Just _)  Nothing     (ValueOf (Lisp.Number Number.Real)    _) y@(ValueOf (Lisp.Number Number.Complex) _) = collectThrow {a=Lisp.Value} (TypeMismatch (Lisp.Number Number.Real) y)
    opToLispOp (Just _)  (Just op) Nothing     (ValueOf (Lisp.Number Number.Real)    x)   (ValueOf (Lisp.Number Number.Real)    y) = pure $ real $ op x y
    opToLispOp (Just _)  (Just op) Nothing     (ValueOf (Lisp.Number Number.Real)    x)   (ValueOf (Lisp.Number Number.Integer) y) = pure $ real $ op x (cast y)
    opToLispOp (Just _)  (Just _)  Nothing     (ValueOf (Lisp.Number Number.Integer) _) y@(ValueOf (Lisp.Number Number.Complex) _) = collectThrow (TypeMismatch (Lisp.Number Number.Integer) y)
    opToLispOp (Just _)  (Just op) Nothing     (ValueOf (Lisp.Number Number.Integer) x)   (ValueOf (Lisp.Number Number.Real)    y) = pure $ real $ op (cast x) y
    opToLispOp (Just op) (Just _)  Nothing     (ValueOf (Lisp.Number Number.Integer) x)   (ValueOf (Lisp.Number Number.Integer) y) = pure $ integer $ op x y
    opToLispOp (Just _)  (Just _)  (Just op)   (ValueOf (Lisp.Number Number.Complex) x)   (ValueOf (Lisp.Number Number.Complex) y) = pure $ complex $ op (cast x) y
    opToLispOp (Just _)  (Just _)  (Just op)   (ValueOf (Lisp.Number Number.Complex) x)   (ValueOf (Lisp.Number Number.Real)    y) = pure $ complex $ op (cast x) (cast y)
    opToLispOp (Just _)  (Just _)  (Just op)   (ValueOf (Lisp.Number Number.Complex) x)   (ValueOf (Lisp.Number Number.Integer) y) = pure $ complex $ op (cast x) (cast y)
    opToLispOp (Just _)  (Just _)  (Just op)   (ValueOf (Lisp.Number Number.Real)    x)   (ValueOf (Lisp.Number Number.Complex) y) = pure $ complex $ op (cast x) y
    opToLispOp (Just _)  (Just op) (Just _)    (ValueOf (Lisp.Number Number.Real)    x)   (ValueOf (Lisp.Number Number.Real)    y) = pure $ real $ op x y
    opToLispOp (Just _)  (Just op) (Just _)    (ValueOf (Lisp.Number Number.Real)    x)   (ValueOf (Lisp.Number Number.Integer) y) = pure $ real $ op x (cast y)
    opToLispOp (Just _)  (Just _)  (Just op)   (ValueOf (Lisp.Number Number.Integer) x)   (ValueOf (Lisp.Number Number.Complex) y) = pure $ complex $ op (cast x) y
    opToLispOp (Just _)  (Just op) (Just _)    (ValueOf (Lisp.Number Number.Integer) x)   (ValueOf (Lisp.Number Number.Real)    y) = pure $ real $ op (cast x) y
    opToLispOp (Just op) (Just _)  (Just _)    (ValueOf (Lisp.Number Number.Integer) x)   (ValueOf (Lisp.Number Number.Integer) y) = pure $ integer $ op x y
    opToLispOp _         _         _         x                                            (ValueOf (Lisp.Number _)              _) = collectThrow {a=Lisp.Value} (TypeMismatchNumber x)
    opToLispOp _         _         _           (ValueOf (Lisp.Number _)              _) y                                          = collectThrow {a=Lisp.Value} (TypeMismatchNumber y)
    opToLispOp _         _         _         x                                          y                                          = collectThrow {a=Lisp.Value} (TypeMismatchNumber x) *>
                                                                                                                                     collectThrow {a=Lisp.Value} (TypeMismatchNumber x)
    private
    foldMLispBinOp :
      (Successable m Interpreter.Error, Monad n, Successable n (ts : List Interpreter.Error ** NonEmpty ts)) =>
      (Lisp.Value -> Lisp.Value -> Interpreter {m} {n} Lisp.Value) ->
      List Lisp.Value -> Interpreter {m} {n} Lisp.Value
    foldMLispBinOp f (x :: xs@(_ :: _)) = foldlM f x xs
    foldMLispBinOp _ xs = collectThrow $ NumArgs GT 2 xs

    private
    lispBinOp :
      (Successable m Interpreter.Error, Monad n, Successable n (ts : List Interpreter.Error ** NonEmpty ts)) =>
      (Lisp.Value -> Lisp.Value -> Interpreter {m} {n} Lisp.Value) ->
      List.List Lisp.Value -> Interpreter {m} {n} Lisp.Value
    lispBinOp f [x, y] = f x y
    lispBinOp _ xs = collectThrow $ NumArgs EQ 2 xs

    export
    primitivesEnv : (Successable m Interpreter.Error, Monad n, Successable n (ts : List Interpreter.Error ** NonEmpty ts)) =>
      SortedMap String (List Lisp.Value -> Interpreter {m} {n} Lisp.Value)
    primitivesEnv = fromList
      [ ("+", foldMLispBinOp $ opToLispOp (Just (+)) (Just (+)) (Just (+)))
      , ("-", foldMLispBinOp $ opToLispOp (Just (-)) (Just (-)) (Just (-)))
      , ("*", foldMLispBinOp $ opToLispOp (Just (*)) (Just (*)) (Just (*)))
      , ("/", foldMLispBinOp $ opToLispOp Nothing (Just (/)) (Just (/)))
      -- , ("remainder", lispBinOp $ \vx, vy => do
      --     y <- collect 0 (valueToInteger vy)
      --     if y == 0
      --       then collectThrow ZeroDivision
      --       else do
      --         x <- collect 0 (valueToInteger vx)
      --         pure $ integer $ assert_total (mod x y))
      ]

    export
    envLookup :
      (Successable m Interpreter.Error, Monad n, Successable n (ts : List Interpreter.Error ** NonEmpty ts)) =>
      String -> Interpreter {m} {n} (List Lisp.Value -> Interpreter {m} {n} Lisp.Value)
    envLookup name with (SortedMap.lookup name (primitivesEnv {m} {n}))
      | Nothing = collect (const $ pure neutral) $ throw $ UnboundVar name
      | Just x = pure x

  namespace repl
    eval : (Successable m Interpreter.Error, Monad n, Successable n (ts : List Interpreter.Error ** NonEmpty ts)) =>
      Lisp.Value -> Interpreter {m} {n} Lisp.Value
    eval (ValueOf Lisp.List [ValueOf Lisp.Atom "quote", ls]) = pure ls
    eval (ValueOf Lisp.List (ValueOf Lisp.Atom fname :: args)) = do
      f <- envLookup fname
      args' <- traverse (assert_total eval) args
      f args'
    eval val = pure val

private
test : Lisp.Value -> Either (ts: List.List Error ** NonEmpty ts) Lisp.Value
test = runCatchCollect {m = Either Error} {n = Either (ts: List.List Error ** NonEmpty ts)} . eval

private
examples : List Lisp.Value
examples =
  [ Util.quote $ Util.list [Util.string "aaa", Util.string "bbb"]
  , Util.list [Util.atom "+", Util.list [Util.string "aaa", Util.string "bbb"] ]
  , Util.list [Util.atom "+", Util.string "aaa", Util.string "bbb" ]
  , Util.list [Util.atom "+", integer 1, integer 2, integer 3 ]
  -- , Util.list [Util.atom "quotient", integer   13,  integer   4 ]
  -- , Util.list [Util.atom "quotient", integer (-13), integer   4 ]
  -- , Util.list [Util.atom "quotient", integer   13,  integer (-4) ]
  -- , Util.list [Util.atom "quotient", integer (-13), integer (-4) ]
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
