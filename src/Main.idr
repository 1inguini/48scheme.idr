module Main

import Pruviloj
import Control.Catchable
import Derive.Show
import Data.Primitives.Views
import Data.Complex
import Data.SortedMap as SortedMap
-- import Scheme.Exception
import Scheme.CatchCollect

%default total
%language ElabReflection

implementation Cast a a where
  cast = id

ComplexD : Type
ComplexD = Complex Double

implementation Cast Integer ComplexD where
  cast = (:+ 0) . cast

implementation Cast Double ComplexD where
  cast = (:+ 0)

namespace Lisp
  ||| Number Type for LispVal
  data LispNumber
    = Complex ComplexD
    | Real Double
    | Integer Integer

  %runElab deriveShow `{LispNumber}

  data LispVal
    = Atom String
    | List (List LispVal)
    | DottedList (List LispVal) LispVal
    | Number LispNumber
    | String String
    | Bool Bool

  implementation Eq LispVal where
    (==) (Lisp.List []) (Lisp.List []) = True
    (==) _ _ = False

  showLispVal : LispVal -> String
  showLispVal (Lisp.Atom atm) = atm
  showLispVal (Lisp.List ls) = "(" <+> unwords (assert_total showLispVal <$> ls) <+> ")"
  showLispVal (Lisp.DottedList ls x) =
    "(" <+> unwords (assert_total showLispVal <$> ls) <+> assert_total (showLispVal x) <+> ")"
  showLispVal (Lisp.Number num) = show num
  showLispVal (Lisp.String str) = "\"" <+> str <+> "\""
  showLispVal (Lisp.Bool True) = "#t"
  showLispVal (Lisp.Bool False) = "#f"

  implementation Show LispVal where
    show = showLispVal

  implementation Semigroup LispVal where
    (<+>) x y = Lisp.List $ toList x <+> toList y
      where
        toList : LispVal -> List LispVal
        toList (Lisp.List ls) = ls
        toList val = [val]

  implementation Monoid LispVal where
    neutral = Lisp.List []

  data Error' lisp
    = NumArgs Ordering Nat (List lisp)
    | TypeMismatch String lisp
    | BadSpecialForm String lisp
    | UnboundVar String
    | ZeroDivision
    | Default String

  Error : Type
  Error = Error' LispVal

  Interpreter : (Successable m Lisp.Error, Monad n, Successable n (ts : List Lisp.Error ** NonEmpty ts)) =>
    Type -> Type
  Interpreter {m} {n} a = CatchCollect {m} {n} {t = Lisp.Error} a

  quote : LispVal -> LispVal
  quote ls = Lisp.List [Lisp.Atom "quote", ls]

  integer : Integer -> LispVal
  integer = Lisp.Number . Lisp.Integer

  real : Double -> LispVal
  real = Lisp.Number . Lisp.Real

  complex : ComplexD -> LispVal
  complex = Lisp.Number . Lisp.Complex

%runElab deriveShow `{Ordering}
%runElab deriveShow `{Lisp.Error'}

implementation Cast LispNumber ComplexD where
  cast (Lisp.Complex x) = x
  cast (Lisp.Real x) = cast x
  cast (Lisp.Integer x) = cast x

lispNumToDouble :
  (Monad m, Catchable m Lisp.Error) =>
  LispNumber -> m Double
lispNumToDouble (Lisp.Complex (x :+ 0.0)) = pure x
lispNumToDouble x@(Lisp.Complex _) = throw $ TypeMismatch "Real" (Lisp.Number x)
lispNumToDouble (Lisp.Real x) = pure x
lispNumToDouble (Lisp.Integer x) = pure $ cast x

lispNumToInteger :
  (Monad m, Catchable m Lisp.Error) =>
  LispNumber -> m Integer
lispNumToInteger x@(Lisp.Complex _) = throw $ TypeMismatch "Integer" (Lisp.Number x)
lispNumToInteger x@(Lisp.Real _) = throw $ TypeMismatch "Integer" (Lisp.Number x)
lispNumToInteger (Lisp.Integer x) = pure x

hasImplementation : (constraint : Type) ->
  { default (| Just %implementation, Nothing |) impl : Maybe constraint } ->
  Maybe constraint
hasImplementation _ {impl} = impl

namespace repl

  private
  cLispNumThrow : (Successable m Lisp.Error, Monad n, Successable n (ts : List Lisp.Error ** NonEmpty ts)) =>
    Lisp.Error -> Interpreter {m} {n} LispNumber
  cLispNumThrow = collect (Lisp.Integer 0) . throw {m}

  private
  cThrowTyMComplex : (Successable m Lisp.Error, Monad n, Successable n (ts : List Lisp.Error ** NonEmpty ts)) =>
    LispNumber -> Interpreter {m} {n} LispNumber
  cThrowTyMComplex = cLispNumThrow . TypeMismatch "Complex" . Lisp.Number

  private
  cThrowTyMReal : (Successable m Lisp.Error, Monad n, Successable n (ts : List Lisp.Error ** NonEmpty ts)) =>
    LispNumber -> Interpreter {m} {n} LispNumber
  cThrowTyMReal = cLispNumThrow . TypeMismatch "Real" . Lisp.Number

  private
  cThrowTyMInteger : (Successable m Lisp.Error, Monad n, Successable n (ts : List Lisp.Error ** NonEmpty ts)) =>
    LispNumber -> Interpreter {m} {n} LispNumber
  cThrowTyMInteger = cLispNumThrow . TypeMismatch "Integer" . Lisp.Number

  opToLispNumOp : (Successable m Lisp.Error, Monad n, Successable n (ts : List Lisp.Error ** NonEmpty ts)) =>
    (Maybe (Integer -> Integer -> Integer)) ->
    (Maybe (Double -> Double -> Double)) ->
    (Maybe (ComplexD -> ComplexD -> ComplexD)) ->
    LispNumber -> LispNumber -> Interpreter {m} {n} LispNumber
  --         Integer   Real      ComplexD
  opToLispNumOp Nothing   Nothing   Nothing   x                  y                  = cLispNumThrow $ Default "Bad primitive"
  opToLispNumOp Nothing   Nothing   (Just op) x                  y                  = pure $ Lisp.Complex $ op (cast x) (cast y)
  opToLispNumOp Nothing   (Just op) Nothing   x@(Lisp.Complex _) y@(Lisp.Complex _) = cThrowTyMReal x *> cThrowTyMReal y
  opToLispNumOp Nothing   (Just op) Nothing   x@(Lisp.Complex _)   (Lisp.Real    _) = cThrowTyMReal x
  opToLispNumOp Nothing   (Just op) Nothing   x@(Lisp.Complex _) y@(Lisp.Integer _) = cThrowTyMInteger x *> cThrowTyMReal y
  opToLispNumOp Nothing   (Just op) Nothing     (Lisp.Real    _) y@(Lisp.Complex _) = cThrowTyMReal y
  opToLispNumOp Nothing   (Just op) Nothing     (Lisp.Real    x)   (Lisp.Real    y) = pure $ Lisp.Real $ op x y
  opToLispNumOp Nothing   (Just op) Nothing     (Lisp.Real    x)   (Lisp.Integer y) = pure $ Lisp.Real $ op x (cast y)
  opToLispNumOp Nothing   (Just op) Nothing     (Lisp.Integer _) y@(Lisp.Complex _) = cThrowTyMInteger y
  opToLispNumOp Nothing   (Just op) Nothing     (Lisp.Integer x)   (Lisp.Real    y) = pure $ Lisp.Real $ op (cast x) y
  opToLispNumOp Nothing   (Just op) Nothing     (Lisp.Integer x)   (Lisp.Integer y) = pure $ Lisp.Real $ op (cast x) (cast y)
  opToLispNumOp Nothing   (Just _)  (Just op)   (Lisp.Complex x)   (Lisp.Complex y) = pure $ Lisp.Complex $ op x y
  opToLispNumOp Nothing   (Just _)  (Just op)   (Lisp.Complex x)   (Lisp.Real    y) = pure $ Lisp.Complex $ op x (cast y)
  opToLispNumOp Nothing   (Just _)  (Just op)   (Lisp.Complex x)   (Lisp.Integer y) = pure $ Lisp.Complex $ op x (cast y)
  opToLispNumOp Nothing   (Just _)  (Just op)   (Lisp.Real    x)   (Lisp.Complex y) = pure $ Lisp.Complex $ op (cast x) y
  opToLispNumOp Nothing   (Just op) (Just _)    (Lisp.Real    x)   (Lisp.Real    y) = pure $ Lisp.Real $ op x y
  opToLispNumOp Nothing   (Just op) (Just _)    (Lisp.Real    x)   (Lisp.Integer y) = pure $ Lisp.Real $ op x (cast y)
  opToLispNumOp Nothing   (Just _)  (Just op)   (Lisp.Integer x)   (Lisp.Complex y) = pure $ Lisp.Complex $ op (cast x) y
  opToLispNumOp Nothing   (Just op) (Just _)    (Lisp.Integer x)   (Lisp.Real    y) = pure $ Lisp.Real $ op (cast x) y
  opToLispNumOp Nothing   (Just op) (Just _)    (Lisp.Integer x)   (Lisp.Integer y) = pure $ Lisp.Real $ op (cast x) (cast y)
  opToLispNumOp (Just _)  Nothing   Nothing   x@(Lisp.Complex _) y@(Lisp.Complex _) = cThrowTyMInteger x *> cThrowTyMInteger y
  opToLispNumOp (Just _)  Nothing   Nothing   x@(Lisp.Complex _) y@(Lisp.Real    _) = cThrowTyMInteger x *> cThrowTyMInteger y
  opToLispNumOp (Just _)  Nothing   Nothing   x@(Lisp.Complex _)   (Lisp.Integer _) = cThrowTyMInteger x
  opToLispNumOp (Just _)  Nothing   Nothing   x@(Lisp.Real    _) y@(Lisp.Complex _) = cThrowTyMInteger x *> cThrowTyMInteger y
  opToLispNumOp (Just _)  Nothing   Nothing   x@(Lisp.Real    _) y@(Lisp.Real    _) = cThrowTyMInteger x *> cThrowTyMInteger y
  opToLispNumOp (Just _)  Nothing   Nothing   x@(Lisp.Real    _)   (Lisp.Integer _) = cThrowTyMInteger x
  opToLispNumOp (Just _)  Nothing   Nothing     (Lisp.Integer _) y@(Lisp.Complex _) = cThrowTyMInteger y
  opToLispNumOp (Just _)  Nothing   Nothing     (Lisp.Integer _) y@(Lisp.Real    _) = cThrowTyMInteger y
  opToLispNumOp (Just op) Nothing   Nothing     (Lisp.Integer x)   (Lisp.Integer y) = pure $ Lisp.Integer $ op x y
  opToLispNumOp (Just _)  Nothing   (Just op)   (Lisp.Complex x)   (Lisp.Complex y) = pure $ Lisp.Complex $ op x y
  opToLispNumOp (Just _)  Nothing   (Just op)   (Lisp.Complex x)   (Lisp.Real    y) = pure $ Lisp.Complex $ op x (cast y)
  opToLispNumOp (Just _)  Nothing   (Just op)   (Lisp.Complex x)   (Lisp.Integer y) = pure $ Lisp.Complex $ op x (cast y)
  opToLispNumOp (Just _)  Nothing   (Just op)   (Lisp.Real    x)   (Lisp.Complex y) = pure $ Lisp.Complex $ op (cast x) y
  opToLispNumOp (Just _)  Nothing   (Just op)   (Lisp.Real    x)   (Lisp.Real    y) = pure $ Lisp.Complex $ op (cast x) (cast y)
  opToLispNumOp (Just _)  Nothing   (Just op)   (Lisp.Real    x)   (Lisp.Integer y) = pure $ Lisp.Complex $ op (cast x) (cast y)
  opToLispNumOp (Just _)  Nothing   (Just op)   (Lisp.Integer x)   (Lisp.Complex y) = pure $ Lisp.Complex $ op (cast x) y
  opToLispNumOp (Just _)  Nothing   (Just op)   (Lisp.Integer x)   (Lisp.Real    y) = pure $ Lisp.Complex $ op (cast x) (cast y)
  opToLispNumOp (Just op) Nothing   (Just _)    (Lisp.Integer x)   (Lisp.Integer y) = pure $ Lisp.Integer $ op x y
  opToLispNumOp (Just _)  (Just _)  Nothing   x@(Lisp.Complex _) y@(Lisp.Complex _) = cThrowTyMReal x *> cThrowTyMReal y
  opToLispNumOp (Just _)  (Just _)  Nothing   x@(Lisp.Complex _) y@(Lisp.Real    _) = cThrowTyMReal x
  opToLispNumOp (Just _)  (Just _)  Nothing   x@(Lisp.Complex _) y@(Lisp.Integer _) = cThrowTyMInteger x
  opToLispNumOp (Just _)  (Just _)  Nothing     (Lisp.Real    _) y@(Lisp.Complex _) = cThrowTyMReal y
  opToLispNumOp (Just _)  (Just op) Nothing     (Lisp.Real    x)   (Lisp.Real    y) = pure $ Lisp.Real $ op x y
  opToLispNumOp (Just _)  (Just op) Nothing     (Lisp.Real    x)   (Lisp.Integer y) = pure $ Lisp.Real $ op x (cast y)
  opToLispNumOp (Just _)  (Just _)  Nothing     (Lisp.Integer _) y@(Lisp.Complex _) = cThrowTyMInteger y
  opToLispNumOp (Just _)  (Just op) Nothing     (Lisp.Integer x)   (Lisp.Real    y) = pure $ Lisp.Real $ op (cast x) y
  opToLispNumOp (Just op) (Just _)  Nothing     (Lisp.Integer x)   (Lisp.Integer y) = pure $ Lisp.Integer $ op x y
  opToLispNumOp (Just _)  (Just _)  (Just op)   (Lisp.Complex x)   (Lisp.Complex y) = pure $ Lisp.Complex $ op (cast x) y
  opToLispNumOp (Just _)  (Just _)  (Just op)   (Lisp.Complex x)   (Lisp.Real    y) = pure $ Lisp.Complex $ op (cast x) (cast y)
  opToLispNumOp (Just _)  (Just _)  (Just op)   (Lisp.Complex x)   (Lisp.Integer y) = pure $ Lisp.Complex $ op (cast x) (cast y)
  opToLispNumOp (Just _)  (Just _)  (Just op)   (Lisp.Real    x)   (Lisp.Complex y) = pure $ Lisp.Complex $ op (cast x) y
  opToLispNumOp (Just _)  (Just op) (Just _)    (Lisp.Real    x)   (Lisp.Real    y) = pure $ Lisp.Real $ op x y
  opToLispNumOp (Just _)  (Just op) (Just _)    (Lisp.Real    x)   (Lisp.Integer y) = pure $ Lisp.Real $ op x (cast y)
  opToLispNumOp (Just _)  (Just _)  (Just op)   (Lisp.Integer x)   (Lisp.Complex y) = pure $ Lisp.Complex $ op (cast x) y
  opToLispNumOp (Just _)  (Just op) (Just _)    (Lisp.Integer x)   (Lisp.Real    y) = pure $ Lisp.Real $ op (cast x) y
  opToLispNumOp (Just op) (Just _)  (Just _)    (Lisp.Integer x)   (Lisp.Integer y) = pure $ Lisp.Integer $ op x y

  -- opToLispNumOp (Just op) _         _  (Lisp.Integer x) (Lisp.Integer y) = Lisp.Integer $ op (cast x) (cast y)
  -- opToLispNumOp Nothing   (Just op) _  (Lisp.Integer x) (Lisp.Integer y) = Lisp.Real    $ op (cast x) (cast y)
  -- opToLispNumOp Nothing   Nothing   op (Lisp.Integer x) (Lisp.Integer y) = Lisp.Complex $ op (cast x) (cast y)
  -- opToLispNumOp _         (Just op) _  (Lisp.Integer x) (Lisp.Real    y) = Lisp.Real    $ op (cast x) (cast y)
  -- opToLispNumOp _         Nothing   op (Lisp.Integer x) (Lisp.Real    y) = Lisp.Complex $ op (cast x) (cast y)
  -- opToLispNumOp _         _         op (Lisp.Integer x) (Lisp.Complex y) = Lisp.Complex $ op (cast x) (cast y)
  -- opToLispNumOp _         (Just op) _  (Lisp.Real    x) (Lisp.Integer y) = Lisp.Real    $ op (cast x) (cast y)
  -- opToLispNumOp _         Nothing   op (Lisp.Real    x) (Lisp.Integer y) = Lisp.Complex $ op (cast x) (cast y)
  -- opToLispNumOp _         (Just op) _  (Lisp.Real    x) (Lisp.Real    y) = Lisp.Real    $ op (cast x) (cast y)
  -- opToLispNumOp _         _         op (Lisp.Real    x) (Lisp.Real    y) = Lisp.Complex $ op (cast x) (cast y)
  -- opToLispNumOp _         _         op (Lisp.Real    x) (Lisp.Complex y) = Lisp.Complex $ op (cast x) (cast y)
  -- opToLispNumOp _         _         op (Lisp.Complex x) y                = Lisp.Complex $ op (cast x) (cast y)

  lispNumOpToLispOp : (Successable m Lisp.Error, Monad n, Successable n (ts : List Lisp.Error ** NonEmpty ts)) =>
    (LispNumber -> LispNumber -> Interpreter {m} {n} LispNumber) ->
    LispVal -> LispVal -> Lisp.Interpreter {m} {n} LispVal
  lispNumOpToLispOp op (Lisp.Number x) (Lisp.Number y) = Lisp.Number <$> op x y
  lispNumOpToLispOp _ x y = collectThrow {a = LispVal} (TypeMismatch "Number" x) *> collectThrow (TypeMismatch "Number" y)

  foldMLispBinOp : (Successable m Lisp.Error, Monad n, Successable n (ts : List Lisp.Error ** NonEmpty ts)) =>
    (LispVal -> LispVal -> Lisp.Interpreter {m} {n} LispVal) ->
    List.List LispVal -> Lisp.Interpreter {m} {n} LispVal
  foldMLispBinOp f (x :: xs@(_ :: _)) = foldlM f x xs
  foldMLispBinOp _ xs = collectThrow $ NumArgs GT 2 xs

  lispBinOp : (Successable m Lisp.Error, Monad n, Successable n (ts : List Lisp.Error ** NonEmpty ts)) =>
    (LispVal -> LispVal -> Lisp.Interpreter {m} {n} LispVal) ->
    List.List LispVal -> Lisp.Interpreter {m} {n} LispVal
  lispBinOp f [x, y] = f x y
  lispBinOp _ xs = collectThrow $ NumArgs EQ 2 xs

  lispRem : (Successable m Lisp.Error, Monad n, Successable n (ts : List Lisp.Error ** NonEmpty ts)) =>
    LispNumber -> LispNumber -> Interpreter {m} {n} LispNumber
  lispRem (Lisp.Integer x) (Lisp.Integer y) with (divides x y)
    lispRem (Lisp.Integer ((y * div) + rem)) (Lisp.Integer y) | (DivBy _) = pure $ Lisp.Integer rem
    lispRem _ _ | (DivByZero) = cLispNumThrow ZeroDivision
  lispRem x y = let err = cLispNumThrow . TypeMismatch "Integer" . Lisp.Number in err x *> err y

  primitivesEnv : (Successable m Lisp.Error, Monad n, Successable n (ts : List Lisp.Error ** NonEmpty ts)) =>
    SortedMap String (List LispVal -> Lisp.Interpreter {m} {n} LispVal)
  primitivesEnv = fromList
    [ ("+", foldMLispBinOp $ lispNumOpToLispOp $ opToLispNumOp (Just (+)) (Just (+)) (Just (+)))
    , ("-", foldMLispBinOp $ lispNumOpToLispOp $ opToLispNumOp (Just (-)) (Just (-)) (Just (-)))
    , ("*", foldMLispBinOp $ lispNumOpToLispOp $ opToLispNumOp (Just (*)) (Just (*)) (Just (*)))
    , ("/", foldMLispBinOp $ lispNumOpToLispOp $ opToLispNumOp Nothing (Just (/)) (Just (/)))
    -- , ("modulo", lispBinOp $ lispNumOpToLispOp $ opToLispNumOp (Just mod) Nothing Nothing)
    , ("remainder", lispBinOp $ lispNumOpToLispOp lispRem)
    ]

  envLookup : (Successable m Lisp.Error, Monad n, Successable n (ts : List Lisp.Error ** NonEmpty ts)) =>
              String -> Lisp.Interpreter {m} {n} (List LispVal -> Lisp.Interpreter {m} {n} LispVal)
  envLookup name with (SortedMap.lookup name (primitivesEnv {m} {n}))
    | Nothing = collect (const $ pure neutral) $ throw $ UnboundVar name
    | Just x = pure x

  eval : (Successable m Lisp.Error, Monad n, Successable n (ts : List Lisp.Error ** NonEmpty ts)) =>
    LispVal -> Lisp.Interpreter {m} {n} LispVal
  eval (Lisp.List [Lisp.Atom "quote", ls]) = pure ls
  eval (Lisp.List (Lisp.Atom fname :: args)) = do
    f <- envLookup fname
    args' <- traverse (assert_total eval) args
    f args'
  eval val = pure val

test : List.List $ Lisp.Interpreter {m = Either Error} {n = Either (ts: List.List Error ** NonEmpty ts)} LispVal
test = eval <$>
  [ Lisp.quote $ Lisp.List [Lisp.String "aaa", Lisp.String "bbb"]
  , Lisp.List [Lisp.Atom "+", Lisp.List [Lisp.String "aaa", Lisp.String "bbb"] ]
  , Lisp.List [Lisp.Atom "+", Lisp.String "aaa", Lisp.String "bbb" ]
  , Lisp.List [Lisp.Atom "+", integer 1, integer 2, integer 3 ]
  , Lisp.List [Lisp.Atom "modulo", integer 2, integer 3 ]
  ]

main : IO ()
main = ?main

   -- do
   --  x <- MkErrCollector ["error : 1"] "1" `catch` \errs => do
   --    y <- throw ["error thrown"]
   --    z <- MkErrCollector ["error : 2"] "2"
   --    w <- throw (the (List String) errs)
   --    pure $ y <+> z <+> w
   --  pure $ x
