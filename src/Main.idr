module Main

import Control.Catchable
import Control.Monad.Reader
import Derive.Eq
import Derive.Show
import Data.Vect
import Data.Vect.Views
import Data.Primitives.Views
import Data.Complex
import Data.SortedMap
-- import Scheme.Exception
import Scheme.CatchCollect

%default total
%language ElabReflection

implementation Semigroup () where
  (<+>) _ _ = ()

implementation Monoid () where
 neutral = ()

implementation Cast a a where
  cast = id

ComplexD : Type
ComplexD = Complex Double

implementation Cast Integer ComplexD where
  cast = (:+ 0) . cast

implementation Cast Double ComplexD where
  cast = (:+ 0)

%runElab deriveShow `{Ordering}

namespace Lisp

  namespace Number
    ||| Number Type for Lisp.Value
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

    representation : Number.Ty -> Type
    representation Number.Complex = ComplexD
    representation Number.Real    = Double
    representation Number.Integer = Integer

    fallbackFor : (nty : Number.Ty) -> Number.representation nty
    fallbackFor Number.Complex = 0 :+ 0
    fallbackFor Number.Real    = 0
    fallbackFor Number.Integer = 0

  Env : Type

  namespace Interpreter
    Error : Type

    Result : Type -> Type
    Result a = {m : Type -> Type} -> (Monad m, Catchable m Interpreter.Error) => m a

    interface (MonadReader Lisp.Env m, Catchable m Interpreter.Error) => Constraint (m : Type -> Type) where
    implementation (MonadReader Lisp.Env m, Catchable m Interpreter.Error) => Constraint m where

    EnvResult : Type -> Type
    EnvResult a = {m : Type -> Type} -> Interpreter.Constraint m => m a

  data Ty
    = Atom
    | List
    | DottedList
    | Number Number.Ty
    | String
    | Bool
    | Function Nat Bool -- number of arguments, whether it has variable length list argument or not
    | Unspecified -- type for unspecified value, such as (if #f "hello")

  %runElab deriveEq `{Lisp.Ty}
  mutual -- parsing fails without this
  %runElab deriveShow `{Lisp.Ty}

  mutual
    data Value : Type where
      ValueOf : (vty : Lisp.Ty) -> (val : representation vty) -> Lisp.Value

    Env = SortedMap String Lisp.Value

    primitiveTy : Nat -> Bool -> Type
    primitiveTy argNum True  = Vect argNum Lisp.Value -> List Lisp.Value -> Interpreter.Result Lisp.Value
    primitiveTy argNum False = Vect argNum Lisp.Value                    -> Interpreter.Result Lisp.Value

    data FunctionDefinition : (argNum : Nat) -> (hasRest : Bool) -> Type where
      PrimitiveFunction : {argNum : Nat} -> {hasRest : Bool} ->
        (primitive : primitiveTy argNum hasRest) -> FunctionDefinition argNum hasRest
      DefineFunction :
        (closure : Lisp.Env) ->
        (argIds : if hasRest then (Vect argNum String, String) else Vect argNum String) ->
        (body : Lisp.Value) -> FunctionDefinition argNum hasRest

    representation : Lisp.Ty -> Type
    representation Lisp.Atom                      = String
    representation Lisp.List                      = List Lisp.Value
    representation Lisp.DottedList                = (List Lisp.Value, Lisp.Value)
    representation (Lisp.Number nty)              = Number.representation nty
    representation Lisp.String                    = String
    representation Lisp.Bool                      = Bool
    representation (Lisp.Function argNum hasRest) = FunctionDefinition argNum hasRest
    representation Lisp.Unspecified               = ()

  getType : Lisp.Value -> Lisp.Ty
  getType (ValueOf lty _) = lty

  unValue : (wanted : Lisp.Ty) -> (v : Lisp.Value) -> {ok : wanted = getType v} ->
    representation wanted
  unValue wanted {ok} (ValueOf _ x) = rewrite ok in x

  lambdaString : String -> String -> String
  lambdaString formals body = concat {t = List}
      [ "(lambda (", formals, ")\n"
      , "  ", body, ")"
      ]

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
    show (ValueOf (Lisp.Function _ _) (PrimitiveFunction _)) = "#<primitive>"
    show (ValueOf (Lisp.Function _ False) (DefineFunction _ argIds body)) =
      lambdaString (unwords $ toList argIds) $
        assert_total $ show body
    show (ValueOf (Lisp.Function argNum True) (DefineFunction _ (argIds, restId) body)) =
      lambdaString (unwords (toList argIds) <+> " . " <+> restId) $
        assert_total $ show body
    show (ValueOf Lisp.Unspecified _) = "#<unspecified>"

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

    function : FunctionDefinition argNum hasRest -> Lisp.Value
    function {argNum} {hasRest} = ValueOf (Lisp.Function argNum hasRest)

    primitiveFunction : (argNum : Nat) -> (hasRest : Bool) ->
      primitiveTy argNum hasRest -> Lisp.Value
    primitiveFunction argNum hasRest primitive = function {argNum} {hasRest} $ PrimitiveFunction primitive

    unspecified : Lisp.Value
    unspecified = ValueOf Lisp.Unspecified ()

    quote : Lisp.Value -> Lisp.Value
    quote ls = list [atom "quote", ls]

  namespace Interpreter

    data Error
      = NumArgs Ordering Nat (List Lisp.Value)
      | TypeMismatch Lisp.Ty (Lisp.Value)
      | BadSpecialForm String (Lisp.Value)
      | UnboundVar String
      | ZeroDivision
      | Default String

    %runElab deriveShow `{Interpreter.Error}
    mutual

    Errors : Type
    Errors = List Interpreter.Error

    throwTypeMismatchNumber : Catchable m Interpreter.Error => Lisp.Value -> m a
    throwTypeMismatchNumber v =
      or (throw $ TypeMismatch (Lisp.Number Number.Integer) v) $
      or (throw $ TypeMismatch (Lisp.Number Number.Real) v) $
      throw $ TypeMismatch (Lisp.Number Number.Complex) v

    Interpreter : Catchable m Interpreter.Error => Type -> Type
    Interpreter {m} = ReaderT Lisp.Env m

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

    valueListToNumberRepresentationList : (Applicative m, Catchable m Interpreter.Error) =>
      (nty : Number.Ty) -> List Lisp.Value -> m (List (Number.representation nty))
    valueListToNumberRepresentationList nty vs = traverse (valueToNum nty) vs

    valueToVariable : (Applicative m, Catchable m Interpreter.Error) =>
      Lisp.Value -> m String
    valueToVariable (ValueOf Lisp.Atom var) = pure var
    valueToVariable v = throw $ TypeMismatch Lisp.Atom v

    lispBinOp : (Applicative m, Catchable m Interpreter.Error) =>
      (Lisp.Value -> Lisp.Value -> m Lisp.Value) ->
      List.List Lisp.Value -> m Lisp.Value

    lispBinOp f [x, y] = f x y
    lispBinOp _ xs = throw $ NumArgs EQ 2 xs

    natQuotient : Nat -> Nat -> Maybe Nat
    natQuotient dividend Z = Nothing
    natQuotient dividend divisor = Just $ quotHelper divisor 0
      where
        quotHelper : Nat -> Nat -> Nat
        quotHelper accm count =
          if lt accm dividend
          then assert_total $ quotHelper (accm + divisor) (S count)
          else count

    quotient : Integer -> Integer -> Maybe Integer
    quotient _ 0 = Nothing
    quotient dividend divisor with (dividend * divisor < 0)
      | False = cast <$> natQuotient (cast $ abs dividend) (cast $ abs divisor)
      | True = negate . cast <$> natQuotient (cast $ abs dividend) (cast $ abs divisor)

    remainder : Integer -> Integer -> Maybe Integer
    remainder dividend divisor = do
      quot <- quotient dividend divisor
      pure $ dividend - divisor * quot

    modulo : Integer -> Integer -> Maybe Integer
    modulo dividend divisor = do
      rem <- remainder dividend divisor
      pure $ rem + if dividend * divisor < 0 then divisor else 0

    OperatorDefinitions : Nat -> Type
    OperatorDefinitions len = Vect (S len)
      (nty : Number.Ty ** let ty = Number.representation nty in (ty -> ty -> ty, ty))

    opToValueListOp : (Applicative m, Catchable m Interpreter.Error) =>
      (nty : Number.Ty) -> let ty = Number.representation nty in (ty -> ty -> ty) -> ty -> List Lisp.Value -> m Lisp.Value
    opToValueListOp nty op seed vs = Util.number nty . foldl op seed <$> valueListToNumberRepresentationList nty vs

    makeNumValueOp :
      (definitions : OperatorDefinitions len) ->
      List Lisp.Value -> Interpreter.Result Lisp.Value
    makeNumValueOp definitions vs = foldl1 or $ map (\(nty ** (op, seed)) =>
      opToValueListOp nty op seed vs) definitions

    opToUnaryValueListOp : (Applicative m, Catchable m Interpreter.Error) =>
      (nty : Number.Ty) -> let ty = Number.representation nty in (ty -> ty -> ty) -> ty ->
      Lisp.Value -> List Lisp.Value -> m Lisp.Value
    opToUnaryValueListOp nty op seed v [] = (number nty . op seed) <$> valueToNum nty v
    opToUnaryValueListOp nty op _ v vs = map (number nty) $
      foldl op <$> valueToNum nty v <*> valueListToNumberRepresentationList nty vs

    makeUnaryNumValueOp :
      (definitions : OperatorDefinitions len) ->
      Vect 1 Lisp.Value -> List Lisp.Value -> Interpreter.Result Lisp.Value
    makeUnaryNumValueOp definitions [v] vs = foldl1 or $ map (\(nty ** (op, seed)) =>
      opToUnaryValueListOp nty op seed v vs) definitions

    maybeNumOpToBinValueOp : (nty : Number.Ty) ->
      (let ty = Number.representation nty in ty -> ty -> Maybe ty) ->
      Interpreter.Error ->
      Vect 2 Lisp.Value -> Interpreter.Result Lisp.Value
    maybeNumOpToBinValueOp nty op err [vx, vy] = do
      (x, y) <- MkPair <$> valueToNum nty vx <*> valueToNum nty vy
      maybe (throw err) (pure . number nty) $ op x y

    primitivesEnv : Env
    primitivesEnv = SortedMap.fromList
      [ ( "+"
        , primitiveFunction 0 True $ \_ => makeNumValueOp
          [ (Number.Integer ** ((+), 0))
          , (Number.Real    ** ((+), 0))
          , (Number.Complex ** ((+), 0))
          ]
        )
      , ( "*"
        , primitiveFunction 0 True $ \_ => makeNumValueOp
          [ (Number.Integer ** ((+), 1))
          , (Number.Real    ** ((+), 1))
          , (Number.Complex ** ((+), 1))
          ]
        )
      , ( "-"
        , primitiveFunction 1 True $ makeUnaryNumValueOp
          [ (Number.Integer ** ((-), 0))
          , (Number.Real    ** ((-), 0))
          , (Number.Complex ** ((-), 0))
          ]
        )
      , ( "/"
        , primitiveFunction 1 True $ makeUnaryNumValueOp
          [ (Number.Real    ** ((/), 1))
          , (Number.Complex ** ((/), 1))
          ]
        )
      , ( "quotient"
        , primitiveFunction 2 False $ maybeNumOpToBinValueOp Number.Integer quotient ZeroDivision
        )
      , ( "remainder"
        , primitiveFunction 2 False $ maybeNumOpToBinValueOp Number.Integer remainder ZeroDivision
        )
      , ( "modulo"
        , primitiveFunction 2 False $ maybeNumOpToBinValueOp Number.Integer modulo ZeroDivision
        )
      ]

  envLookup :
    String -> Interpreter.EnvResult Lisp.Value
  envLookup varName =
    ask >>= (maybe (throw $ UnboundVar varName) pure . SortedMap.lookup varName)

  namespace repl
    inserts : Foldable t => SortedMap k v -> t (k,v) -> SortedMap k v
    inserts = foldl (flip $ uncurry insert)

    plusMinusNeutral : (x : Nat) -> (y : Nat) -> {auto smaller : LTE x y} -> x + (y - x) = y
    plusMinusNeutral Z     Z = Refl
    plusMinusNeutral Z     (S k) = Refl
    plusMinusNeutral (S k) (S j) {smaller} = let smaller' = fromLteSucc smaller in
      rewrite eqSucc (k + (j - k)) j $ plusMinusNeutral k j in Refl

    mutual
      apply : FunctionDefinition argNum hasRest -> List Lisp.Value -> Interpreter.EnvResult Lisp.Value
      apply {argNum} {hasRest = False} (PrimitiveFunction f) args
        with (decEq argNum (length args))
        | Yes prf = f $ rewrite prf in fromList args
        | No _ = throw $ NumArgs EQ argNum args
      apply {argNum} {hasRest = True} (PrimitiveFunction f) fullArgs
        with (isLTE argNum $ length fullArgs)
        | Yes prf =
          let (args, rest) = Vect.splitAt {m=length fullArgs - argNum} argNum $
                rewrite plusMinusNeutral argNum (length fullArgs)
                in Vect.fromList fullArgs
          in f args $ toList rest
        | No _ = throw $ NumArgs GT argNum fullArgs
      apply {argNum} {hasRest = False} (DefineFunction closure argIds body) args
        with (decEq argNum (length args))
        | Yes prf =
            local (const $ inserts closure $ zip argIds $ rewrite prf in fromList args) $
              assert_total $ eval body
        | No _ = throw $ NumArgs EQ argNum args
      apply {argNum} {hasRest = True} (DefineFunction closure (argIds, restId) body) fullArgs
        with (isLTE argNum $ length fullArgs)
        | Yes prf =
          let (args, rest) = Vect.splitAt {m=length fullArgs - argNum} argNum $
                rewrite plusMinusNeutral argNum (length fullArgs)
                in Vect.fromList fullArgs
          in local (const $ inserts closure $ (restId, Util.list $ toList rest) :: zip argIds args) $
            assert_total $ eval body
        | No _ = throw $ NumArgs GT argNum fullArgs

      eval : Interpreter.Constraint m =>
        Lisp.Value -> m Lisp.Value
      eval (ValueOf Lisp.List [ValueOf Lisp.Atom "quote", ls]) = pure ls
      eval (ValueOf Lisp.List (ValueOf Lisp.Atom "quote" :: ls)) = throw $ NumArgs EQ 1 ls
      eval (ValueOf Lisp.List [ValueOf Lisp.Atom "lambda", ValueOf Lisp.List vArgIds, body]) = do
        argIds <- traverse valueToVariable vArgIds
        env <- ask
        pure $ function $ DefineFunction {hasRest = False} env (Vect.fromList argIds) body
      eval (ValueOf Lisp.List [ValueOf Lisp.Atom "lambda", ValueOf Lisp.DottedList (vArgIds, vRestId), body]) = do
        (argIds, restId) <- MkPair <$> traverse valueToVariable vArgIds <*> valueToVariable vRestId
        env <- ask
        pure $ function $ DefineFunction {hasRest = True} env (Vect.fromList argIds, restId) body
      eval (ValueOf Lisp.List [ValueOf Lisp.Atom "lambda", vRestId, body]) = do
        restId <- valueToVariable vRestId
        env <- ask
        pure $ function $ DefineFunction {hasRest = True} env ([], restId) body
      eval (ValueOf Lisp.List [ValueOf Lisp.Atom "if", vtest, consequent, alternate]) = do
        ValueOf Lisp.Bool test <- eval vtest
        | v => throw (TypeMismatch Lisp.Bool v)
        pure $ if test then consequent else alternate
      eval (ValueOf Lisp.List (ValueOf Lisp.Atom "if" :: ls)) =
        (*>) {a = ()} (throw $ NumArgs EQ 3 ls) (throw $ NumArgs EQ 2 ls)
      eval (ValueOf Lisp.List [ValueOf Lisp.Atom "if", vtest, consequent]) = do
        ValueOf Lisp.Bool test <- eval vtest
        | v => throw (TypeMismatch Lisp.Bool v)
        pure $ if test then consequent else unspecified
      eval (ValueOf Lisp.Atom var) = envLookup var
      eval (ValueOf Lisp.List (vFunc :: args)) = do
        ValueOf (Lisp.Function _ _) f <- eval vFunc
        | v => throw (TypeMismatch (Lisp.Function (length args) False) v)
        args' <- traverse (assert_total eval) args
        apply f args'
      eval val = pure val

test : Lisp.Value -> (String, Either Interpreter.Errors Lisp.Value)
test v = (show v, runCatchCollect $ flip runReaderT primitivesEnv $ eval v)

examples : List Lisp.Value
examples =
  [ Util.quote $ Util.list [Util.string "aaa", Util.string "bbb"]

  , Util.list [Util.atom "+", Util.list [Util.string "aaa", Util.string "bbb"]]
  , Util.list [Util.atom "+", Util.string "aaa", Util.string "bbb"]
  , Util.list [Util.atom "+", Util.string "aaa", Util.bool False, Util.string "ccc"]
  , Util.list [Util.atom "+", Util.integer 3, Util.integer 4]
  , Util.list [Util.atom "+", Util.integer 3]
  , Util.list [Util.atom "+"]

  , Util.list [Util.atom "*", Util.integer 4]
  , Util.list [Util.atom "*"]

  , Util.list [Util.atom "-", Util.string "aaa", Util.bool False, Util.string "ccc"]
  , Util.list [Util.atom "-", Util.integer 3, Util.integer 4]
  , Util.list [Util.atom "-", Util.integer 3, Util.integer 4, Util.integer 5]
  , Util.list [Util.atom "-", Util.integer 3]

  , Util.list [Util.atom "/", Util.integer 3, Util.integer 4]
  , Util.list [Util.atom "/", Util.integer 3, Util.integer 4, Util.integer 5]
  , Util.list [Util.atom "/", Util.integer 3]

  , Util.list [Util.atom "quotient", Util.integer   13,  Util.integer   4]
  , Util.list [Util.atom "quotient", Util.integer (-13), Util.integer   4]
  , Util.list [Util.atom "quotient", Util.integer   13,  Util.integer (-4)]
  , Util.list [Util.atom "quotient", Util.integer (-13), Util.integer (-4)]

  , Util.list [Util.atom "remainder", Util.integer   13,  Util.integer   4]
  , Util.list [Util.atom "remainder", Util.integer (-13), Util.integer   4]
  , Util.list [Util.atom "remainder", Util.integer   13,  Util.integer (-4)]
  , Util.list [Util.atom "remainder", Util.integer (-13), Util.integer (-4)]

  , Util.list [Util.atom "modulo", Util.integer   13,  Util.integer   4]
  , Util.list [Util.atom "modulo", Util.integer (-13), Util.integer   4]
  , Util.list [Util.atom "modulo", Util.integer   13,  Util.integer (-4)]
  , Util.list [Util.atom "modulo", Util.integer (-13), Util.integer (-4)]

  , Util.list
      [ Util.list [ Util.atom "lambda", Util.atom "x" , Util.atom "x" ]
      , Util.string "hello", Util.bool True
      ]
  , Util.list
      [ Util.list [Util.atom "lambda", Util.list [Util.atom "x", Util.atom "y"], Util.atom "x"]
      , Util.string "hello", Util.bool True
      ]
  , Util.list
      [ Util.list [Util.list [Util.atom "lambda", Util.atom "x", Util.atom "y"], Util.atom "x"]
      , Util.string "hello", Util.bool True, Util.real 12.3]
  , Util.list
      [ Util.list [Util.atom "lambda", Util.dottedList [Util.atom "x"] $ Util.atom "y", Util.atom "x"]
      , Util.string "hello"
      ]
  , Util.list
      [ Util.list [Util.atom "lambda", Util.dottedList [Util.atom "x"] $ Util.atom "y", Util.atom "x"]
      , Util.string "hello", Util.bool True
      ]
  , Util.list
      [ Util.list [Util.atom "lambda", Util.dottedList [Util.atom "x"] $ Util.atom "y", Util.atom "x"]
      , Util.string "hello", Util.bool True, Util.real 12.3
      ]
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
