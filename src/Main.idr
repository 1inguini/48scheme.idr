module Main

import Data.Complex
import Scheme.Exception

%default total

ComplexD : Type
ComplexD = Complex Double

||| Number Type for LispVal
data LispNumber
  = Complex (ComplexD)
  | Real Double
  | Integer Integer

data LispVal
  = Atom String
  | List (List LispVal)
  | DottedList (List LispVal) LispVal
  | Number LispNumber
  | String String
  | Bool Bool

main : IO ()
main = do
  print "Hello, world!"
