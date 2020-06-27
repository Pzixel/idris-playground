module Main
import Data.Vect
import Data.Vect.Quantifiers

%default total

uniqueElements : Vect n a -> Type
uniqueElements xs = (е : a) -> (a, b : Elem e xs) -> a = b

-- IsSet : Nat -> Type -> Type 
-- IsSet  n t = (xs : Vect n t ** uniqueElements xs)

main : IO ()
main = pure ()