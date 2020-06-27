module Main
import Data.Vect
import Data.Vect.Quantifiers

%default total

uniqueElements : Vect n a -> Type
uniqueElements xs = (e : a) -> (x, y : Elem e xs) -> x = y

Set : Nat -> Type -> Type 
Set n t = (xs : Vect n t ** uniqueElements xs)

foo : Set 3 Int
foo = 
    let xs = [1,2,3] 
        bar = ?bar 
    in (xs ** bar)

main : IO ()
main = pure ()