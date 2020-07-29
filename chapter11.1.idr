module Main
import Data.List.Views
import Data.Vect
import Data.Vect.Views
import Data.Nat.Views
import Data.Bits

%default total

data InfList : Type -> Type where
    (::) : (value : elem) -> Inf (InfList elem) -> InfList elem
 
    
%name InfList xs, ys, zs

countFrom : Integer -> InfList Integer
countFrom x = x :: countFrom (x + 1)

getPrefix : (count : Nat) -> InfList ty -> List ty
getPrefix Z xs = []
getPrefix (S k) (x :: xs) = x :: getPrefix k xs

every_other : Stream a -> Stream a
every_other (_ :: (x :: xs)) = x :: every_other xs

Functor InfList where
    map func (x::xs) = func x :: map func xs

data Face = Heads | Tails

instance Show Face where
    show Heads = "Heads"
    show Tails = "Tails"

isOdd : Int -> Bool 
isOdd value = 
    let onePattern = bitAt (the (Fin 1) 0)
    in ((intToBits (cast value)) `Data.Bits.and` onePattern) == onePattern


coinFlips : Stream Int -> Stream Face
coinFlips (value :: xs) = (if isOdd value then Heads else Tails) :: coinFlips xs

main : IO ()
main = print $ take 10 (coinFlips [1..]) 