module Main
import Data.Vect
import Data.Vect.Quantifiers

%default total

data Set : Vect k a -> Type where 
    Empty : Set []
    WithElement : Set xs -> Not (Elem x xs) -> Set (x :: xs)

lem : Set (x::xs) -> Elem y xs -> Not (x=y)
lem (WithElement isSet f) el Refl = f el

mapAll : {p1, p2 : a -> Type} -> (f : {x : a} -> p1 x -> p2 x) -> All p1 xs -> All p2 xs
mapAll f  Nil     = Nil
mapAll f (ah::at) = f ah :: mapAll f at

map2All : {p1, p2, p3 : a -> Type} -> (f : {x : a} -> p1 x -> p2 x -> p3 x) -> All p1 xs -> All p2 xs -> All p3 xs
map2All f  Nil     Nil      = Nil
map2All f (ah::at) (bh::bt) = f ah bh :: map2All f at bt

nelTail : Not (Elem y (x::xs)) -> Not (Elem y xs)
nelTail ctra = ctra . There

nelLem : Not (Elem y (x::xs)) -> Not (Elem y ys) -> Not (Elem y (x::ys))
nelLem ctra1 ctra2  Here      = ctra1 Here
nelLem ctra1 ctra2 (There el) = ctra2 el

removeElemFromSet : (value : a) -> (xs : Vect (S n) a) -> Elem value xs -> Set xs -> (heads : Vect m a) -> All (\h => Not (Elem h xs)) heads
                 -> (ys : Vect n a ** (Set ys, All (\h => Not (Elem h ys)) heads, Not (Elem value ys)))
removeElemFromSet         value (value::xs)  Here            (WithElement isSet f) heads allh = (xs ** (isSet, mapAll nelTail allh, f))
removeElemFromSet {n=S k} value (x::xs)     (There later) sx@(WithElement isSet f) heads allh =
  let (ys ** (sys, nex::anh2, nel)) = removeElemFromSet value xs later isSet (x::heads) (f :: mapAll nelTail allh)
  in  (x::ys ** (WithElement sys nex, map2All nelLem allh anh2, neitherHereNorThere (lem sx later . sym) nel))

main : IO ()
main = pure ()