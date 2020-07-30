module Main
import Data.Vect;

%default total

myReverse : Vect n elem -> Vect n elem
myReverse [] = []
myReverse (x :: xs) = reverseProof $ myReverse xs ++ [x] where
    reverseProof : Vect (k + 1) elem -> Vect (S k) elem
    reverseProof {k} result = rewrite plusCommutative 1 k in result

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = rewrite plusZeroRightNeutral m in Refl
myPlusCommutes (S n) m with (myPlusCommutes n m, plusSuccRightSucc m n)
    | (p1, p2) = rewrite p1 in p2

reverseProof_xs : Vect ((S n) + len) a -> Vect (plus n (S len)) a
reverseProof_xs {n} {len} xs = rewrite sym (plusSuccRightSucc n len) in xs

myReverse' : Vect n elem -> Vect n elem
myReverse' = reverseImpl [] where
    reverseImpl : Vect n a -> Vect m a -> Vect (n+m) a
    reverseImpl {n} acc [] = rewrite plusZeroRightNeutral n in acc
    reverseImpl acc (x :: xs) = reverseProof_xs (reverseImpl (x::acc) xs)

main : IO ()
main = print $ 10
