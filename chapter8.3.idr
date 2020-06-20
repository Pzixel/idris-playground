module Main

%default total

data Vect : Nat -> Type -> Type where
    Nil  : Vect Z a
    (::) : a -> Vect k a -> Vect (S k) a

twoPlusTwoNotFive : 2 + 2 = 5 -> Void
twoPlusTwoNotFive Refl impossible

zeroNotSuc : (0=S k)->Void
zeroNotSuc Refl impossible

sucNotZero : (S k=0)->Void
sucNotZero Refl impossible

noSucc : ((k = j) -> Void) -> (S k = S j) -> Void
noSucc contra Refl = contra Refl

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Dec (num1 = num2)
checkEqNat Z Z = Yes Refl
checkEqNat Z (S _) = No zeroNotSuc
checkEqNat (S k) Z = No sucNotZero
checkEqNat (S k) (S j) = 
    case checkEqNat k j of 
        Yes p => Yes $ cong p
        No contra => No $ noSucc contra

vectInjective : {xs : Vect n a} -> {ys : Vect m b} -> x::xs = y::ys -> (x = y, xs = ys)
vectInjective Refl = (Refl, Refl)

headUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} -> (contra : (x = y) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
headUnequal contra prf = contra $ fst $ vectInjective prf

tailUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} -> (contra : (xs = ys) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
tailUnequal contra prf = contra $ snd $ vectInjective prf

DecEq a => DecEq (Vect n a) where 
    decEq [] [] = Yes Refl 
    decEq (x :: xs) (y :: ys) = case (decEq x y, decEq xs ys) of 
        (Yes Refl, Yes Refl) => Yes Refl 
        (No contraX, _) => No $ headUnequal contraX
        (_, No contraY) => No $ tailUnequal contraY

main : IO ()
main = print $ 10