module Main

%default total

data Vect : Nat -> Type -> Type where
    Nil  : Vect Z a
    (::) : a -> Vect k a -> Vect (S k) a

data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where     
    Same : (num : Nat) -> EqNat num num

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat Z Z = pure $ Same 0
checkEqNat Z (S _) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = (\(Same x) => Same (S x)) <$> checkEqNat k j
    
exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = (\(Same _) => input) <$> checkEqNat m len

checkEqNat2 : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat2 Z Z = pure $ Refl
checkEqNat2 Z (S _) = Nothing
checkEqNat2 (S k) Z = Nothing
checkEqNat2 (S k) (S j) = cong <$> checkEqNat2 k j

exactLength2 : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength2 {m} len input = (\Refl => input) <$> checkEqNat2 m len

same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons = cong

same_lists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists Refl = cong

data ThreeEq : a -> b -> c -> Type where     
    Refl3 : ThreeEq x x x

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS x x x Refl3 = Refl3

main : IO ()
main = print $ 10