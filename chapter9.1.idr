module Main

%default total

data Vect : Nat -> Type -> Type where
    Nil  : Vect Z a
    (::) : a -> Vect k a -> Vect (S k) a

data Elem : a -> Vect k a -> Type where
    Here : Elem x (x :: xs)
    There : (later : Elem x xs) -> Elem x (y :: xs)

Uninhabited (Elem x []) where
    uninhabited _ impossible

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

removeElem : (value : a) -> (xs : Vect (S n) a) -> Elem value xs -> Vect n a
removeElem x (x :: xs) Here = xs
removeElem {n = (S k)} value (x :: xs) (There later) = x :: (removeElem value xs later)

removeElem_auto : (value : a) -> (xs : Vect (S n) a) -> {auto prf : Elem value xs} -> Vect n a
removeElem_auto value xs {prf} = removeElem value xs prf

notInHeadOrTail : (contraX : (value = x) -> Void) -> (contraXs : Elem value xs -> Void) -> Elem value (x :: xs) -> Void
notInHeadOrTail contraX contraXs Here = contraX Refl
notInHeadOrTail contraX contraXs (There later) = contraXs later

isElem : DecEq a => (value : a) -> (xs : Vect n a) -> Dec (Elem value xs)
isElem value [] = No uninhabited
isElem value (x :: xs) = case decEq value x of
    (Yes Refl) => Yes Here
    (No contraX) => case isElem value xs of
        (Yes x) => Yes $ There x
        (No contraXs) => No (notInHeadOrTail contraX contraXs)

data ElemList : a -> List a -> Type where
    HereList : ElemList x (x :: xs)
    ThereList : (later : ElemList x xs) -> ElemList x (y :: xs)

Uninhabited (ElemList x []) where
    uninhabited _ impossible

data Last : List a -> a -> Type where
    LastOne : Last [value] value
    LastCons : (prf : Last xs value) -> Last (x :: xs) value

Uninhabited (Last [] x) where
    uninhabited _ impossible

noLastIfNotEq : (contra : (value = x) -> Void) -> Last [x] value -> Void
noLastIfNotEq contra LastOne = contra Refl
noLastIfNotEq _ (LastCons prf) = uninhabited prf

notLastIfNotInTail : (contra : Last (y :: xs) value -> Void) -> Last (x :: (y :: xs)) value -> Void
notLastIfNotInTail contra (LastCons prf) = contra prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No uninhabited
isLast (x :: []) value = case decEq value x of
    (Yes Refl) => Yes LastOne
    (No contra) => No (noLastIfNotEq contra)
isLast (x :: y :: xs) value = case isLast (y :: xs) value of
    (Yes prf) => Yes $ LastCons prf
    (No contra) => No (notLastIfNotInTail contra)

main : IO ()
main = print $ 10
