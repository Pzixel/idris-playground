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

data Set : Vect k a -> Type where 
    Empty : Set []
    WithElement : Set xs -> Not (Elem x xs) -> Set (x :: xs)

notInTailThenNowhere : (Elem value ys -> Void) -> Not (x = value) -> Elem value (x :: ys) -> Void
notInTailThenNowhere {x} {value=x} isNotElm notEq Here = notEq Refl
notInTailThenNowhere {x} {value} isNotElm notEq (There y) = isNotElm y

removeElemFromSet : (value : a) -> (xs : Vect (S n) a) -> Elem value xs -> Set xs -> (ys : Vect n a ** (Set ys, Not (Elem value ys)))
removeElemFromSet value (value :: xs) Here (WithElement isSet f) = (xs ** (isSet, f))
removeElemFromSet {n = (S k)} value (x :: xs) (There later) (WithElement isSet f) =
     let (ys ** (isResultSet, isNotElm)) = removeElemFromSet value xs later isSet
     in (x :: ys ** (WithElement isResultSet ?nonono, notInTailThenNowhere isNotElm ?noteqq))

main : IO ()
main = pure ()