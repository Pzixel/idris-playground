module Main
import Data.Vect
import Data.Vect.Quantifiers

%default total

data ListLast : List a -> Type where
    Empty : ListLast []
    NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

describeHelper : (input : List Int) -> (form : ListLast input) -> String
describeHelper [] Empty = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x)= "Non-empty, initial portion = " ++ show xs 

listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case listLast xs of 
    Empty => NonEmpty [] x
    (NonEmpty ys y) => NonEmpty (x :: ys) y

describeListEnd : List Int -> String
describeListEnd xs with (listLast xs)
  describeListEnd _ | Empty = "Empty"
  describeListEnd _ | (NonEmpty ys x) ="Non-empty, initial portion = " ++ show ys 

covering myReverse : List a -> List a
myReverse xs with (listLast xs)
  myReverse _ | Empty = []
  myReverse _ | (NonEmpty ys y) = (y :: myReverse ys)

data SplitList : List a -> Type where
    SplitNil : SplitList []
    SplitOne : SplitList [x]
    SplitPair : (lefts : List a) -> (rights : List a) -> SplitList (lefts ++ rights)

splitAtEmptyIsEmpty : splitAt n [] = ([], [])
splitAtEmptyIsEmpty = Refl
    
splitCorrect : {n : Nat} -> (xs : List a) -> (fst (splitAt n xs) ++ snd (splitAt n xs)) = xs
splitCorrect [] = ?splitCorrect_rhs_1
splitCorrect (x :: xs) = ?splitCorrect_rhs_2

half : Nat -> Nat 
half Z = Z
half (S Z) = Z
half (S (S x)) = S (half x)

splitList : (input : List a) -> SplitList input
splitList [] = SplitNil
splitList [x] = SplitOne
splitList xs = 
    let n = half $ length xs
        res = Prelude.List.splitAt n xs
    in rewrite sym (splitCorrect {n} xs) in SplitPair (fst res) (snd res)


-- partial mergeSort : Ord a => List a -> List a
-- mergeSort xs with (splitList xs)
--   mergeSort [] | SplitNil = []
--   mergeSort [x] | SplitOne = [x]
--   mergeSort (lefts ++ rights) | (SplitPair lefts rights) = merge (mergeSort lefts) (mergeSort rights) 


main : IO ()
main = pure ()