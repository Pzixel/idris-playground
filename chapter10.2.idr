module Main
import Data.List.Views
import Data.Vect
import Data.Vect.Views
import Data.Nat.Views

%default total

mergeSort : Ord a => List a -> List a
mergeSort xs with (splitRec xs)
    mergeSort [] | SplitRecNil = []
    mergeSort [x] | SplitRecOne = [x]
    mergeSort (lefts ++ rights) | (SplitRecPair lrec rrec) = merge (mergeSort lefts | lrec) (mergeSort rights | rrec) 

covering equalSuffix : Eq a => List a -> List a -> List a
equalSuffix xs ys with (snocList xs, snocList ys)
    equalSuffix _ _ | (Empty, Empty) = []
    equalSuffix _ _ | (Empty, Snoc y) = []
    equalSuffix _ _ | (Snoc x, Empty) = []
    equalSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc revx, Snoc revy) = 
        if x /= y then [] else (equalSuffix xs ys | (revx, revy)) ++ [x]

mergeSortV : Ord a => Vect n a -> Vect n a
mergeSortV xs with (splitRec xs)
    mergeSortV [] | SplitRecNil = []
    mergeSortV [x] | SplitRecOne = [x]
    mergeSortV (lefts ++ rights) | (SplitRecPair lrec rrec) = merge (mergeSortV lefts | lrec) (mergeSortV rights | rrec) 
    
toBinary : Nat -> String
toBinary k with (halfRec k) 
    toBinary Z | HalfRecZ = "0"
    toBinary (n + n) | (HalfRecEven rec) = (toBinary n | rec) ++ "0"
    toBinary (S (n + n)) | (HalfRecOdd rec) = (toBinary n | rec) ++ "1"

palindrome : List Char -> Bool    
palindrome s with (vList s) 
    palindrome [] | VNil = True
    palindrome [x] | VOne = True
    palindrome (x :: (xs ++ [y])) | (VCons rec) = x == y && (palindrome xs | rec)

main : IO ()
main = print $ mergeSort [1,4,5,2,3,4,7]