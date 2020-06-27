module Main
import Data.Vect
import Data.Vect.Quantifiers

%default total

showList : Show a => List a -> String
showList xs = "[" ++ show' xs ++ "]" where
    show' : List a -> String
    show' Nil        = ""
    show' (x :: Nil) = show x
    show' (x :: xs)  = show x ++ ", " ++ show' xs   

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
    
splitList : (input : List a) -> SplitList input
splitList input = splitListHelp input input
    where
        splitListHelp : List a -> (input : List a) -> SplitList input
        splitListHelp _ [] = SplitNil
        splitListHelp _ [x] = SplitOne
        splitListHelp (_ :: _ :: counter) (item :: items) = 
            case splitListHelp counter items of
                SplitNil => SplitOne
                SplitOne {x} => SplitPair [item] [x]
                SplitPair lefts rights => SplitPair (item :: lefts) rights
        splitListHelp _ items = SplitPair [] items

partial mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (lefts ++ rights) | (SplitPair lefts rights) = merge (mergeSort lefts) (mergeSort rights) 

data TakeN : List a -> Type where
    Fewer : TakeN xs
    Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

takeN : (n : Nat) -> (xs : List a) -> TakeN xs    
takeN Z xs = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) with (takeN k xs)
  takeN (S k) (x :: xs) | Fewer = Fewer
  takeN (S k) (x :: (n_xs ++ rest)) | (Exact n_xs) = Exact (x :: n_xs)

partial groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupByN n rest

half : Nat -> Nat 
half Z = Z
half (S Z) = Z
half (S (S x)) = S (half x)

halves : List a -> (List a, List a)  
halves xs = 
    let mid = half $ length xs
        taken = takeN mid xs
    in case taken of 
        Fewer => ([], xs)
        (Exact n_xs {rest}) => (n_xs, rest)

main : IO ()
main = pure ()