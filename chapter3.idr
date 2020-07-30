module Main
import Debug.Trace
import Data.Vect;

-- infix  4 :+:

-- data Vect : Nat -> Type -> Type where
--    Nil  : Vect Z a
--    (:+:) : a -> Vect k a -> Vect (S k) a

-- testFunc : (Vect n a) -> (Vect m a) -> (n = m) -> Integer
-- testFunc _ _ _ = 50

-- foo : Integer
-- foo = let arr = (1 :+: (2 :+: (3 :+: Nil)))
--           arrWithFour = 4 :+: arr
--       in testFunc arr arr Refl

-- add : (a: Int) -> (b: Int) -> (c: Int, c >= a && c >= b)
-- add a b = (a + b, Refl)

palindrome : String -> Bool
palindrome s = s == reverse s

counts : String -> (Nat, Nat)
counts s = (length (words s), length s)

top_ten : Ord a => List a -> List a
top_ten = Prelude.List.take 10 . reverse . sort

over_length : Nat -> List String -> Nat
over_length n = length . filter (\x => length x > n)

allLengths : List String -> List Nat
allLengths [] = []
allLengths (x :: xs) = length x :: allLengths xs

insSort : (Ord elem) => Vect n elem -> Vect n elem
insSort [] = []
insSort (x :: xs) =
    let sortedXs = insSort xs
        position = findPosition x sortedXs
    in insertAt position x sortedXs
    where
        findPosition : (Ord elem) => elem -> Vect n elem -> Fin (S n)
        findPosition x xs = let maybeIndex = findIndex (\elm => x < elm) xs in
            fromMaybe last (weaken <$> maybeIndex)


transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = (const []) <$> range
transposeMat (x :: xs) =
    let transXs = transposeMat xs
    in appendHeadColumn x transXs where
        appendHeadColumn = zipWith (::)

addMatrix : Num a => Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
addMatrix = zipWith (zipWith (+))

multMatrix : Num a => Vect n (Vect m a) -> Vect m (Vect p a) -> Vect n (Vect p a)
multMatrix xs ys =
    let transposedYs = transposeMat ys
    in (\xrow => combineRows xrow <$> transposedYs) <$> xs where
        combineRows xrow yrow = sum (zipWith (*) xrow yrow)


vectTake : (m: Nat) -> Vect n a -> Vect (minimum m n) a
vectTake Z _ = []
vectTake m [] = rewrite minimumZeroZeroLeft m in []
vectTake (S k) (x :: xs) = x :: vectTake k xs


sumEntries : Num a => {n : Nat} -> (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys = do
    i <- integerToFin pos n
    pure $ index i xs + index i ys

main : IO ()
main = repl "\n> " (show . palindrome . toLower)
