module Main

%default total

data Vect : Nat -> Type -> Type where
    Nil  : Vect Z a
    (::) : a -> Vect k a -> Vect (S k) a

length : (xs : Vect len elem) -> Nat
length [] = 0
length (x::xs) = 1 + length xs

Show a => Show (Vect n a) where
    show xs = "[" ++ show' xs ++ "]" where
        show' : Vect n a -> String
        show' Nil        = ""
        show' (x :: Nil) = show x
        show' (x :: xs)  = show x ++ ", " ++ show' xs

data Elem : a -> Vect k a -> Type where
    Here : Elem x (x :: xs)
    There : (later : Elem x xs) -> Elem x (y :: xs)

Uninhabited (Elem x []) where
    uninhabited _ impossible

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

data WordState : (guesses_remaining : Nat) -> (letters : Nat) -> Type where
    MkWordState : (word : String) -> (missing : Vect letters Char) -> WordState guesses_remaining letters

getMissing : WordState guesses_remaining letters -> Vect letters Char
getMissing (MkWordState _ missing) = missing

data Finished : Type where
    Lost : (game : WordState 0 (S letters)) -> Finished
    Won  : (game : WordState (S guesses) 0) -> Finished

data ValidInput : List Char -> Type where
    Letter : (c : Char) -> ValidInput [c]

Uninhabited (ValidInput []) where
    uninhabited _ impossible

Uninhabited (ValidInput (_ :: _ :: _)) where
    uninhabited _ impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [x] = Yes $ Letter x
isValidInput [] = No uninhabited
isValidInput (_ :: _ :: _) = No uninhabited

isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput (unpack s)

processGuess : (letter : Char) -> WordState (S guesses) (S letters) -> Either (WordState guesses (S letters)) (WordState (S guesses) letters)
processGuess letter (MkWordState word xs) = case isElem letter xs of
    (Yes prf) => Right $ MkWordState word (removeElem_auto letter xs)
    (No contra) => Left $ MkWordState word xs

covering readGuess : IO (x ** ValidInput x)
readGuess = do
    input <- getLine
    let chars = unpack input
    case isValidInput chars of
        (Yes prf) => pure $ (chars ** prf)
        (No contra) => do
            print "Invalid input"
            readGuess

covering game : WordState (S guesses) (S letters) -> IO Finished
game {guesses} {letters} st = do
    ([c] ** _) <- readGuess
    let guess = processGuess c st
    case guess of
        (Left l) => case guesses of
            Z => pure $ Lost l
            (S k) => do
                putStrLn $ "Wrong. Number of guesses = " ++ (show (S k))
                game l
        (Right r) => case letters of
            Z => pure $ Won r
            (S k) => do
                putStrLn $ "Correct. Letters left = " ++ (the String (show (getMissing r)))
                game r

-- getInitialGameState : (word : String) -> (S guesses : Nat) -> WordState (S guesses) (len word)

covering main : IO ()
main = do
    _ <- game $ the (WordState 15 _) (MkWordState "abrakadabra" (['a','b','r','a','c','a','d','a','b','r','a']) )
    pure ()
