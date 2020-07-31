module Main
import Data.Vect

%default total

data GameState : Type where
    NotRunning : GameState
    Running : (guesses : Nat) -> (letters : Nat) -> GameState

letters : String -> List Char
letters str = nub (map toUpper (unpack str))

data GuessResult = Correct | Incorrect

data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
    NewGame : (word : String) -> GameCmd () NotRunning (const (Running 6 (length (letters word))))
    Won  : GameCmd () (Running (S guesses) 0) (const NotRunning)
    Lost : GameCmd () (Running 0 (S guesses)) (const NotRunning)
    Guess : (c : Char) -> GameCmd GuessResult (Running (S guesses) (S letters))
                                                                            (
                                                                                \res => case res of
                                                                                    Correct => Running (S guesses) letters
                                                                                    Incorrect => Running guesses (S letters)
                                                                            )
    ShowState : GameCmd () state (const state)

    Message : String -> GameCmd () state (const state)
    ReadGuess : GameCmd Char state (const state)

    Pure : (res : ty) -> GameCmd ty (state_fn res) state_fn
    (>>=) : GameCmd a state1 state2_fn -> ((res : a) -> GameCmd b (state2_fn res) state3_fn) -> GameCmd b state1 state3_fn

namespace Loop
    data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
        (>>=) : GameCmd a state1 state2_fn -> ((res : a) -> Inf (GameLoop b (state2_fn res) state3_fn)) -> GameLoop b state1 state3_fn
        Exit : GameLoop () NotRunning (const NotRunning)

gameLoop : GameLoop () (Running (S guesses) (S letters)) (const NotRunning)
gameLoop {guesses} {letters} =
    do
        ShowState
        guess <- ReadGuess
        guessResult <- Guess guess
        case guessResult of
            Correct => case letters of
                Z =>
                    do
                        Won
                        ShowState
                        Exit
                (S k) =>
                    do
                        ShowState
                        gameLoop
            Incorrect =>
                do
                    Message "Bad guess"
                    case guesses of
                        Z =>
                            do
                                Lost
                                ShowState
                                Exit
                        (S k) =>
                            do
                                ShowState
                                gameLoop

hangman : GameLoop () NotRunning (const NotRunning)
hangman = do
    NewGame "testing"
    gameLoop

data Game : GameState -> Type where
    GameStart  : Game NotRunning
    GameWon    : (word : String) -> Game NotRunning
    GameLost   : (word : String) -> Game NotRunning
    InProgress : (word : String) -> (guesses : Nat) -> (missing : Vect letters Char) -> Game (Running guesses letters)

Show (Game g) where
    show GameStart = "Starting"
    show (GameWon word) = "Game won: word was " ++ word
    show (GameLost word) = "Game lost: word was " ++ word
    show (InProgress word guesses missing) = "\n" ++ pack (hideMissing <$> unpack word) ++ "\n" ++ show guesses ++ " guesses left"
        where
            hideMissing : Char -> Char
            hideMissing c = if c `elem` missing then '-' else c

data Fuel = Dry | More (Lazy Fuel)

data GameResult : (ty : Type) -> (ty -> GameState) -> Type where
    OK : (res : ty) -> Game (outstate_fn res) -> GameResult ty outstate_fn
    OutOfFuel : GameResult ty outstate_fn

ok : (res : ty) -> Game (outstate_fn res) ->IO (GameResult ty outstate_fn)
ok res st = pure (OK res st)

removeElem : (value : a) -> (xs : Vect (S n) a) -> Elem value xs -> Vect n a
removeElem x (x :: xs) Here = xs
removeElem {n = (S k)} value (x :: xs) (There later) = x :: (removeElem value xs later)

removeElem_auto : (value : a) -> (xs : Vect (S n) a) -> {auto prf : Elem value xs} -> Vect n a
removeElem_auto value xs {prf} = removeElem value xs prf

runCmd : {auto fuel : Fuel} -> Game instate -> GameCmd ty instate outstate_fn ->IO (GameResult ty outstate_fn)
runCmd state (NewGame word) = ok () (InProgress (toUpper word) _ (fromList (letters word)))
runCmd (InProgress word _ _) Won = ok () (GameWon word)
runCmd (InProgress word _ _) Lost = ok () (GameLost word)
runCmd (InProgress word _ missing) (Guess c) =
    case isElem c missing of
        Yes prf => ok Correct (InProgress word _ (removeElem_auto c missing))
        No contra => ok Incorrect (InProgress word _ missing)
runCmd state ShowState =
    do
        printLn state
        ok () state
runCmd state (Message x) =
    do
        printLn x
        ok () state
runCmd {fuel=More fuel} state ReadGuess =
    do
        putStr "Guess: "
        input <- getLine
        let letter = head' $ filter (isAlpha) $ take 1 $ unpack input
        case (letter, length input) of
            (Just x, S Z) => ok (toUpper x) state
            _ =>
                do
                    putStrLn "Invalid input"
                    runCmd state ReadGuess
runCmd {fuel=Dry} state ReadGuess = pure OutOfFuel
runCmd state (Pure res) = ok res state
runCmd {fuel} state (cmd >>= next) =
    do
        OK cmdRes newSt <- runCmd state cmd
            | OutOfFuel => pure OutOfFuel
        runCmd newSt (next cmdRes)
run : Fuel -> Game instate -> GameLoop ty instate outstate_fn -> IO (GameResult ty outstate_fn)
run Dry _ _ = pure OutOfFuel
run (More fuel) st (cmd >>= next) =
    do
        OK cmdRes newSt <- runCmd st cmd
            | OutOfFuel => pure OutOfFuel
        run fuel newSt (next cmdRes)
run (More fuel) st Exit = ok () st

covering
forever : Fuel
forever = More forever

covering
main : IO ()
main =
    do
        run forever GameStart hangman
        pure ()
