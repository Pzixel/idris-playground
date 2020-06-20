module Main
import Data.Vect

%default total

data WordState : (guesses_remaining : Nat) -> (letters : Nat) -> Type where
    MkWordState : (word : String) -> (missing : Vect letters Char) -> WordState guesses_remaining letters

data Finished : Type where
    Lost : (game : WordState 0 (S letters)) -> Finished
    Won  : (game : WordState (S guesses) 0) -> Finished

game_step : WordState (S guesses) (S letters) -> IO Finished
game_step (st @ (MkWordState word (x :: xs))) = do
    input <- getLine
    case unpack input of 
        [x] => ?impl 
        _ => do 
            print "Invalid input"
            game_step st

main : IO ()
main = print $ 10