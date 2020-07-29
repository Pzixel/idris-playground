module Main
import Data.List.Views
import Data.Vect
import Data.Vect.Views
import Data.Nat.Views
import Data.Bits

%default total

data Fuel = Dry | More (Lazy Fuel)

data Command : Type -> Type where
    PutStrLn : String -> Command ()
    GetLine : Command String

    Pure : ty -> Command ty
    Bind : Command a -> (a -> Command b) -> Command b

namespace CommandDo
    (>>=) : Command a -> (a -> Command b) -> Command b
    (>>=) = Bind    
    
data ConsoleIO : Type -> Type where
    Quit : a -> ConsoleIO a
    Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

(>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
(>>=) = Do

covering
forever : Fuel
forever = More forever

runCommand : Command a -> IO a
runCommand (PutStrLn x) = putStrLn x
runCommand GetLine = getLine
runCommand (Pure val) = pure val
runCommand (Bind c f) = 
    do 
        res <- runCommand c
        runCommand (f res)

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run _ (Quit val) = pure (Just val)
run (More fuel) (Do c f) = 
    do 
        res <- runCommand c
        run fuel (f res)
run Dry p = pure Nothing

data Input = Answer Int | QuitCmd

readInput : (prompt : String) -> Command Input
readInput prompt = 
    do 
        PutStrLn prompt
        answer <- GetLine
        if toLower answer == "quit"
            then Pure QuitCmd
            else Pure (Answer (cast answer))

quiz : Stream Int -> (score : Nat) -> ConsoleIO Nat
quiz (num1 :: num2 :: nums) score = 
    do 
        PutStrLn ("Score so far: " ++ show score ++ "\n")
        input <- readInput (show num1 ++ "*" ++ show num2 ++ "? ")
        case input of
            Answer answer => 
                if (cast answer == num1 * num2) 
                    then 
                        do 
                            putStrLn "Correct!"
                            quiz nums (score + 1)
                    else 
                        do 
                            putStrLn ("Wrong, the answer is " ++ show (num1 * num2))
                            quiz nums score   
            QuitCmd => Quit score            

covering
main : IO ()
main = pure ()