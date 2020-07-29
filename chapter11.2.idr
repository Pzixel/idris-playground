module Main
import Data.List.Views
import Data.Vect
import Data.Vect.Views
import Data.Nat.Views
import Data.Bits

%default total

data InfIO : Type where
    Do : IO a -> (a -> Inf InfIO) -> InfIO

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

loopPrint : String -> InfIO
loopPrint msg = Do (putStrLn msg) (\_ => loopPrint msg)  

run : Fuel -> InfIO -> IO ()
run (More fuel) (Do c f) = 
    do 
        res <- c
        run fuel (f res)
run Dry p = putStrLn "Out of fuel"

quiz : Stream Int -> (score : Nat) -> InfIO
quiz (num1 :: num2 :: nums) score = 
    do 
        putStrLn ("Score so far: " ++ show score)
        putStr (show num1 ++ "*" ++ show num2 ++ "? ")
        answer <- getLine
        if (cast answer == num1 * num2) 
            then 
                do 
                    putStrLn "Correct!"
                    quiz nums (score + 1)
            else 
                do 
                    putStrLn ("Wrong, the answer is " ++ show (num1 * num2))
                    quiz nums score        

covering
forever : Fuel
forever = More forever

totalREPL : (prompt : String) -> (action : String -> String) -> InfIO
totalREPL prompt action = 
    do 
        putStr prompt
        input <- getLine
        putStr $ action input
        totalREPL prompt action


covering
main : IO ()
main = run forever (quiz [1..] 0)