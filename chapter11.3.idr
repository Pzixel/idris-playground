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
    ReadFile : String -> Command (Either FileError String)
    WriteFile : String -> String -> Command (Either FileError ())

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
runCommand (ReadFile x) = readFile x
runCommand (WriteFile fileName content) = writeFile fileName content
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

quiz : Stream Int -> (score : Nat) -> (tries : Nat) -> ConsoleIO Nat
quiz (num1 :: num2 :: nums) score tries =
    do
        let scoreString = show score ++ " / " ++ show tries
        PutStrLn ("Score so far: " ++ scoreString ++ "\n")
        input <- readInput (show num1 ++ "*" ++ show num2 ++ "? ")
        case input of
            Answer answer =>
                if (answer == num1 * num2)
                    then
                        do
                            PutStrLn "Correct!"
                            quiz nums (score + 1) (tries + 1)
                    else
                        do
                            PutStrLn ("Wrong, the answer is " ++ show (num1 * num2))
                            quiz nums score (tries + 1)
            QuitCmd =>
                do
                    PutStrLn $ "Final score: " ++ scoreString
                    Quit score

shell : ConsoleIO ()
shell =
    do
        PutStrLn "enter a command"
        command <- GetLine
        case words (toLower command) of
            ["cat", filename] =>
                do
                    res <- ReadFile filename
                    case res of
                        (Left e) =>
                            do
                                PutStrLn $ "Unknown error: " ++ (show e)
                                shell
                        (Right content) =>
                            do
                                PutStrLn content
                                shell
            ["copy", source, destination] =>
                do
                    res <- ReadFile source
                    case res of
                        (Left e) =>
                            do
                                PutStrLn $ "Unknown error while reading: " ++ (show e)
                                shell
                        (Right content) =>
                            do
                                resWrite <- WriteFile destination content
                                case resWrite of
                                    (Left e) =>
                                        do
                                            PutStrLn $ "Unknown error while writing: " ++ (show e)
                                            shell
                                    (Right _) => shell
            ("quit" :: _) => Quit ()
            _ =>
                do
                    PutStrLn "Unknown command"
                    shell


covering
main : IO ()
main = pure ()
