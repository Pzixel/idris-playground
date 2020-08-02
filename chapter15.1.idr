module Main
import Data.Vect
import System.Concurrency.Channels

%default total

data Message = Add Nat Nat

covering
adder : IO ()
adder =
    do
        Just sender_chan <- listen 1
            | Nothing => adder
        Just msg <- unsafeRecv Message sender_chan
            | Nothing => adder
        case msg of
            Add x y =>
                do
                    unsafeSend sender_chan (x + y)
                    adder

covering
main : IO ()
main =
    do
        Just adder_id <- spawn adder
            | Nothing => putStrLn "Spawn failed"
        Just chan <- connect adder_id
            | Nothing => putStrLn "Connection failed"
        unsafeSend chan (Add 2 3)
        Just answer <- unsafeRecv Nat chan
            | Nothing => putStrLn "Send failed"
        printLn answer

