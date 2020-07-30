module Main
import Data.List.Views
import Data.Vect
import Data.Vect.Views
import Data.Nat.Views
import Data.Bits

%default total

data StackCmd : Type -> Nat -> Nat -> Type where
    Push : Integer -> StackCmd () height (S height)
    Pop : StackCmd Integer (S height) height
    Top : StackCmd Integer (S height) (S height)

    GetStr : StackCmd String height height
    PutStr : String -> StackCmd () height height

    Pure : ty -> StackCmd ty height height
    (>>=) : StackCmd a height1 height2 -> (a -> StackCmd b height2 height3) -> StackCmd b height1 height3

testAdd : StackCmd Integer a a
testAdd =
    do
        Push 10
        Push 20
        val1 <- Pop
        val2 <- Pop
        Pure (val1 + val2)

runStack : (stk : Vect inHeight Integer) -> StackCmd ty inHeight outHeight -> IO (ty, Vect outHeight Integer)
runStack stk (Push val) = pure ((), val :: stk)
runStack (val :: stk) Pop = pure (val, stk)
runStack (val :: stk) Top = pure (val, val :: stk)
runStack stk GetStr =
    do
        x <- getLine
        pure (x, stk)
runStack stk (PutStr s) =
    do
        putStrLn s
        pure ((), stk)
runStack stk (Pure x) = pure (x, stk)
runStack stk (cmd >>= next) =
    do
        (cmdRes, newStk) <- runStack stk cmd
        runStack newStk (next cmdRes)

data StackIO : Nat -> Type where
    Do : StackCmd a height1 height2 -> (a -> Inf (StackIO height2)) -> StackIO height1

namespace StackDo
    (>>=) : StackCmd a height1 height2 -> (a -> Inf (StackIO height2)) -> StackIO height1
    (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run : Fuel -> Vect height Integer -> StackIO height -> IO ()
run (More fuel) stk (Do c f) =
    do
        (res, newStk) <- runStack stk c
        run fuel newStk (f res)
run Dry stk p = pure ()

data StkInput = Number Integer | Add | Subtract | Multiply | Negate | Discard | Duplicate

strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput "subtract" = Just Subtract
strToInput "multiply" = Just Multiply
strToInput "negate" = Just Negate
strToInput "discard" = Just Discard
strToInput "duplicate" = Just Duplicate
strToInput x = if all isDigit (unpack x) then Just (Number (cast x)) else Nothing


mutual
    duplicate : StackIO height
    duplicate {height = Z} =
        do
            PutStr "Fewer elements than 1"
            stackCalc
    duplicate {height = (S k)} =
        do
            val1 <- Top
            Push val1
            PutStr ("Duplicated " ++ show val1)
            stackCalc

    discard : StackIO height
    discard {height = Z} =
        do
            PutStr "Fewer elements than 1"
            stackCalc
    discard {height = (S k)} =
        do
            val1 <- Pop
            PutStr ("Discarded " ++ show val1)
            stackCalc

    negate : StackIO height
    negate {height = Z} =
        do
            PutStr "Fewer elements than 1"
            stackCalc
    negate {height = (S k)} =
        do
            val1 <- Pop
            Push (-val1)
            result <- Top
            PutStr (show result)
            stackCalc

    tryBinary : (Integer -> Integer -> Integer) -> StackIO height
    tryBinary op {height = (S (S k))} =
        do
            val1 <- Pop
            val2 <- Pop
            Push (val2 `op` val1)
            result <- Top
            PutStr (show result)
            stackCalc
    tryBinary _ =
        do
            PutStr "Fewer elements than 2"
            stackCalc

    stackCalc : StackIO height
    stackCalc =
        do
             PutStr "> "
             input <- GetStr
             case strToInput input of
                Nothing =>
                    do
                        PutStr "Invalid input\n"
                        stackCalc
                Just (Number x) =>
                    do
                        Push x
                        stackCalc
                Just Add => tryBinary (+)
                Just Subtract => tryBinary (-)
                Just Multiply => tryBinary (*)
                Just Negate => negate
                Just Discard => discard
                Just Duplicate => duplicate

partial
main : IO ()
main = run forever [] stackCalc
