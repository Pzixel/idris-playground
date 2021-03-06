module Main
import Data.List.Views
import Data.Vect
import Data.Vect.Views
import Data.Nat.Views
import Data.Bits

%default total

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

PIN : Type
PIN = Vect 4 Char

data ATMState = Ready | CardInserted | Session
data PINCheck = CorrectPIN | IncorrectPIN
data HasCard : ATMState -> Type where
    HasCI      : HasCard CardInserted
    HasSession : HasCard Session
data ATMCmd : (ty : Type) -> ATMState -> (ty -> ATMState) -> Type where
    InsertCard : ATMCmd ()   Ready        (const CardInserted)
    EjectCard  : {auto prf : HasCard state} -> ATMCmd ()   state        (const Ready)
    GetPIN     : ATMCmd PIN  CardInserted (const CardInserted)
    CheckPIN   : PIN -> ATMCmd PINCheck CardInserted
                                                    (\check =>
                                                        case check of
                                                            CorrectPIN => Session
                                                            IncorrectPIN => CardInserted
                                                    )
    GetAmount  : ATMCmd Nat state (const state)
    Dispense   : (amount : Nat) -> ATMCmd () Session (const Session)

    Message    : String -> ATMCmd () state (const state)
    Pure  : (res : ty) -> ATMCmd ty (state_fn res) state_fn
    (>>=) : ATMCmd a state1 state2_fn -> ((res : a) -> ATMCmd b (state2_fn res) state3_fn) -> ATMCmd b state1 state3_fn

atm : ATMCmd () Ready (const Ready)
atm =
    do
        InsertCard
        pin <- GetPIN
        pinOK <- CheckPIN pin
        case pinOK of
            CorrectPIN =>
                do
                    amount <- GetAmount
                    Dispense amount
                    Message "Please remove your card and cash"
                    EjectCard
            IncorrectPIN =>
                do
                    Message "Incorrect PIN"
                    EjectCard

testPIN : Vect 4 Char
testPIN = ['1', '2', '3', '4']

readVect : (n : Nat) -> IO (Vect n Char)
readVect Z =
    do
        discard <- getLine
        pure []
readVect (S k) =
    do
        ch <- getChar
        chs <- readVect k
        pure (ch :: chs)

runATM : ATMCmd res inState outState_fn -> IO res
runATM InsertCard =
    do
        putStrLn "Please insert your card (press enter)"
        x <- getLine
        pure ()
runATM EjectCard = putStrLn "Card ejected"
runATM GetPIN =
    do
         putStr "Enter PIN: "
         readVect 4
runATM (CheckPIN pin) = if pin == testPIN then pure CorrectPIN else pure IncorrectPIN
runATM GetAmount =
    do
        putStr "How much would you like? "
        x <- getLine
        pure (cast x)
runATM (Dispense amount) = putStrLn ("Here is " ++ show amount)
runATM (Message msg) = putStrLn msg
runATM (Pure res) = pure res
runATM (x >>= f) =
    do
        x' <- runATM x
        runATM (f x')

namespace securityshell
    data Access = LoggedOut | LoggedIn
    data PwdCheck = Correct | Incorrect
    data ShellCmd : (ty : Type) -> Access -> (ty -> Access) -> Type where
        Password : String -> ShellCmd PwdCheck LoggedOut
                                                    (\check =>
                                                        case check of
                                                            Correct => LoggedIn
                                                            Incorrect => LoggedOut
                                                    )
        Logout : ShellCmd () LoggedIn (const LoggedOut)
        GetSecret : ShellCmd String LoggedIn (const LoggedIn)

        PutStr : String -> ShellCmd () state (const state)
        Pure : (res : ty) -> ShellCmd ty (state_fn res) state_fn
        (>>=) : ShellCmd a state1 state2_fn ->((res : a) -> ShellCmd b (state2_fn res) state3_fn) ->ShellCmd b state1 state3_fn

    session : ShellCmd () LoggedOut (const LoggedOut)
    session =
        do
            Correct <- Password "wurzel"
                | Incorrect => PutStr "Wrong password"
            msg <- GetSecret
            PutStr ("Secret code: " ++ show msg ++ "\n")
            Logout

    -- sessionBad : ShellCmd () LoggedOut (const LoggedOut)
    -- sessionBad =
    --     do
    --         Password "wurzel"
    --         msg <- GetSecret
    --         PutStr ("Secret code: " ++ show msg ++ "\n")
    --         Logout

    -- noLogout : ShellCmd () LoggedOut (const LoggedOut)
    -- noLogout =
    --     do
    --         Correct <- Password "wurzel"
    --             | Incorrect => PutStr "Wrong password"
    --         msg <- GetSecret
    --         PutStr ("Secret code: " ++ show msg ++ "\n")

namespace Vend
    VendState : Type
    VendState = (Nat, Nat)

    data Input = COIN | VEND | CHANGE | REFILL Nat
    data CoinResult = Inserted | Rejected

    data MachineCmd : (ty : Type) -> VendState -> (ty -> VendState) -> Type where
        InsertCoin : MachineCmd CoinResult (pounds, chocs)
                                                    (
                                                        \res =>
                                                            case res of
                                                                Inserted => (S pounds, chocs)
                                                                Rejected => (pounds, chocs)
                                                    )
        Vend       : MachineCmd () (S pounds, S chocs) (const (pounds, chocs))
        GetCoins   : MachineCmd () (pounds, chocs)     (const (Z, chocs))
        Refill : (bars : Nat) ->
                    MachineCmd () (Z, chocs)          (const (Z, bars + chocs))
        Display : String -> MachineCmd () state (const state)
        GetInput : MachineCmd (Maybe Input) state (const state)

        Pure : (res : ty) -> MachineCmd ty (state_fn res) state_fn
        (>>=) : MachineCmd a state1 state2_fn -> ((res : a) -> MachineCmd b (state2_fn res) state3_fn) -> MachineCmd b state1 state3_fn

    data MachineIO : VendState -> Type where
        Do : MachineCmd a state1 state2_fn -> ((res : a) -> Inf (MachineIO (state2_fn res))) -> MachineIO state1

    namespace MachineDo
        (>>=) : MachineCmd a state1 state2_fn -> ((res : a) -> Inf (MachineIO (state2_fn res))) -> MachineIO state1
        (>>=) = Do

    mutual
        vend : MachineIO (pounds, chocs)
        vend {pounds = S p} {chocs = S c} =
            do
                Vend
                Display "Enjoy!"
                machineLoop
        vend {chocs = Z} =
            do
                Display "Out of stock!"
                machineLoop
        vend {pounds = Z} =
            do
                Display "Insert a coin"
                machineLoop

        refill : (num : Nat) -> MachineIO (pounds, chocs)
        refill {pounds = Z} num =
            do
                Refill num
                Display $ "Added " ++ (show num) ++ " chocs into machine"
                machineLoop
        refill {pounds = S p} _ =
            do
                Display "Can't refill: Coins in machine"
                machineLoop


        machineLoop : MachineIO (pounds, chocs)
        machineLoop {pounds} {chocs} =
            do
                Display $ "Machine state: Coins in machine " ++ (show pounds) ++ " chocs " ++ (show chocs)
                Just x <- GetInput
                    | Nothing =>
                        do
                            Display "Invalid input"
                            machineLoop
                case x of
                    COIN =>
                        do
                            res <- InsertCoin
                            case res of
                                Inserted =>
                                    do
                                        Display "Coin inserted"
                                        machineLoop
                                Rejected =>
                                    do
                                        Display "Bad coin"
                                        machineLoop
                    VEND => vend
                    CHANGE =>
                        do
                            GetCoins
                            Display "Change returned"
                            machineLoop
                    REFILL num => refill num

    parseInput : String -> Maybe Input
    parseInput "coin" = pure COIN
    parseInput "vend" = pure VEND
    parseInput "change" = pure CHANGE
    parseInput x = case words x of
        ["refill", amount] => if all isDigit (unpack amount) then pure (REFILL (cast amount)) else Nothing
        _ => Nothing

    runMachine : MachineCmd a s state2_fn -> IO a
    runMachine {s=(pounds, chocs)} InsertCoin =
        pure $ if pounds < 5 then Inserted else Rejected -- simple failure emulation
    runMachine Vend = pure ()
    runMachine GetCoins = pure ()
    runMachine (Refill bars) = pure ()
    runMachine (Display x) = putStrLn x
    runMachine GetInput = parseInput <$> getLine
    runMachine (Pure res) = pure res
    runMachine (x >>= f) =
        do
            machineRes <- runMachine x
            runMachine (f machineRes)

    run : Fuel -> MachineIO _ -> IO ()
    run Dry _ = pure ()
    run (More fuel) (Do machine f) =
        do
            machinRes <- runMachine machine
            run fuel (f machinRes)

partial
main : IO ()
main = run forever (the (MachineIO (0, 0)) machineLoop)
