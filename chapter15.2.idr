module Main
import Data.Vect
import System.Concurrency.Channels

%default total

data Message = Add Nat Nat

AdderType : Message -> Type
AdderType (Add _ _) = Nat

data ListAction : Type where
    Length : List elem -> ListAction
    Append : List elem -> List elem -> ListAction

ListType : ListAction -> Type
ListType (Length xs) = Nat
ListType (Append {elem} xs ys) = List elem

data MessagePID : (iface : reqType -> Type) -> Type where
    MkMessage : PID -> MessagePID iface
data Fuel = Dry | More (Lazy Fuel)

covering
forever : Fuel
forever = More forever

data ProcState = NoRequest | Sent | Complete

data Process : (iface : reqType -> Type) -> Type -> (in_state : ProcState) -> (out_state : ProcState) -> Type where
    Request : MessagePID service_iface -> (msg : service_reqType) -> Process iface (service_iface msg) st st
    Respond : ((msg : reqType) -> Process iface (iface msg) NoRequest NoRequest) -> Process iface (Maybe reqType) st Sent
    Spawn : Process service_iface () NoRequest Complete ->Process iface (Maybe (MessagePID service_iface)) st st
    Loop : Inf (Process iface a NoRequest Complete) -> Process iface a Sent Complete
    Action : IO a -> Process iface a st st
    Pure : a -> Process iface a st st
    (>>=) : Process iface a st1 st2 -> (a -> Process iface b st2 st3) -> Process iface b st1 st3

NoRecv : Void -> Type
NoRecv = void

Service : (iface : reqType -> Type) -> Type -> Type
Service iface a = Process iface a NoRequest Complete

Client : Type -> Type
Client a = Process NoRecv a NoRequest NoRequest

procAdder : Service AdderType ()
procAdder =
    do
        Respond (
            \msg =>
                case msg of
                    Add x y => Pure (x + y))
        Loop procAdder

procMain : Client ()
procMain =
    do
        Just adder_id <- Spawn procAdder
            | Nothing => Action (putStrLn "Spawn failed")
        answer <- Request adder_id (Add 2 3)
        Action (printLn answer)

run : Fuel -> Process iface t in_state out_state -> IO (Maybe t)
run Dry _ = pure Nothing
run fuel (Request (MkMessage {iface} process) msg) =
    do
        Just chan <- connect process
            | _ => pure Nothing
        ok <- unsafeSend chan msg
        if ok then unsafeRecv (iface msg) chan else pure Nothing
run fuel (Respond {reqType} calc)
    =
        do
            Just sender <- listen 1
                | Nothing => pure (Just Nothing)
            Just msg <- unsafeRecv reqType sender
                | Nothing => pure (Just Nothing)
            Just res <- run fuel (calc msg)
                | Nothing => pure Nothing
            unsafeSend sender res
            pure (Just (Just msg))
run (More fuel) (Loop act) = run fuel act
run fuel (Spawn proc) =
    do
        Just pid <- spawn (
            do
                run fuel proc
                pure ()
            )
            | Nothing => pure Nothing
        pure (Just (Just (MkMessage pid)))
run fuel (Action act) =
    do
        res <- act
        pure (Just res)
run fuel (Pure val) = pure (Just val)
run fuel (act >>= next) =
    do
        Just x <- run fuel act
            | Nothing => pure Nothing
        run fuel (next x)

covering
runProc : Client () -> IO ()
runProc proc =
    do
        run forever proc
        pure ()
