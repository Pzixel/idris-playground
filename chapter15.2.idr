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

procList : Service ListType ()
procList =
    do
        Respond
            (
                \msg =>
                    case msg of
                        (Length xs) => Pure $ length xs
                        (Append xs ys) => Pure $ xs ++ ys
            )
        Loop procList

procListMain : Client ()
procListMain =
    do
        Just list <- Spawn procList
            | Nothing => Action (putStrLn "Spawn failed")
        len <- Request list (Length [1,2,3])
        Action (printLn len)
        app <- Request list (Append [1,2,3] [4,5,6])
        Action (printLn app)

covering
runProc : Client () -> IO ()
runProc proc =
    do
        run forever proc
        pure ()

record WCData where
    constructor MkWCData
    wordCount : Nat
    lineCount : Nat

doCount : (content : String) -> WCData
doCount content =
    let lcount = length (lines content)
        wcount = length (words content)
    in MkWCData lcount wcount


data WC = CountFile String | GetData String

WCType : WC -> Type
WCType (CountFile x) = ()
WCType (GetData x) = Maybe WCData

countFile : List (String, WCData) -> String -> Process WCType (List (String, WCData)) Sent Sent
countFile files fname =
    do
        Right content <- Action (readFile fname)
            | Left err => Pure files
        let count = doCount content
        Action (putStrLn ("Counting complete for " ++ fname))
        Pure ((fname, doCount content) :: files)

wcService : (loaded : List (String, WCData)) -> Service WCType ()
wcService loaded =
    do
        msg <- Respond
            (
                \msg => case msg of
                    CountFile fname => Pure ()
                    GetData fname => Pure (lookup fname loaded)
            )
        newLoaded <- case msg of
            Just (CountFile fname) => countFile loaded fname
            _ => Pure loaded
        Loop (wcService newLoaded)

procWcMain : Client ()
procWcMain =
    do
        let fileName = "chapter15.2.idr";
        Just wc <- Spawn (wcService [])
            | Nothing => Action (putStrLn "Spawn failed")
        Action (putStrLn $ "Counting " ++ fileName)
        Request wc (CountFile fileName)
        Action (putStrLn "Processing")
        Just wcdata <- Request wc (GetData fileName)
            | Nothing => Action (putStrLn "File error")
        Action (putStrLn ("Words: " ++ show (wordCount wcdata)))
        Action (putStrLn ("Lines: " ++ show (lineCount wcdata)))
