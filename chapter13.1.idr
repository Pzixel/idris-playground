module Main
import Data.List.Views
import Data.Vect
import Data.Vect.Views
import Data.Nat.Views
import Data.Bits

%default total

namespace Door
    data DoorState = DoorClosed | DoorOpen

    data DoorCmd : Type -> DoorState -> DoorState -> Type where
        Open : DoorCmd     () DoorClosed DoorOpen
        Close : DoorCmd    () DoorOpen   DoorClosed
        RingBell : DoorCmd () DoorClosed DoorClosed
        
        Pure : ty -> DoorCmd ty state state
        (>>=) : DoorCmd a state1 state2 -> (a -> DoorCmd b state2 state3) -> DoorCmd b state1 state3

    doorProg : DoorCmd () DoorClosed DoorClosed
    doorProg = 
        do 
            RingBell
            Open 
            Close  

namespace Vend 
    VendState : Type
    VendState = (Nat, Nat) 

    data Input = COIN | VEND | CHANGE | REFILL Nat    

    data MachineCmd : Type -> VendState -> VendState -> Type where
        InsertCoin : MachineCmd () (pounds, chocs)     (S pounds, chocs)
        Vend       : MachineCmd () (S pounds, S chocs) (pounds, chocs)
        GetCoins   : MachineCmd () (pounds, chocs)     (Z, chocs)    
        Refill : (bars : Nat) ->
                    MachineCmd () (Z, chocs)          (Z, bars + chocs)
        Display : String -> MachineCmd () state state
        GetInput : MachineCmd (Maybe Input) state state
        
        Pure : ty -> MachineCmd ty state state
        (>>=) : MachineCmd a state1 state2 -> (a -> MachineCmd b state2 state3) -> MachineCmd b state1 state3
                
    data MachineIO : VendState -> Type where
        Do : MachineCmd a state1 state2 -> (a -> Inf (MachineIO state2)) -> MachineIO state1
        
    namespace MachineDo
        (>>=) : MachineCmd a state1 state2 -> (a -> Inf (MachineIO state2)) -> MachineIO state1
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
                machineLoop
        refill {pounds = S p} _ =
            do
                Display "Can't refill: Coins in machine"
                machineLoop
        
        
        machineLoop : MachineIO (pounds, chocs)
        machineLoop =
            do 
                Just x <- GetInput
                    | Nothing => 
                        do 
                            Display "Invalid input"
                            machineLoop
                case x of
                    COIN => 
                        do 
                            InsertCoin
                            machineLoop
                    VEND => vend
                    CHANGE => 
                        do 
                            GetCoins
                            Display "Change returned"
                            machineLoop
                    REFILL num => refill num

main : IO ()
main = pure ()