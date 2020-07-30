module Main
import Data.List.Views
import Data.Vect
import Data.Vect.Views
import Data.Nat.Views
import Data.Bits

%default total

namespace Door
    data DoorState = DoorClosed | DoorOpen
    data DoorResult = OK | Jammed

    data DoorCmd : (ty : Type) -> DoorState -> (ty -> DoorState) -> Type where
        Open : DoorCmd DoorResult DoorClosed
            (\res =>
                case res of
                    OK => DoorOpen
                    Jammed => DoorClosed
            )
        Close : DoorCmd    () DoorOpen   (const DoorClosed)
        RingBell : DoorCmd () s          (const s)

        Display : String -> DoorCmd () state (const state)

        Pure : (res : ty) -> DoorCmd ty (state_fn res) state_fn
        (>>=) : DoorCmd a state1 state2_fn -> ((res : a) -> DoorCmd b (state2_fn res) state3_fn) -> DoorCmd b state1 state3_fn

    doorProg : DoorCmd () DoorClosed (const DoorClosed)
    doorProg =
        do
            RingBell
            jam <- Open
            case jam of
                OK => Close
                Jammed => Display "Something bad happened"
            RingBell
