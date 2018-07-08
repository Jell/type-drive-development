%default total

data DoorState = DoorClosed | DoorOpen

data DoorResult = OK | Jammed

namespace DoorCmdMachine
  data DoorCmd : (ty : Type) -> DoorState -> (ty -> DoorState) -> Type where
       Open : DoorCmd DoorResult DoorClosed
                                 (\res => case res of
                                               OK => DoorOpen
                                               Jammed => DoorClosed)
       Close : DoorCmd () DoorOpen (const DoorClosed)

       RingBell : DoorCmd () DoorClosed (const DoorClosed)

       Display : String -> DoorCmd () state (const state)

       Pure : (res : ty) -> DoorCmd ty (state_fn res) state_fn

       (>>=) : DoorCmd a state1 state2_fn ->
               ((res : a) -> DoorCmd b (state2_fn res) state3_fn) ->
               DoorCmd b state1 state3_fn


doorProg : DoorCmd () DoorClosed (const DoorClosed)
doorProg = do RingBell
              OK <- Open | Jammed => Display "Door jammed"
              Display "gooday"
              Close
              OK <- Open | Jammed => Display "Door jammed"
              Display "gooday"
              Close
