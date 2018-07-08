import Data.Vect

%default total

data DoorState = DoorClosed | DoorOpen

namespace DoorCmdMachine
  data DoorCmd : Type -> DoorState -> DoorState -> Type where
       Open : DoorCmd () DoorClosed DoorOpen
       Close : DoorCmd () DoorOpen DoorClosed
       RingBell : DoorCmd () state state

       Pure : ty -> DoorCmd ty state state
       (>>=) : DoorCmd a state1 state2 ->
               (a -> DoorCmd b state2 state3) ->
               DoorCmd b state1 state3

doorProg : DoorCmd () DoorClosed DoorClosed
doorProg = do RingBell
              Open
              RingBell
              Close

VendState : Type
VendState = (Nat,Nat)

data Input = COIN
           | VEND
           | CHANGE
           | REFILL Nat

data CoinResult = Inserted | Rejected

data MachineCmd : (ty : Type) -> VendState -> (ty -> VendState) -> Type where
  InsertCoin : MachineCmd CoinResult (pounds, chocs)
                          (\res => case res of
                                        Inserted => (S pounds, chocs)
                                        Rejected => (pounds, chocs))
  Vend       : MachineCmd () (S pounds, S chocs) (const (pounds, chocs))
  GetCoins   : MachineCmd () (pounds, chocs)     (const (Z, chocs))

  Refill     : (bars : Nat) ->
               MachineCmd () (Z, chocs)          (const (Z, bars + chocs))

  Display    : String ->
               MachineCmd () state               (const state)

  GetInput   : MachineCmd (Maybe Input) state (const state)

  Pure : (res : ty) -> MachineCmd ty (state_fn res) state_fn

  (>>=) : MachineCmd a state1 state2_fn ->
          ((res : a) -> MachineCmd b (state2_fn res) state3_fn) ->
          MachineCmd b state1 state3_fn


data MachineIO : VendState -> Type where
  Do : MachineCmd a state1 state2_fn ->
       ((res : a) -> Inf (MachineIO (state2_fn res))) ->
       MachineIO state1

namespace MachineDo
  (>>=) : MachineCmd a state1 state2_fn ->
          ((res : a) -> Inf (MachineIO (state2_fn res))) ->
          MachineIO state1
  (>>=) = Do


mutual
  vend : MachineIO (pounds, chocs)
  vend {pounds = (S k)} {chocs = (S j)}
    = do Vend
         Display "Enjoy!"
         machine_loop
  vend {chocs = Z} = do Display "Out of stock!"
                        machine_loop
  vend {pounds = Z} = do Display "Insert coin!"
                         machine_loop

  refill : (num : Nat) -> MachineIO (pounds, chocs)
  refill {pounds = Z} num
    = do Refill num
         machine_loop
  refill {pounds = (S k)} num
    = do Display "Can't refill, coinds in machine"
         machine_loop

  machine_loop : MachineIO (pounds, chocs)
  machine_loop =
    do Just x <- GetInput
            | Nothing => do Display "Invalid input"
                            machine_loop
       case x of
            COIN => do Inserted <- InsertCoin
                         | Rejected => do Display "Fake coin!"
                                          machine_loop
                       machine_loop
            VEND => vend
            CHANGE => do GetCoins
                         Display "Change returned"
                         machine_loop
            (REFILL num) => refill num


namespace GuessCmd
  data GuessCmd : Type -> Nat -> Nat -> Type where
    Try : Integer -> GuessCmd Ordering (S guesses) guesses

    Pure : ty -> GuessCmd ty state state
    (>>=) : GuessCmd a state1 state2 ->
            (a -> GuessCmd b state2 state3) ->
            GuessCmd b state1 state3


threeGuesses : GuessCmd () 3 0
threeGuesses = do Try 10
                  Try 20
                  Try 15
                  Pure ()

{-
noGuesses : GuessCmd () 0 0
noGuesses = do Try 10
               Pure ()
-}

data Matter = Solid | Liquid | Gas

namespace MatterCmd
  data MatterCmd : Type -> Matter -> Matter -> Type where
    Condense : MatterCmd () Gas Liquid
    Freeze : MatterCmd () Liquid Solid
    Melt : MatterCmd () Solid Liquid
    Boil : MatterCmd () Liquid Gas

    Pure : ty -> MatterCmd ty state state
    (>>=) : MatterCmd a state1 state2 ->
            (a -> MatterCmd b state2 state3) ->
            MatterCmd b state1 state3


iceSteam : MatterCmd () Solid Gas
iceSteam = do Melt
              Boil

steamIce : MatterCmd () Gas Solid
steamIce = do Condense
              Freeze

{-
overMelt : MatterCmd () Solid Gas
overMelt = do Melt
              Melt
-}

namespace StackCmd
  data StackCmd : Type -> Nat -> Nat -> Type where
    Push : Integer -> StackCmd () height (S height)
    Pop : StackCmd Integer (S height) height
    Top : StackCmd Integer (S height) (S height)

    GetStr : StackCmd String height height
    PutStr : String -> StackCmd () height height

    Pure : ty -> StackCmd ty height height
    (>>=) : StackCmd a height1 height2 ->
            (a -> StackCmd b height2 height3) ->
            StackCmd b height1 height3

testAdd : StackCmd Integer 0 0
testAdd = do Push 10
             Push 20
             val1 <- Pop
             val2 <- Pop
             Pure (val1 + val2)

doAdd : StackCmd () (S (S height)) (S height)
doAdd = do val1 <- Pop
           val2 <- Pop
           Push (val1 + val2)

doSubstract : StackCmd () (S (S height)) (S height)
doSubstract = do val1 <- Pop
                 val2 <- Pop
                 Push (val2 - val1)

doMultiply : StackCmd () (S (S height)) (S height)
doMultiply = do val1 <- Pop
                val2 <- Pop
                Push (val1 * val2)

doNegate : StackCmd () (S height) (S height)
doNegate = do val <- Pop
              Push (-val)

doDiscard : StackCmd Integer (S height) height
doDiscard = Pop

doDuplicate : StackCmd () (S height) (S (S height))
doDuplicate = do val <- Top
                 Push val

runStack : (stk : Vect inHeight Integer) ->
           StackCmd ty inHeight outHeight ->
           IO (ty, Vect outHeight Integer)
runStack stk (Push x) = pure ((), x :: stk)
runStack (x :: stk) Pop = pure (x, stk)
runStack (x :: stk) Top = pure (x, x :: stk)

runStack stk GetStr = do x <- getLine
                         pure (x, stk)
runStack stk (PutStr y) = do putStr y
                             pure ((), stk)

runStack stk (Pure x) = pure (x, stk)
runStack stk (cmd >>= next)
  = do (cmdRes, newStk) <- runStack stk cmd
       runStack newStk (next cmdRes)

namespace StackDo
  data StackIO : Nat -> Type where
    Do : StackCmd a height1 height2 ->
         (a -> Inf (StackIO height2)) ->
         StackIO height1

  (>>=) : StackCmd a height1 height2 ->
          (a -> Inf (StackIO height2)) ->
          StackIO height1
  (>>=) = Do

run : Vect height Integer -> StackIO height -> IO ()
run stk (Do cmd next) = do (res, newStk) <- runStack stk cmd
                           run newStk (next res)


data StkInput = Number Integer | Add | Subs | Mult | Neg | Dup | Discard

strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput "subs" = Just Subs
strToInput "mult" = Just Mult
strToInput "neg" = Just Neg
strToInput "discard" = Just Discard
strToInput "dup" = Just Dup
strToInput x = if all isDigit (unpack x)
               then Just (Number (cast x))
               else Nothing

mutual
  tryAdd : StackIO height
  tryAdd {height=(S (S h))} = do doAdd
                                 result <- Top
                                 PutStr (show result ++ "\n")
                                 stackCalc
  tryAdd = do PutStr "Fewer than two items on the stack\n"
              stackCalc

  trySubs : StackIO height
  trySubs {height=(S (S h))} = do doSubstract
                                  result <- Top
                                  PutStr (show result ++ "\n")
                                  stackCalc
  trySubs = do PutStr "Fewer than two items on the stack\n"
               stackCalc

  tryMult : StackIO height
  tryMult {height=(S (S h))} = do doMultiply
                                  result <- Top
                                  PutStr (show result ++ "\n")
                                  stackCalc
  tryMult = do PutStr "Fewer than two items on the stack\n"
               stackCalc

  tryNeg : StackIO height
  tryNeg {height=(S h)} = do doNegate
                             result <- Top
                             PutStr (show result ++ "\n")
                             stackCalc
  tryNeg = do PutStr "Fewer than one item on the stack\n"
              stackCalc

  tryDup : StackIO height
  tryDup {height=(S h)} = do doDuplicate
                             result <- Top
                             PutStr ("Duplicated: " ++ show result ++ "\n")
                             stackCalc
  tryDup = do PutStr "Fewer than one item on the stack\n"
              stackCalc

  tryDiscard : StackIO height
  tryDiscard {height=(S h)} = do x <- doDiscard
                                 PutStr ("Discarded: " ++ show x ++ "\n")
                                 stackCalc
  tryDiscard = do PutStr "Fewer than one item on the stack\n"
                  stackCalc

  stackCalc : StackIO height
  stackCalc = do PutStr "> "
                 input <- GetStr
                 case strToInput input of
                      Nothing => do PutStr "Invalid input\n"
                                    stackCalc
                      (Just (Number x)) => do Push x
                                              stackCalc
                      (Just Subs) => trySubs
                      (Just Mult) => tryMult
                      (Just Neg) => tryNeg
                      (Just Discard) => tryDiscard
                      (Just Dup) => tryDup
                      (Just Add) => tryAdd

main : IO ()
main = run [] stackCalc
