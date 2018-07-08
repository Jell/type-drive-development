import System.Concurrency.Channels

%default total

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

data Message = Add Nat Nat

data MessagePID : (iface : reqType -> Type) -> Type where
  MkMessage : PID -> MessagePID iface

data ProcState = NoRequest | Sent | Complete

AdderType : Message -> Type
AdderType (Add k j) = Nat

NoRecv : Void ->  Type
NoRecv = const Void

data Process : (iface : reqType -> Type) ->
               Type ->
               (in_state : ProcState) ->
               (out_state : ProcState) ->
               Type where
     Request : MessagePID service_iface ->
               (msg : service_reqType) ->
               Process iface (service_iface msg) st st
     Respond : ((msg : reqType) -> Process iface (iface msg) NoRequest NoRequest) ->
               Process iface (Maybe reqType) st Sent
     Spawn : Process service_iface () NoRequest Complete ->
             Process iface (Maybe (MessagePID service_iface)) st st
     Loop : Inf (Process iface  a NoRequest Complete) ->
            Process iface a Sent Complete
     Action : IO a -> Process iface a st st
     Pure : a -> Process iface a st st
     (>>=) : Process iface a st1 st2 ->
             (a -> Process iface b st2 st3) ->
             Process iface b st1 st3

run : Fuel -> Process iface t in_state out_state -> IO (Maybe t)
run Dry _ = pure Nothing
run (More fuel) (Request {service_iface} (MkMessage process) msg)
  = do Just chan <- connect process
         | Nothing => pure Nothing
       ok <- unsafeSend chan msg
       if ok then do Just x <- unsafeRecv (service_iface msg) chan
                       | Nothing => pure Nothing
                     pure (Just x)
             else pure Nothing
run (More fuel) (Respond {reqType} calc)
  = do Just sender <- listen 1
         | Nothing => pure Nothing
       Just msg <- unsafeRecv reqType sender
         | Nothing => pure Nothing
       res <- run fuel (calc msg)
       unsafeSend sender res
       pure (Just (Just msg))
run (More fuel) (Action act)
  = do res <- act
       pure (Just res)
run (More fuel) (Spawn proc)
  = do Just pid <- spawn (do run fuel proc
                             pure ())
         | Nothing => pure Nothing
       pure (Just (Just (MkMessage pid)))
run (More fuel) (Loop act) = run fuel act
run (More fuel) (Pure val) = pure (Just val)
run (More fuel) (act >>= next)
  = do Just x <- run fuel act
         | Nothing => pure Nothing
       run fuel (next x)

partial
runProc : Process iface () in_state out_state -> IO ()
runProc proc = do run forever proc
                  pure ()

procAdder : Process AdderType () NoRequest Complete
procAdder = do Respond (\msg => case msg of
                                     Add x y => Pure (x + y))
               Loop procAdder

procMain : Process NoRecv () NoRequest NoRequest
procMain = do Just adder_id <- Spawn procAdder
                | Nothing => Action (putStrLn "Spawn failed")
              answer <- Request adder_id (Add 2 3)
              Action (printLn answer)



partial
adder : IO ()
adder = do Just sender_chan <- listen 1
             | Nothing => adder
           Just msg <- unsafeRecv Message sender_chan
             | Nothing => adder
           case msg of
                Add x y => do ok <- unsafeSend sender_chan (x + y)
                              adder

partial
main : IO ()
main = do Just adder_id <- spawn adder
            | Nothing => putStrLn "Spawn failed"
          Just chan <- connect adder_id
            | Nothing => putStrLn "Connection failed"

          ok <- unsafeSend chan (Add 2 3)
          Just answer <- unsafeRecv Nat chan
            | Nothing => putStrLn "Send failed"
          printLn answer

          ok <- unsafeSend chan (Add 2 3)
          Just answer <- unsafeRecv Nat chan
            | Nothing => putStrLn "Send failed"
          printLn answer
