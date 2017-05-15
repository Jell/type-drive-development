import Data.Primitives.Views
import System

%default total

data Command : Type -> Type where
     PutStr : String -> Command ()
     GetLine : Command String
     ReadFile : (filename : String) -> Command (Either FileError String)
     WriteFile : (filename : String) -> (content : String) -> Command (Either FileError ())
     CopyFile : (from : String) -> (to : String) -> Command (Either FileError ())
     Pure : ty -> Command ty
     Bind : Command a -> (a -> Command b) -> Command b

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

data ConsoleIO : Type -> Type where
     Quit : a -> ConsoleIO a
     Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

runCommand : Command a -> IO a
runCommand (ReadFile filename) = readFile filename
runCommand (WriteFile filename content) = writeFile filename content
runCommand (CopyFile from to) = do Right content <- readFile from
                                         | Left error => pure (Left error)
                                   writeFile to content
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (Pure x) = pure x
runCommand (Bind c f) = do res <- runCommand c
                           runCommand (f res)

run : ConsoleIO a -> IO (Maybe a)
run (Quit val) = pure (Just val)
run (Do c f) = do res <- runCommand c
                  run (f res)

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
               (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound num with (divides num 12)
      bound ((12 * div) + rem) | (DivBy prf) = rem + 1

data Input = Answer Int
           | QuitCmd

readInput : (prompt : String) -> Command Input
readInput prompt = do PutStr prompt
                      answer <- GetLine
                      if toLower answer == "quit"
                      then Pure QuitCmd
                      else Pure (Answer (cast answer))
mutual
  correct : Stream Int -> (score : Nat) -> (attempts : Nat) -> ConsoleIO Nat
  correct nums score attempts
    = do PutStr "correct!\n"
         quiz nums (score + 1) (attempts + 1)

  wrong : Stream Int -> Int -> (score : Nat) -> (attempts : Nat) -> ConsoleIO Nat
  wrong nums ans score attempts
    = do PutStr ("Wrong, the answer is " ++ show ans ++"\n")
         quiz nums score (attempts + 1)

  quiz : Stream Int -> (score : Nat) -> (attempts : Nat) -> ConsoleIO Nat
  quiz (num1 :: num2 :: nums) score attempts
    = do PutStr ("Score so far: " ++ show score ++ "/" ++ show attempts ++ "\n")
         input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
         case input of
              (Answer answer) => if answer == num1 * num2
                                 then correct nums score attempts
                                 else wrong nums (num1*num2) score attempts
              QuitCmd => Quit score

main : IO ()
main = do seed <- time
          Just score <- run (quiz (arithInputs (fromInteger seed)) 0 0)
            | Nothing => putStrLn "not gonna happen"
          putStrLn ("Final score: " ++ show score)

shell : ConsoleIO ()
shell = do PutStr "> "
           input <- GetLine
           case span (/= ' ') input of
                    ("exit", "") => do PutStr ("Bye" ++ "\n")
                                       Quit ()

                    ("cat", args) => do Right content <- ReadFile (ltrim args)
                                              | Left error => do PutStr (show error ++ "\n")
                                                                 shell
                                        PutStr (content ++ "\n")
                                        shell

                    ("copy", args) => let (from, to) = span (/= ' ') (ltrim args) in
                                      do Right () <- CopyFile from (ltrim to)
                                               | Left error => do PutStr (show error ++ "\n")
                                                                  shell
                                         PutStr ("Copied!\n")
                                         shell

                    (cmd, args) => do PutStr ("Invalid command: " ++ cmd ++ "\n")
                                      shell

run' : ConsoleIO () -> IO ()
run' (Quit ()) = pure ()
run' (Do c f) = do res <- runCommand c
                   run' (f res)
