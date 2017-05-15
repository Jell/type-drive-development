import Data.Primitives.Views
import System

%default total

record Score where
       constructor MkScore
       correct : Nat
       attempted : Nat

record GameState where
       constructor MkGameState
       score : Score
       difficulty : Int

Show GameState where
  show st = show (correct (score st)) ++ "/" ++
            show (attempted (score st)) ++ "\n" ++
            "Difficulty: "++ show (difficulty st)

initState : GameState
initState = MkGameState (MkScore 0 0) 12

data Command : Type -> Type where
     PutStr : String -> Command ()
     GetLine : Command String

     GetRandom : Command Int
     GetGameState : Command GameState
     PutGameState : GameState -> Command ()

     Pure : ty -> Command ty
     Bind : Command a -> (a -> Command b) -> Command b

data ConsoleIO : Type -> Type where
     Quit : a -> ConsoleIO a
     Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b


mutual
  Functor Command where
    map func x = do val <- x
                    pure (func val)

  Applicative Command where
    pure x = Pure x
    (<*>) f a = do f' <- f
                   a' <- a
                   pure (f' a')

  Monad Command where
    (>>=) = Bind

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

setDifficulty : Nat -> GameState -> GameState
setDifficulty newDiff = record {difficulty=cast newDiff}

addWrong : GameState -> GameState
addWrong = record {score->attempted $= S}

addCorrect : GameState -> GameState
addCorrect = record {score->attempted $= S,
                     score->correct $= S}

data Input = Answer Int
           | QuitCmd

readInput : (prompt : String) -> Command Input
readInput prompt = do PutStr prompt
                      answer <- GetLine
                      if toLower answer == "quit"
                      then Pure QuitCmd
                      else Pure (Answer (cast answer))

updateGameState : (GameState -> GameState) -> Command ()
updateGameState f = do st <- GetGameState
                       PutGameState (f st)

mutual
  correct : ConsoleIO GameState
  correct = do PutStr "Correct!\n"
               updateGameState addCorrect
               quiz

  wrong : Int -> ConsoleIO GameState
  wrong ans = do PutStr $ "Wrong, the answer was: "++show ans++"\n"
                 updateGameState addWrong
                 quiz

  quiz : ConsoleIO GameState
  quiz = do num1 <- GetRandom
            num2 <- GetRandom
            st <- GetGameState
            PutStr (show st ++ "\n")
            input <- readInput $ show num1 ++ " * " ++ show num2 ++ "? "
            case input of
                 (Answer answer) => if answer == num1 * num2
                                    then correct
                                    else wrong (num1 * num2)
                 QuitCmd => Quit st

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
               (seed' `shiftR` 2) :: randoms seed'

runCommand : Stream Int ->
             GameState ->
             Command a ->
             IO (a, Stream Int, GameState)
runCommand rnds state (PutStr x) = do putStr x
                                      pure ((), rnds, state)
runCommand rnds state GetLine = do str <- getLine
                                   pure (str, rnds, state)
runCommand (val :: rnds) state GetRandom
           = pure (getRandom val (difficulty state), rnds, state)
  where
    getRandom : Int -> Int -> Int
    getRandom val max with (divides val max)
      getRandom val 0 | DivByZero = 1
      getRandom ((max * div) + rem) max | (DivBy prf) = abs rem + 1
runCommand rnds state GetGameState
  = pure (state, rnds, state)
runCommand rnds state (PutGameState newState)
  = pure ((), rnds, newState)
runCommand rnds state (Pure val)
  = pure (val, rnds, state)
runCommand rnds state (Bind c f)
  = do (res, newRnds, newState) <- runCommand rnds state c
       runCommand newRnds newState (f res)

run : Stream Int -> GameState -> ConsoleIO a -> IO (Maybe a, Stream Int, GameState)
run rnds state (Quit val) = pure $ (Just val, rnds, state)
run rnds state (Do c f)
  = do (res, newRnds, newState) <- runCommand rnds state c
       run newRnds newState (f res)

main : IO ()
main = do seed <- time
          (Just score, _, state) <-
            run (randoms (fromInteger seed)) initState quiz
              | _ => putStrLn "never reached"
          putStrLn $ "Final Score: "++show state

record Votes where
       constructor MkVotes
       upvotes : Int
       downvotes : Int

record Article where
       constructor MkArticle
       title : String
       url : String
       score : Votes

initPage : (title : String) -> (url : String) -> Article
initPage title url = MkArticle title url (MkVotes 0 0)

goodPage : Article
goodPage = MkArticle "Good Page" "http://example.com/good" (MkVotes 101 7)

badPage : Article
badPage = MkArticle "Bad Page" "http://example.com/bad" (MkVotes 5 47)

getScore : Article -> Int
getScore article = (upvotes (score article)) - (downvotes (score article))


addUpvote : Article -> Article
addUpvote = record {score->upvotes $= (+1)}

addDownvote : Article -> Article
addDownvote = record {score->downvotes $= (+1)}
