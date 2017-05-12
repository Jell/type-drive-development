import Data.Vect

removeElem : (value : a) ->
             (xs : Vect (S n) a) ->
             {auto prf : Elem value xs} ->
             Vect n a
removeElem value (value :: ys) {prf=Here} = ys
removeElem {n=Z} value (y :: []) {prf=(There later)} = absurd later
removeElem {n=(S k)} value (y :: ys) {prf=(There later)}
  = y :: removeElem value ys {prf=later}


data WordState : (guesses_remaining : Nat) -> (letter : Nat) -> Type where
     MkWordState : (word : String) ->
                   (missing : Vect letters Char) ->
                    WordState guesses_remaining letters

data Finished : Type where
     Lost : (game : WordState 0 (S letters)) -> Finished
     Won : (game : WordState (S guesses) 0) -> Finished

data ValidInput : List Char -> Type where
     Letter : (c : Char) -> ValidInput [c]

noEmpty : ValidInput [] -> Void
noEmpty (Letter _) impossible

noMoreThanOne : ValidInput (x :: (y :: xs)) -> Void
noMoreThanOne (Letter _) impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No noEmpty
isValidInput (x :: []) = Yes (Letter x)
isValidInput (x :: (y :: xs)) = No noMoreThanOne

isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput (unpack s)

readGuess : IO (x ** ValidInput x)
readGuess = do putStr "Guess:"
               x <- getLine
               case isValidString (toUpper x) of
                    (Yes prf) => pure (_ ** prf)
                    (No contra) => do putStrLn "Invalid guess"
                                      readGuess

processGuess : (letter : Char) ->
               WordState (S guesses) (S letters) ->
               Either (WordState guesses (S letters))
                      (WordState (S guesses) letters)
processGuess letter (MkWordState word missing)
  = case isElem letter missing of
         (Yes prf) => Right (MkWordState word (removeElem letter missing))
         (No contra) => Left (MkWordState word missing)

printState : WordState guesses letters -> IO ()
printState (MkWordState word missing) =
  putStrLn (pack (map (\c => case isElem (toUpper c) missing of
                                  (Yes prf) => '_'
                                  (No contra) => c)
                      (unpack word)))

game : WordState (S guesses) (S letters) -> IO Finished
game {guesses} {letters} state
  = do (x ** prf) <- readGuess
       case prf of
            (Letter c) =>
              case processGuess c state of
                   (Left l) => case guesses of
                                    Z => pure (Lost l)
                                    (S k) => do putStrLn ("Nope! " ++
                                                          (show guesses) ++
                                                          " guesses left")
                                                printState l
                                                game l
                   (Right r) => case letters of
                                     Z => pure (Won r)
                                     (S k) => do putStrLn "Yes!"
                                                 printState r
                                                 game r

main : IO ()
main = do result <- game {guesses=2}
                         (MkWordState "Test" ['T', 'E', 'S'])
          case result of
               (Lost (MkWordState word missing)) =>
                     putStrLn ("You lose. The word was " ++ word)
               (Won game) =>
                    putStrLn "You win!"
