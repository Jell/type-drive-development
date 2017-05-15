import Control.Monad.State

data Tree a = Empty
            | Node (Tree a) a (Tree a)

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred"
                      (Node Empty "Sheila" Empty))
                "Alice"
                (Node Empty "Bob" (Node Empty "Eve" Empty))

flatten : Tree a -> List a
flatten Empty = []
flatten (Node left val right) = flatten left ++ val :: flatten right

treeLabelWith : Stream labelType -> Tree a ->
                (Stream labelType, Tree (labelType, a))
treeLabelWith lbls Empty = (lbls, Empty)
treeLabelWith lbls (Node left val right)
  = let (lblThis :: lblsLeft, left_labelled) = treeLabelWith lbls left
        (lblsRight, right_labelled) = treeLabelWith lblsLeft right
    in (lblsRight, Node left_labelled (lblThis, val) right_labelled)

treeLabel : Tree a -> Tree (Integer, a)
treeLabel tree = snd (treeLabelWith [1..] tree)


treeLabelWith' : Tree a -> State (Stream labelType) (Tree (labelType, a))
treeLabelWith' Empty = pure Empty
treeLabelWith' (Node left val right)
  = do left_labelled <- treeLabelWith' left
       (this :: rest) <- get
       put rest
       right_labelled <- treeLabelWith' right
       pure (Node left_labelled (this, val) right_labelled)

treeLabel' : Tree a -> Tree (Integer, a)
treeLabel' tree = evalState (treeLabelWith' tree) [1..]

update : (stateType -> stateType) -> State stateType ()
update f = do s <- get
              put (f s)

increase : Nat -> State Nat ()
increase inc = update (+inc)

countEmpty : Tree a -> State Nat ()
countEmpty Empty = update (+1)
countEmpty (Node left val right) = do countEmpty left
                                      countEmpty right

countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = do (empties, nodes) <- get
                          put (empties + 1, nodes)
countEmptyNode (Node left val right) = do countEmptyNode left
                                          (empties, nodes) <- get
                                          put (empties, nodes + 1)
                                          countEmptyNode right


data State' : (stateType : Type) -> Type -> Type where
     Get : State' stateType stateType
     Put : stateType -> State' stateType ()

     Pure : ty -> State' stateType ty
     Bind : State' stateType a -> (a -> State' stateType b) -> State' stateType b


get : State' stateType stateType
get = Get

put : stateType -> State' stateType ()
put = Put

pure : ty -> State' stateType ty
pure = Pure

runState : State' stateType a -> (st : stateType) -> (a, stateType)
runState Get st = (st, st)
runState (Put newState) st = ((), newState)
runState (Pure x) st = (x, st)
runState (Bind cmd prog) st = let (val, nextState) = runState cmd st in
                                  runState (prog val) nextState

mutual
  Functor (State' stateType) where
    map func x = do val <- x
                    pure (func val)

  Applicative (State' stateType) where
    pure = Pure
    (<*>) f a = do f' <- f
                   a' <- a
                   pure (f' a')

  Monad (State' stateType) where
    (>>=) = Bind


treeLabelWith'' : Tree a -> State' (Stream labelType) (Tree (labelType, a))
treeLabelWith'' Empty = pure Empty
treeLabelWith'' (Node left val right)
  = do left_labelled <- treeLabelWith'' left
       (this :: rest) <- get
       put rest
       right_labelled <- treeLabelWith'' right
       pure (Node left_labelled (this, val) right_labelled)


treeLabel'' : Tree a -> Tree (Integer, a)
treeLabel'' tree = fst (runState (treeLabelWith'' tree) [1..])

crew : List String
crew = ["Lister", "Rimmer", "Kryten", "Cat"]

main : IO ()
main = do putStr "Display Crew? "
          x <- getLine
          when (x == "yes") $
            do traverse putStrLn crew
               pure ()
          putStrLn "Done"

addIfPositive : Integer -> State' Integer Bool
addIfPositive val = do when (val > 0) $
                            do current <- get
                               put (current + val)
                       pure (val > 0)

addPositives : List Integer -> State' Integer Nat
addPositives vals = do added <- traverse addIfPositive vals
                       pure (length (filter id added))
