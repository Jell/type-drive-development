import Data.List
import Data.Vect

%default total

data WithEnvP = WiEnv | WoEnv

mutual
  data LVal = LError String
            | O (OType WiEnv (S n))
            | L (Vect (S (S n)) LVal)
            | E LEnv

  ||| OType is used as a function that takes a first LEnv argument and a bunch a
  ||| LVal. The number of LVal it should take depends on the Nat parameter.
  data OType : WithEnvP -> Nat -> Type where
    ZEnv : LEnv -> LVal -> OType WiEnv 1
    ZFree :  LVal -> OType WoEnv 1
    NEnv : OType WiEnv k -> LEnv -> LVal -> OType WiEnv (S k)
    NFree : OType WoEnv k -> LVal -> OType WoEnv (S k)

  LEnv : Type
  LEnv = (List (List (String, LVal)))

operate : (env:LEnv) -> (operative:LVal) -> (operands:Vect (S n) LVal) -> LVal
operate env (O {n=a} x) {n=b} operands with (decEq a b)
 operate env (O x) (y :: xs) | (Yes Refl) = ?wat
 operate env (O x) operands | (No contra) = LError "Wrong arity/number of args"
operate env _ operands = LError "Not operative"
