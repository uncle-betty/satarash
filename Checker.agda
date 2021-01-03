module Checker where

open import Codata.Musical.Costring using (toCostring)
open import Data.Bool using (Bool ; true ; false)
open import Data.List using (List ; [] ; _∷_)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_)
open import Data.String using (String)
open import Data.Unit using (⊤)
open import Function using (_$_ ; _∘_ ; case_of_)
open import IO.Primitive using (IO ; readFiniteFile ; putStrLn)
open import Level using (0ℓ ; Lift ; lift)

open import Parser using (parse)
open import Verifier using (Formula ; Proof ; checkLRAT)

{-# FOREIGN GHC import qualified System.Environment as SE #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}

postulate getArgs : IO (List String)

{-# COMPILE GHC getArgs = fmap (fmap T.pack) SE.getArgs #-}

bitsᶜ : ℕ
bitsᶜ = 24

runCheck : String → String → Maybe Bool
runCheck fStr pStr = do
  f , p ← parse bitsᶜ fStr pStr
  just $ case checkLRAT bitsᶜ f p of λ where
    (just _) → true
    nothing  → false
  where
  open Data.Maybe using (_>>=_)

main : IO ⊤
main = do
  fPath ∷ pPath ∷ [] ← getArgs
    where _ → putStrLn $ toCostring "usage: Checker foobar.cnf foobar.lrat"
  fStr ← readFiniteFile fPath
  pStr ← readFiniteFile pPath
  case runCheck fStr pStr of λ where
    nothing      → putStrLn $ toCostring "parse error"
    (just true)  → putStrLn $ toCostring "ok"
    (just false) → putStrLn $ toCostring "invalid proof"
  where
  open IO.Primitive using (_>>=_)
