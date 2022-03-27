{-# OPTIONS --guardedness #-}

module Satarash.Checker where

open import Data.Bool using (Bool ; true ; false)
open import Data.Char using (Char)
open import Data.List using (List ; [] ; _∷_)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_)
open import Data.String using (String ; toList)
open import Data.Unit using (⊤)
open import Function using (_$_ ; _∘_ ; case_of_)
open import IO using (Main ; run ; readFiniteFile ; putStrLn)
open import System.Environment using (getArgs)

open import Satarash.Parser using (parse)
open import Satarash.Verifier using (Formula ; Proof ; checkLRAT)

bitsᶜ : ℕ
bitsᶜ = 24

runCheck : List Char → List Char → Maybe Bool
runCheck fStr pStr = do
  f , p ← parse bitsᶜ fStr pStr
  just $ case checkLRAT bitsᶜ f p of λ where
    (just _) → true
    nothing  → false
  where
  open Data.Maybe using (_>>=_)

main : Main
main = run $ do
  fPath ∷ pPath ∷ [] ← getArgs
    where _ → putStrLn "usage: Checker foobar.cnf foobar.lrat"
  fStr ← readFiniteFile fPath
  pStr ← readFiniteFile pPath
  case runCheck (toList fStr) (toList pStr) of λ where
    nothing      → putStrLn "parse error"
    (just true)  → putStrLn "ok"
    (just false) → putStrLn "invalid proof"
  where
  open IO using (_>>=_)
