module Checker where

open import Agda.Builtin.IO using () renaming (IO to IO′)
open import Codata.Musical.Costring using (toCostring)
open import Data.Bool using (Bool ; true ; false)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_)
open import Data.String using (String)
open import Data.Unit using (⊤)
open import Function using (_$_ ; _∘_ ; case_of_)
open import IO.Primitive using (IO ; readFiniteFile ; putStrLn)
open import Level using (0ℓ ; Lift ; lift)

open import Parser using (parseParameters ; parseProof ; parseFormula)
open import Verifier using (Formula ; Proof ; checkLRAT)

runCheck : String → String → Maybe Bool
runCheck fStr pStr = do
  (bitsᵛ , bitsᶜ , pStr′) ← parseParameters pStr
  proof ← parseProof bitsᵛ bitsᶜ pStr′
  formula ← parseFormula bitsᵛ bitsᶜ fStr
  just $ case checkLRAT bitsᶜ formula proof of λ where
    (just _) → true
    nothing  → false
  where
  open Data.Maybe using (_>>=_)

main : IO′ ⊤
main = do
  formulaStr ← readFiniteFile "satarash.cnf"
  proofStr ← readFiniteFile "satarash.lrat"
  case runCheck formulaStr proofStr of λ where
    nothing      → putStrLn $ toCostring "parse error"
    (just true)  → putStrLn $ toCostring "ok"
    (just false) → putStrLn $ toCostring "invalid proof"
  where
  open IO.Primitive using (_>>=_)
