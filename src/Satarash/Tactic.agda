{-# OPTIONS --allow-exec #-}

module Satarash.Tactic where

open import Data.Bool using (Bool ; false ; true ; _∧_ ; _∨_ ; not ; _xor_ ; if_then_else_)
open import Data.Char using (Char)
open import Function using (_∘_ ; _$_ ; case_of_ ; const)
open import Data.List using (List ; [] ; _∷_ ; [_] ; length ; map ; _++_ ; _∷ʳ_)
open import Data.Maybe using (Maybe ; nothing ; just ; fromMaybe)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _∸_)
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃-syntax)
open import Data.String using (String ; fromList) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality using (
    _≡_ ; refl ; cong ; trans ; module ≡-Reasoning
  )
open import Reflection using (
    TC ; typeError ; inferType ; quoteTC ; unify ; debugPrint ;
    ErrorPart ; strErr ; termErr ; nameErr
  )
open import Reflection.AST using (
    Term ; def ; con ; lam ; pi ; var ; lit ; nat ; Abs ; abs ; Arg ; arg ;
    arg-info ; visible ; modality ; relevant ; quantity-ω ;
    showTerm
  )
open import Reflection.External using (CmdSpec ; cmdSpec ; runCmdTC ; StdOut)
open import Reflection.TCM.Syntax using (pure ; _>>=_ ; _>>_ ; _<$>_)

open import Data.Tree.AVL.Map <-strictTotalOrder using (Map ; empty ; insert ; lookup)

open import Satarash.Tseytin using (
    _⇔_ ; _⇒_ ;
    Formula₀ ; con₀ ; var₀ ; and₀ ; or₀ ; not₀ ; xor₀ ; iff₀ ; imp₀ ; ite₀ ; eval₀ ; show₀ ;
    Formula₆ ; transform₆ ; eval₆ ; Formula₇ ; transform₇ ; eval₇ ; transform₇-✓ ;
    maxVar
  )

import Satarash.Parser as P
import Satarash.Tseytin as T
import Satarash.Verifier as V

printParse-✓ : ∀ nᵛ nᶜ f₀ ps f₇ p →
  P.parse (P.printFormula nᵛ nᶜ (transform₆ (not₀ f₀))) ps ≡ just (f₇ , p) →
  transform₇ (not₀ f₀) ≡ just f₇
printParse-✓ nᵛ nᶜ f₀ ps f₇ p p₁ = P.printParse-✓ nᵛ nᶜ (transform₆ (not₀ f₀)) ps f₇ p p₁

postulate
  trust : (f₀ : Formula₀) → ∃[ f₇ ] transform₇ (not₀ f₀) ≡ just f₇ × ∀ v → eval₇ v f₇ ≡ false

runSatarash : (f₀ : Formula₀) →
  TC (∃[ f₇ ] transform₇ (not₀ f₀) ≡ just f₇ × ∀ v → eval₇ v f₇ ≡ false)
runSatarash f₀ = do
    let f₆ = transform₆ (not₀ f₀)
    let nᵛ = maxVar f₆
    let nᶜ = length f₆
    let cs = P.printFormula nᵛ nᶜ f₆

    debugPrint "satarash" 15 (strErr "DIMACS = " ∷ strErr (fromList cs) ∷ [])

    "ok\n" ← runCmdTC (cmdSpec "satarash.sh" [] (fromList cs))
      where out → typeError (strErr "satarash.sh output: " ∷ strErr out ∷ [])

    pure (trust f₀)

not-injective : ∀ {x y} → not x ≡ not y → x ≡ y
not-injective {true}  {true}  refl = refl
not-injective {false} {false} refl = refl

unsat→∀ : ∀ f₀ f₇ → transform₇ (not₀ f₀) ≡ just f₇ → (∀ v → eval₇ v f₇ ≡ false) →
  ∀ v → eval₀ v f₀ ≡ true
unsat→∀ f₀ f₇ p₁ p₂ v = not-injective $
  begin
    not (eval₀ v f₀)                   ≡˘⟨ transform₇-✓ v (not₀ f₀) f₇ p₁ ⟩
    eval₇ (T.makeTrue₅ v (not₀ f₀)) f₇ ≡⟨ p₂ (T.makeTrue₅ v (not₀ f₀)) ⟩
    false                              ≡⟨⟩
    not true                           ∎
  where open ≡-Reasoning

to-⇒ : ∀ {x y} → (x ≡ true → y ≡ true) → (x ⇒ y) ≡ true
to-⇒ {true}  {true}  p = refl
to-⇒ {true}  {false} p = p refl
to-⇒ {false} {true}  p = refl
to-⇒ {false} {false} p = refl

from-⇒ : ∀ {x y} → (x ⇒ y) ≡ true → x ≡ true → y ≡ true
from-⇒ {.true} {true} refl refl = refl

to-⇔ : ∀ {x y} → x ≡ y → (x ⇔ y) ≡ true
to-⇔ {true}  {.true}  refl = refl
to-⇔ {false} {.false} refl = refl

from-⇔ : ∀ {x y} → (x ⇔ y) ≡ true → x ≡ y
from-⇔ {true}  {true}  refl = refl
from-⇔ {false} {false} refl = refl

data RelType : Set where
  rel-≡      : RelType

showRelType : RelType → String
showRelType rel-≡      = "rel-≡"

getVisible : List (Arg Term) → ℕ → TC Term
getVisible []                                n       = typeError (strErr "bad ≡ in goal" ∷ [])
getVisible (arg (arg-info visible _) x ∷ _ ) zero    = pure x
getVisible (arg (arg-info visible _) _ ∷ as) (suc n) = getVisible as n
getVisible (_                          ∷ as) n       = getVisible as n

translateFormula : ℕ → Term → TC Formula₀
translateFormula n (con (quote true) _)  = pure (con₀ true)
translateFormula n (con (quote false) _) = pure (con₀ false)
translateFormula n (var x _)             = pure (var₀ (n ∸ (suc x)))
translateFormula n (def (quote _∧_) (arg _ t₁ ∷ arg _ t₂ ∷ [])) = do
  f₀₁ ← translateFormula n t₁
  f₀₂ ← translateFormula n t₂
  pure (and₀ f₀₁ f₀₂)
translateFormula n (def (quote _∨_) (arg _ t₁ ∷ arg _ t₂ ∷ [])) = do
  f₀₁ ← translateFormula n t₁
  f₀₂ ← translateFormula n t₂
  pure (or₀ f₀₁ f₀₂)
translateFormula n (def (quote not) (arg _ t ∷ [])) = do
  f₀ ← translateFormula n t
  pure (not₀ f₀)
translateFormula n (def (quote _xor_) (arg _ t₁ ∷ arg _ t₂ ∷ [])) = do
  f₀₁ ← translateFormula n t₁
  f₀₂ ← translateFormula n t₂
  pure (xor₀ f₀₁ f₀₂)
translateFormula n (def (quote _⇔_) (arg _ t₁ ∷ arg _ t₂ ∷ [])) = do
  f₀₁ ← translateFormula n t₁
  f₀₂ ← translateFormula n t₂
  pure (iff₀ f₀₁ f₀₂)
translateFormula n (def (quote _⇒_) (arg _ t₁ ∷ arg _ t₂ ∷ [])) = do
  f₀₁ ← translateFormula n t₁
  f₀₂ ← translateFormula n t₂
  pure (imp₀ f₀₁ f₀₂)
-- XXX - don't assume that there are two implicits
translateFormula n (def (quote if_then_else_) (_ ∷ _ ∷ arg _ t₁ ∷ arg _ t₂ ∷ arg _ t₃ ∷ [])) = do
  f₀₁ ← translateFormula n t₁
  f₀₂ ← translateFormula n t₂
  f₀₃ ← translateFormula n t₃
  pure (ite₀ f₀₁ f₀₂ f₀₃)
translateFormula n t = typeError (strErr "bad formula part: " ∷ termErr t ∷ [])

translatePart : ℕ → Term → TC (RelType × Formula₀)
translatePart n (def (quote _≡_) args) = do
  lhs ← getVisible args 0
  rhs ← getVisible args 1
  fˡ ← translateFormula n lhs
  fʳ ← translateFormula n rhs
  pure (rel-≡ , iff₀ fˡ fʳ)
translatePart n t = typeError (strErr "bad goal part: " ∷ termErr t ∷ [])

translateParts : ℕ → Term → TC (List RelType × Formula₀)
translateParts n (pi (arg _ t₁) (abs _ t₂)) = do
  r  , f₀₁ ← translatePart  n t₁
  rs , f₀₂ ← translateParts (suc n) t₂
  pure (r ∷ rs , imp₀ f₀₁ f₀₂)
translateParts n t = do
  r , f₀ ← translatePart n t
  pure ([ r ] , f₀)

collectVariables : Term → TC (List String × Term)
collectVariables (pi (arg _ (def (quote Bool) _)) (abs v t)) = do
  vs , t′ ← collectVariables t
  pure (v ∷ vs , t′)
collectVariables t = pure ([] , t)

collectParts : ℕ → Term → List String
collectParts n (pi (arg _ _) (abs _ t)) = ("a" ++ˢ show n) ∷ collectParts (suc n) t
collectParts n _                        = []

translateGoal : Term → TC (List String × List String × List RelType × Formula₀)
translateGoal t = do
  vs , t′ ← collectVariables t
  let as = collectParts 1 t′
  rs , f₀ ← translateParts (length vs) t′
  pure (vs , as , rs , f₀)

makeArgument : Term → Arg Term
makeArgument t = arg (arg-info visible (modality relevant quantity-ω)) t

makeLambdas : List String → Term → Term
makeLambdas []       t = t
makeLambdas (v ∷ vs) t = lam visible (abs v (makeLambdas vs t))

makeVariableMap : ℕ → ℕ → ℕ → Term
makeVariableMap zero     n↑ o = def (quote empty) []
makeVariableMap (suc n↓) n↑ o = def (quote insert) (arg₁ ∷ arg₂ ∷ arg₃ ∷ [])
  where
  arg₁ = makeArgument (lit (nat n↑))
  arg₂ = makeArgument (var (suc n↓ + o) []) -- suc, because of makeAssignment's lambda
  arg₃ = makeArgument (makeVariableMap n↓ (suc n↑) o)

makeAssignment : ℕ → ℕ → Term
makeAssignment n o = lam visible (abs "n" (def (quote fromMaybe) (arg₂₁ ∷ arg₂₂ ∷ [])))
  where
  arg₁₁ = makeArgument (var 0 [])
  arg₁₂ = makeArgument (makeVariableMap n zero o)
  arg₂₁ = makeArgument (con (quote false) [])
  arg₂₂ = makeArgument (def (quote lookup) (arg₁₁ ∷ arg₁₂ ∷ []))

makeUnsatForAll : List String → List String → Term → Term → Term → Term → Term
makeUnsatForAll vs as f₀ f₇ p₁ p₂ = (def (quote unsat→∀) (arg₁ ∷ arg₂ ∷ arg₃ ∷ arg₄ ∷ arg₅ ∷ []))
  where
  arg₁ = makeArgument f₀
  arg₂ = makeArgument f₇
  arg₃ = makeArgument p₁
  arg₄ = makeArgument p₂
  arg₅ = makeArgument (makeAssignment (length vs) (length as))

makeTransformed : List RelType → Term → Term
makeTransformed []               t = t
makeTransformed (rel-≡ ∷ [])     t = def (quote from-⇔) (arg₁ ∷ [])
  where
  arg₁ = makeArgument t
makeTransformed (rel-≡ ∷ r ∷ rs) t = makeTransformed (r ∷ rs) t′
  where
  arg₁₁ = makeArgument (var (length rs) [])
  arg₂₁ = makeArgument t
  arg₂₂ = makeArgument (def (quote to-⇔) (arg₁₁ ∷ []))
  t′ = def (quote from-⇒) (arg₂₁ ∷ arg₂₂ ∷ [])

makeProofFromUnsat : List String → List String → List RelType → Term → Term → Term → Term → Term
makeProofFromUnsat vs as rs f₀ f₇ p₁ p₂ =
  makeLambdas (vs ++ as) transformed
  where
  unsatForAll = makeUnsatForAll vs as f₀ f₇ p₁ p₂
  transformed = makeTransformed rs unsatForAll

macro
  satarash-∀ : Term → TC ⊤
  satarash-∀ hole = do
    goal ← inferType hole

    vs , as , rs , f₀ ← translateGoal goal

    debugPrint "satarash" 5 (strErr "vs =" ∷ map (strErr ∘ (" " ++ˢ_)) vs)
    debugPrint "satarash" 5 (strErr "as =" ∷ map (strErr ∘ (" " ++ˢ_)) as)
    debugPrint "satarash" 5 (strErr "rs =" ∷ map (strErr ∘ (" " ++ˢ_) ∘ showRelType) rs)
    debugPrint "satarash" 5 (strErr "f₀ = " ∷ strErr (show₀ f₀) ∷ [])

    f₇ , p₁ , p₂ ← runSatarash f₀

    f₀′ ← quoteTC f₀
    f₇′ ← quoteTC f₇
    p₁′ ← quoteTC p₁
    p₂′ ← quoteTC p₂

    let proof = makeProofFromUnsat vs as rs f₀′ f₇′ p₁′ p₂′

    debugPrint "satarash" 10 (strErr "proof = " ∷ termErr proof ∷ [])

    unify hole proof
