{-# OPTIONS --allow-exec #-}

module Satarash.Examples where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; _xor_ ; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)

open import Satarash.Tseytin using (_⇒_ ; _⇔_)
open import Satarash.Tactic using (bool-∀ ; word-∀)
open import Satarash.Word using (
    Word ; ~ ; _∧ʷ_ ; _∨ʷ_ ; _xorʷ_ ; ↕ ; _⊞_ ; _⊟_ ; _⊠_ ; _<ˡ_ ; _≤ˡ_ ; _>ˡ_ ; _≥ˡ_
  )

--- booleans ---------------------------------------------------------------------------------------

-- something simple
bool₁ : ∀ x y → x ∧ y ≡ y ∧ x
bool₁ = bool-∀

-- slightly more complex
bool₂ : ∀ x y z → x ∧ (y ∨ z) ≡ x ∧ y ∨ x ∧ z
bool₂ = bool-∀

-- one assumption
bool₃ : ∀ x y → x ≡ not y → x ∧ y ≡ false
bool₃ = bool-∀

-- two assumptions
bool₄ : ∀ x y → x ≡ true → y ≡ false → x ∧ not y ≡ true
bool₄ = bool-∀

-- needs explicit type
bool₅ : (x : Bool) → x ≡ x
bool₅ = bool-∀

-- try xor
bool₆ : ∀ x y → x ∨ y ≡ x xor y xor (x ∧ y)
bool₆ = bool-∀

-- try if-then-else
bool₇ : ∀ x y z → (if x then y else z) ≡ (x ∧ y ∨ not x ∧ z)
bool₇ = bool-∀

-- try implication, if-and-only-if
bool₈ : ∀ x y → (x ⇒ y) ≡ true → (y ⇒ x) ≡ true → (x ⇔ y) ≡ true
bool₈ = bool-∀

--- words ------------------------------------------------------------------------------------------

-- XXX - some of the following are currently exponential in the word width

-- and, or, xor
word₁ : (x y : Word 3) → x ∨ʷ y ≡ x xorʷ y xorʷ x ∧ʷ y
word₁ = word-∀

-- not
word₂ : (x : Word 3) → ~ (~ x) ≡ x
word₂ = word-∀

-- addition, subtraction
word₃ : (x y : Word 3) → x ⊞ y ⊟ x ≡ y
word₃ = word-∀

-- multiplication
word₄ : (x y : Word 3) → x ⊠ y ≡ y ⊠ x
word₄ = word-∀

-- negation
word₅ : (x y : Word 3) → x ⊟ y ≡ x ⊞ (↕ y)
word₅ = word-∀

-- less than, greater than
word₆ : (x y : Word 3) → x <ˡ y → y >ˡ x
word₆ = word-∀

-- less than or equal to, greater than or equal to
word₇ : (x y : Word 3) → x ≤ˡ y → y ≥ˡ x
word₇ = word-∀

-- not equal to
word₈ : (x y : Word 3) → x <ˡ y → x ≢ y
word₈ = word-∀
