{-# OPTIONS --allow-exec #-}

module Satarash.Examples where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; _xor_ ; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Satarash.Tseytin using (_⇒_ ; _⇔_)
open import Satarash.Tactic using (satarash-∀)

-- something simple
test₁ : ∀ x y → x ∧ y ≡ y ∧ x
test₁ = satarash-∀

-- slightly more complex
test₂ : ∀ x y z → x ∧ (y ∨ z) ≡ x ∧ y ∨ x ∧ z
test₂ = satarash-∀

-- one assumption
test₃ : ∀ x y → x ≡ not y → x ∧ y ≡ false
test₃ = satarash-∀

-- two assumptions
test₄ : ∀ x y → x ≡ true → y ≡ false → x ∧ not y ≡ true
test₄ = satarash-∀

-- needs explicit type
test₅ : (x : Bool) → x ≡ x
test₅ = satarash-∀

-- try xor
test₆ : ∀ x y → x ∨ y ≡ x xor y xor (x ∧ y)
test₆ = satarash-∀

-- try if-then-else
test₇ : ∀ x y z → (if x then y else z) ≡ (x ∧ y ∨ not x ∧ z)
test₇ = satarash-∀

-- try implication, if-and-only-if
test₈ : ∀ x y → (x ⇒ y) ≡ true → (y ⇒ x) ≡ true → (x ⇔ y) ≡ true
test₈ = satarash-∀
