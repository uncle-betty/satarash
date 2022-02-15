module Tseytin where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; _xor_ ; _≟_)
open import Data.Bool.Properties using (∧-identityʳ ; ∨-zeroʳ)
open import Data.Empty using (⊥)
open import Data.List using (List ; _∷_ ; [] ; [_] ; _++_ ; length)
open import Data.List.Relation.Binary.Equality.DecPropositional (_≟_) using (_≡?_)
open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s ; _<_)
open import Data.Nat.Properties using (≤-refl ; <-irrefl ; <-trans)
open import Data.Product using (∃-syntax ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_ ; _|>_ ; case_of_)
open import Relation.Binary.PropositionalEquality using (
    _≡_ ; refl ; sym ; cong ; trans ; _≢_ ; ≢-sym ;
    ≡-≟-identity ; ≢-≟-identity ; module ≡-Reasoning
  )
open import Relation.Nullary using (Dec ; yes ; no ; _because_ ; ofʸ ; ofⁿ)
open import Relation.Nullary.Negation using (contradiction)
open import Tactic.Cong using (cong!)

x∧x≡x : ∀ x → x ∧ x ≡ x
x∧x≡x false = refl
x∧x≡x true  = refl

¬¬x≡x : ∀ x → not (not x) ≡ x
¬¬x≡x false = refl
¬¬x≡x true  = refl

infix 4 _↔_ _↮_

_↔_ : (x y : Bool) → Bool
false ↔ false = true
false ↔ true  = false
true  ↔ false = false
true  ↔ true  = true

_↮_ : (x y : Bool) → Bool
x ↮ y = not (x ↔ y)

↔⇒≡ : ∀ {x y} → (x ↔ y) ≡ true → x ≡ y
↔⇒≡ {false} {false} _ = refl
↔⇒≡ {true}  {true}  _ = refl

x↔x : ∀ x → (x ↔ x) ≡ true
x↔x false = refl
x↔x true  = refl

↮-unsat⇒≡ : ∀ {x y} → (x ↮ y) ≡ false → x ≡ y
↮-unsat⇒≡ {x} {y} p = ↔⇒≡ (trans (sym (¬¬x≡x (x ↔ y))) (cong not p))

t↔x≡x : ∀ x → (true ↔ x) ≡ x
t↔x≡x false = refl
t↔x≡x true  = refl

f↔x≡¬x : ∀ x → (false ↔ x) ≡ not x
f↔x≡¬x false = refl
f↔x≡¬x true  = refl

∧-↔ : ∀ x y → x ∧ (y ↔ y) ≡ x
∧-↔ x false = ∧-identityʳ x
∧-↔ x true  = ∧-identityʳ x

∧-exp-✓ : ∀ x y r → (x ∧ y ↔ r) ≡ (not x ∨ not y ∨ r) ∧ (x ∨ not r) ∧ (y ∨ not r)
∧-exp-✓ false y    false = sym (∨-zeroʳ y)
∧-exp-✓ false y    true  = refl
∧-exp-✓ true false r     = f↔x≡¬x r
∧-exp-✓ true true  r     = trans (t↔x≡x r) (sym (∧-identityʳ r))

∨-exp-✓ : ∀ x y r → (x ∨ y ↔ r) ≡ (x ∨ y ∨ not r) ∧ (not x ∨ r) ∧ (not y ∨ r)
∨-exp-✓ false false r = trans (f↔x≡¬x r) (sym (∧-identityʳ (not r)))
∨-exp-✓ false true  r = t↔x≡x r
∨-exp-✓ true  false r = trans (t↔x≡x r) (sym (∧-identityʳ r))
∨-exp-✓ true  true  r = trans (t↔x≡x r) (sym (x∧x≡x r))

not-exp-✓ : ∀ x r → (not x ↔ r) ≡ (not x ∨ not r) ∧ (x ∨ r)
not-exp-✓ false r = t↔x≡x r
not-exp-✓ true  r = trans (f↔x≡¬x r) (sym (∧-identityʳ (not r)))

xor-exp-✓ : ∀ x y r →
  (x xor y ↔ r) ≡ (not x ∨ not y ∨ not r) ∧ (x ∨ y ∨ not r) ∧ (x ∨ not y ∨ r) ∧ (not x ∨ y ∨ r)
xor-exp-✓ false false r = trans (f↔x≡¬x r) (sym (∧-identityʳ (not r)))
xor-exp-✓ false true  r = trans (t↔x≡x r) (sym (∧-identityʳ r))
xor-exp-✓ true  false r = t↔x≡x r
xor-exp-✓ true  true  r = trans (f↔x≡¬x r) (sym (∧-identityʳ (not r)))

Address : Set
Address = List Bool

Assignment : Set
Assignment = Address → Bool

data Formula (S : Set) : Set where
  varᶠ : Address → Formula S
  tmpᶠ : {S} → Address → Formula S
  andᶠ : Formula S → Formula S → Formula S
  orᶠ  : Formula S → Formula S → Formula S
  notᶠ : Formula S → Formula S
  xorᶠ : Formula S → Formula S → Formula S
  iffᶠ : Formula S → Formula S → Formula S

f₁ : Formula ⊥
f₁ = orᶠ (varᶠ (false ∷ [])) (andᶠ (varᶠ (true ∷ [])) (varᶠ (true ∷ [])))

eval : {S : Set} → Assignment → Assignment → Formula S → Bool
eval v t (varᶠ x)   = v x
eval v t (tmpᶠ x)   = t x
eval v t (andᶠ x y) = eval v t x ∧ eval v t y
eval v t (orᶠ x y)  = eval v t x ∨ eval v t y
eval v t (notᶠ x)   = not (eval v t x)
eval v t (xorᶠ x y) = eval v t x xor eval v t y
eval v t (iffᶠ x y) = eval v t x ↔ eval v t y

flatten : Address → Formula ⊥ → Formula ⊤

flatten₀ : Address → Address → Formula ⊤
flatten₀ n x = iffᶠ (tmpᶠ n) (varᶠ x)

flatten₁ : Address → (Formula ⊤ → Formula ⊤) → Formula ⊥ → Formula ⊤
flatten₁ n op x =
  let s = flatten (n ++ [ false ]) x in
  andᶠ (iffᶠ (tmpᶠ n) (op (tmpᶠ (n ++ [ false ])))) s

flatten₂ : Address → (Formula ⊤ → Formula ⊤ → Formula ⊤) → Formula ⊥ → Formula ⊥ → Formula ⊤
flatten₂ n op x y =
  let sˡ = flatten (n ++ [ false ]) x in
  let sʳ = flatten (n ++ [ true ]) y in
  (andᶠ (andᶠ (iffᶠ (tmpᶠ n) (op (tmpᶠ (n ++ [ false ])) (tmpᶠ (n ++ [ true ])))) sˡ) sʳ)

flatten n (varᶠ x)   = flatten₀ n x
flatten n (andᶠ x y) = flatten₂ n andᶠ x y
flatten n (orᶠ x y)  = flatten₂ n orᶠ x y
flatten n (notᶠ x)   = flatten₁ n notᶠ x
flatten n (xorᶠ x y) = flatten₂ n xorᶠ x y
flatten n (iffᶠ x y) = flatten₂ n iffᶠ x y

makeTrue : Assignment → Formula ⊥ → Assignment

makeTrue₁ : Assignment → (Bool → Bool) → Formula ⊥ → Assignment
makeTrue₁ v op x =
  let t′ = makeTrue v x in
    λ where
      []      → op (t′ [])
      (_ ∷ n) → t′ n

makeTrue₂ : Assignment → (Bool → Bool → Bool) → Formula ⊥ → Formula ⊥ → Assignment
makeTrue₂ v op x y =
  let tˡ = makeTrue v x in
  let tʳ = makeTrue v y in
    λ where
      []          → op (tˡ []) (tʳ [])
      (false ∷ n) → tˡ n
      (true ∷ n)  → tʳ n

makeTrue v (varᶠ x)   = λ _ → v x
makeTrue v (andᶠ x y) = makeTrue₂ v _∧_ x y
makeTrue v (orᶠ x y)  = makeTrue₂ v _∨_ x y
makeTrue v (notᶠ x)   = makeTrue₁ v not x
makeTrue v (xorᶠ x y) = makeTrue₂ v _xor_ x y
makeTrue v (iffᶠ x y) = makeTrue₂ v _↔_ x y

-- XXX - how to avoid repetition in this proof?
prefixLemma : ∀ m n v t f → eval v t (flatten (m ∷ n) f) ≡ eval v (t ∘ (m ∷_)) (flatten n f)
prefixLemma m n v t (varᶠ x) = refl
prefixLemma m n v t (andᶠ x y)
  rewrite sym (prefixLemma m (n ++ [ false ]) v t x)
  rewrite sym (prefixLemma m (n ++ [ true ]) v t y)
  = refl
prefixLemma m n v t (orᶠ x y)
  rewrite sym (prefixLemma m (n ++ [ false ]) v t x)
  rewrite sym (prefixLemma m (n ++ [ true ]) v t y)
  = refl
prefixLemma m n v t (notᶠ x)
  rewrite sym (prefixLemma m (n ++ [ false ]) v t x)
  = refl
prefixLemma m n v t (xorᶠ x y)
  rewrite sym (prefixLemma m (n ++ [ false ]) v t x)
  rewrite sym (prefixLemma m (n ++ [ true ]) v t y)
  = refl
prefixLemma m n v t (iffᶠ x y)
  rewrite sym (prefixLemma m (n ++ [ false ]) v t x)
  rewrite sym (prefixLemma m (n ++ [ true ]) v t y)
  = refl

-- XXX - how to avoid repetition in this proof?
makeTrue-✓₁ : ∀ v f → eval v (makeTrue v f) (flatten [] f) ≡ true
makeTrue-✓₁ v (varᶠ x) = x↔x (v x)
makeTrue-✓₁ v (andᶠ x y)
  rewrite prefixLemma false [] v (makeTrue v (andᶠ x y)) x
  rewrite prefixLemma true [] v (makeTrue v (andᶠ x y)) y
  rewrite makeTrue-✓₁ v x
  rewrite makeTrue-✓₁ v y
  rewrite x↔x (makeTrue v x [] ∧ makeTrue v y [])
  = refl
makeTrue-✓₁ v (orᶠ x y)
  rewrite prefixLemma false [] v (makeTrue v (orᶠ x y)) x
  rewrite prefixLemma true [] v (makeTrue v (orᶠ x y)) y
  rewrite makeTrue-✓₁ v x
  rewrite makeTrue-✓₁ v y
  rewrite x↔x (makeTrue v x [] ∨ makeTrue v y [])
  = refl
makeTrue-✓₁ v (notᶠ x)
  rewrite prefixLemma false [] v (makeTrue v (notᶠ x)) x
  rewrite makeTrue-✓₁ v x
  rewrite x↔x (not (makeTrue v x []))
  = refl
makeTrue-✓₁ v (xorᶠ x y)
  rewrite prefixLemma false [] v (makeTrue v (xorᶠ x y)) x
  rewrite prefixLemma true [] v (makeTrue v (xorᶠ x y)) y
  rewrite makeTrue-✓₁ v x
  rewrite makeTrue-✓₁ v y
  rewrite x↔x (makeTrue v x [] xor makeTrue v y [])
  = refl
makeTrue-✓₁ v (iffᶠ x y)
  rewrite prefixLemma false [] v (makeTrue v (iffᶠ x y)) x
  rewrite prefixLemma true [] v (makeTrue v (iffᶠ x y)) y
  rewrite makeTrue-✓₁ v x
  rewrite makeTrue-✓₁ v y
  rewrite x↔x (makeTrue v x [] ↔ makeTrue v y [])
  = refl

makeTrue-✓₂ : ∀ v t f → makeTrue v f [] ≡ eval v t f
makeTrue-✓₂ v t (varᶠ x)   = refl
makeTrue-✓₂ v t (andᶠ x y) rewrite makeTrue-✓₂ v t x | makeTrue-✓₂ v t y = refl
makeTrue-✓₂ v t (orᶠ x y)  rewrite makeTrue-✓₂ v t x | makeTrue-✓₂ v t y = refl
makeTrue-✓₂ v t (notᶠ x)   rewrite makeTrue-✓₂ v t x = refl
makeTrue-✓₂ v t (xorᶠ x y) rewrite makeTrue-✓₂ v t x | makeTrue-✓₂ v t y = refl
makeTrue-✓₂ v t (iffᶠ x y) rewrite makeTrue-✓₂ v t x | makeTrue-✓₂ v t y = refl

transform₁ : Formula ⊥ → Formula ⊤
transform₁ f = andᶠ (tmpᶠ []) (flatten [] f)

transform₁-✓ : ∀ v t f → eval v (makeTrue v f) (transform₁ f) ≡ eval v t f
transform₁-✓ v t f
  rewrite makeTrue-✓₁ v f
  rewrite makeTrue-✓₂ v t f
  = ∧-identityʳ (eval v t f)

f₂ : Formula ⊤
f₂ = transform₁ f₁
