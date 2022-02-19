-- FIXME - some proofs contain a hilarious amount of duplication

module Tseytin where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; _xor_ ; _≟_)
open import Data.Bool.Properties using (∧-identityʳ ; ∧-idem)
open import Data.Empty using (⊥)
open import Data.List using (List ; _∷_ ; [] ; [_] ; _++_ ; length)
open import Data.List.Relation.Binary.Equality.DecPropositional (_≟_) using (_≡?_)
open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s ; _<_)
  renaming (_≟_ to _≟ⁿ_ ; _<?_ to _<?ⁿ_)
open import Data.Nat.Properties using (
    ≤-refl ; <-irrefl ; <-trans ; <-transˡ ;
    <⇒≢ ; <⇒≯ ; <⇒≤ ; ≤⇒≯ ; <-irrelevant ; module ≤-Reasoning
  )
open import Data.Product using (∃-syntax ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_ ; _|>_ ; case_of_)
open import Relation.Binary.PropositionalEquality using (
    _≡_ ; refl ; sym ; cong ; cong₂ ; trans ; _≢_ ; ≢-sym ;
    ≡-≟-identity ; ≢-≟-identity ; module ≡-Reasoning
  )
open import Relation.Nullary using (¬_ ; Dec ; yes ; no ; _because_ ; ofʸ ; ofⁿ)
open import Relation.Nullary.Decidable using (dec-yes-irr ; dec-no)
open import Relation.Nullary.Negation using (contradiction)
open import Tactic.Cong using (cong!)

infix 4 _↔_

_↔_ : (x y : Bool) → Bool
false ↔ false = true
false ↔ true  = false
true  ↔ false = false
true  ↔ true  = true

x↔x : ∀ x → (x ↔ x) ≡ true
x↔x false = refl
x↔x true  = refl

x↔t≡x : ∀ x → (x ↔ true) ≡ x
x↔t≡x false = refl
x↔t≡x true  = refl

x↔f≡¬x : ∀ x → (x ↔ false) ≡ not x
x↔f≡¬x false = refl
x↔f≡¬x true  = refl

∧-sub-✓ : ∀ x y r → (r ↔ x ∧ y) ≡ (not x ∨ not y ∨ r) ∧ (x ∨ not r) ∧ (y ∨ not r)
∧-sub-✓ false false r = trans (x↔f≡¬x r) (sym (∧-idem (not r)))
∧-sub-✓ false true  r = trans (x↔f≡¬x r) (sym (∧-identityʳ (not r)))
∧-sub-✓ true false  r = x↔f≡¬x r
∧-sub-✓ true true   r = trans (x↔t≡x r) (sym (∧-identityʳ r))

∨-sub-✓ : ∀ x y r → (r ↔ x ∨ y) ≡ (x ∨ y ∨ not r) ∧ (not x ∨ r) ∧ (not y ∨ r)
∨-sub-✓ false false r = trans (x↔f≡¬x r) (sym (∧-identityʳ (not r)))
∨-sub-✓ false true  r = x↔t≡x r
∨-sub-✓ true  false r = trans (x↔t≡x r) (sym (∧-identityʳ r))
∨-sub-✓ true  true  r = trans (x↔t≡x r) (sym (∧-idem r))

not-sub-✓ : ∀ x r → (r ↔ not x) ≡ (not x ∨ not r) ∧ (x ∨ r)
not-sub-✓ false r = x↔t≡x r
not-sub-✓ true  r = trans (x↔f≡¬x r) (sym (∧-identityʳ (not r)))

xor-sub-✓ : ∀ x y r →
  (r ↔ x xor y) ≡ (not x ∨ not y ∨ not r) ∧ (x ∨ y ∨ not r) ∧ (x ∨ not y ∨ r) ∧ (not x ∨ y ∨ r)
xor-sub-✓ false false r = trans (x↔f≡¬x r) (sym (∧-identityʳ (not r)))
xor-sub-✓ false true  r = trans (x↔t≡x r) (sym (∧-identityʳ r))
xor-sub-✓ true  false r = x↔t≡x r
xor-sub-✓ true  true  r = trans (x↔f≡¬x r) (sym (∧-identityʳ (not r)))

↔-sub-✓ : ∀ x y r →
  (r ↔ (x ↔ y)) ≡ (x ∨ y ∨ r) ∧ (not x ∨ not y ∨ r) ∧ (not x ∨ y ∨ not r) ∧ (x ∨ not y ∨ not r)
↔-sub-✓ false false r = trans (x↔t≡x r) (sym (∧-identityʳ r))
↔-sub-✓ false true  r = x↔f≡¬x r
↔-sub-✓ true  false r = trans (x↔f≡¬x r) (sym (∧-identityʳ (not r)))
↔-sub-✓ true  true  r = trans (x↔t≡x r) (sym (∧-identityʳ r))

data Formula (S A : Set) : Set where
  varᶠ : ℕ → Formula S A
  tmpᶠ : {S} → A → Formula S A
  andᶠ : Formula S A → Formula S A → Formula S A
  orᶠ  : Formula S A → Formula S A → Formula S A
  notᶠ : Formula S A → Formula S A
  xorᶠ : Formula S A → Formula S A → Formula S A
  iffᶠ : Formula S A → Formula S A → Formula S A

Formula₀ : (S : Set) → Set
Formula₀ S = Formula ⊥ S

Formula₁ : Set
Formula₁ = Formula ⊤ (List Bool)

Formula₂ : Set
Formula₂ = Formula ⊤ ℕ

f₁ : Formula₀ ℕ
f₁ = orᶠ (varᶠ 0) (andᶠ (varᶠ 1) (varᶠ 1))

variable
  A : Set

eval : {S : Set} → (ℕ → Bool) → (A → Bool) → Formula S A → Bool
eval v t (varᶠ x)   = v x
eval v t (tmpᶠ x)   = t x
eval v t (andᶠ x y) = eval v t x ∧ eval v t y
eval v t (orᶠ x y)  = eval v t x ∨ eval v t y
eval v t (notᶠ x)   = not (eval v t x)
eval v t (xorᶠ x y) = eval v t x xor eval v t y
eval v t (iffᶠ x y) = eval v t x ↔ eval v t y

flatten : List Bool → Formula₀ A → Formula₁

flatten₀ : List Bool → ℕ → Formula₁
flatten₀ n x = iffᶠ (tmpᶠ n) (varᶠ x)

flatten₁ : List Bool → (Formula₁ → Formula₁) → Formula₀ A → Formula₁
flatten₁ n op x =
  let s = flatten (n ++ [ false ]) x in
  andᶠ (iffᶠ (tmpᶠ n) (op (tmpᶠ (n ++ [ false ])))) s

flatten₂ : List Bool → (Formula₁ → Formula₁ → Formula₁) → Formula₀ A → Formula₀ A → Formula₁
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

makeTrue : (ℕ → Bool) → Formula₀ A → (List Bool → Bool)

makeTrue₁ : (ℕ → Bool) → (Bool → Bool) → Formula₀ A → (List Bool → Bool)
makeTrue₁ v op x =
  let t′ = makeTrue v x in
    λ where
      []      → op (t′ [])
      (_ ∷ n) → t′ n

makeTrue₂ : (ℕ → Bool) → (Bool → Bool → Bool) → Formula₀ A → Formula₀ A → (List Bool → Bool)
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

evalCons : ∀ m n v t f → eval v t (flatten {A} (m ∷ n) f) ≡ eval v (t ∘ (m ∷_)) (flatten n f)
evalCons m n v t (varᶠ x) = refl
evalCons m n v t (andᶠ x y)
  rewrite sym (evalCons m (n ++ [ false ]) v t x)
  rewrite sym (evalCons m (n ++ [ true ]) v t y)
  = refl
evalCons m n v t (orᶠ x y)
  rewrite sym (evalCons m (n ++ [ false ]) v t x)
  rewrite sym (evalCons m (n ++ [ true ]) v t y)
  = refl
evalCons m n v t (notᶠ x)
  rewrite sym (evalCons m (n ++ [ false ]) v t x)
  = refl
evalCons m n v t (xorᶠ x y)
  rewrite sym (evalCons m (n ++ [ false ]) v t x)
  rewrite sym (evalCons m (n ++ [ true ]) v t y)
  = refl
evalCons m n v t (iffᶠ x y)
  rewrite sym (evalCons m (n ++ [ false ]) v t x)
  rewrite sym (evalCons m (n ++ [ true ]) v t y)
  = refl

makeTrue-✓₁ : ∀ v f → eval v (makeTrue {A} v f) (flatten [] f) ≡ true
makeTrue-✓₁ v (varᶠ x) = x↔x (v x)
makeTrue-✓₁ v (andᶠ x y)
  rewrite evalCons false [] v (makeTrue v (andᶠ x y)) x
  rewrite evalCons true [] v (makeTrue v (andᶠ x y)) y
  rewrite makeTrue-✓₁ v x
  rewrite makeTrue-✓₁ v y
  rewrite x↔x (makeTrue v x [] ∧ makeTrue v y [])
  = refl
makeTrue-✓₁ v (orᶠ x y)
  rewrite evalCons false [] v (makeTrue v (orᶠ x y)) x
  rewrite evalCons true [] v (makeTrue v (orᶠ x y)) y
  rewrite makeTrue-✓₁ v x
  rewrite makeTrue-✓₁ v y
  rewrite x↔x (makeTrue v x [] ∨ makeTrue v y [])
  = refl
makeTrue-✓₁ v (notᶠ x)
  rewrite evalCons false [] v (makeTrue v (notᶠ x)) x
  rewrite makeTrue-✓₁ v x
  rewrite x↔x (not (makeTrue v x []))
  = refl
makeTrue-✓₁ v (xorᶠ x y)
  rewrite evalCons false [] v (makeTrue v (xorᶠ x y)) x
  rewrite evalCons true [] v (makeTrue v (xorᶠ x y)) y
  rewrite makeTrue-✓₁ v x
  rewrite makeTrue-✓₁ v y
  rewrite x↔x (makeTrue v x [] xor makeTrue v y [])
  = refl
makeTrue-✓₁ v (iffᶠ x y)
  rewrite evalCons false [] v (makeTrue v (iffᶠ x y)) x
  rewrite evalCons true [] v (makeTrue v (iffᶠ x y)) y
  rewrite makeTrue-✓₁ v x
  rewrite makeTrue-✓₁ v y
  rewrite x↔x (makeTrue v x [] ↔ makeTrue v y [])
  = refl

makeTrue-✓₂ : ∀ v t f → makeTrue {A} v f [] ≡ eval v t f
makeTrue-✓₂ v t (varᶠ x)   = refl
makeTrue-✓₂ v t (andᶠ x y) rewrite makeTrue-✓₂ v t x | makeTrue-✓₂ v t y = refl
makeTrue-✓₂ v t (orᶠ x y)  rewrite makeTrue-✓₂ v t x | makeTrue-✓₂ v t y = refl
makeTrue-✓₂ v t (notᶠ x)   rewrite makeTrue-✓₂ v t x = refl
makeTrue-✓₂ v t (xorᶠ x y) rewrite makeTrue-✓₂ v t x | makeTrue-✓₂ v t y = refl
makeTrue-✓₂ v t (iffᶠ x y) rewrite makeTrue-✓₂ v t x | makeTrue-✓₂ v t y = refl

transform₁ : Formula₀ A → Formula₁
transform₁ f = andᶠ (tmpᶠ []) (flatten [] f)

transform₁-✓ : ∀ v t f → eval v (makeTrue {A} v f) (transform₁ f) ≡ eval v t f
transform₁-✓ v t f
  rewrite makeTrue-✓₁ v f
  rewrite makeTrue-✓₂ v t f
  = ∧-identityʳ (eval v t f)

f₂ : Formula₁
f₂ = transform₁ f₁

≡⇒≡? : ∀ {x y} → (p : x ≡ y) → x ≡? y ≡ yes p
≡⇒≡? = ≡-≟-identity _≡?_

≢⇒≡? : ∀ {x y} → x ≢ y → ∃[ p ] x ≡? y ≡ no p
≢⇒≡? = ≢-≟-identity _≡?_

≡⇒≟ⁿ : ∀ {x y} → (p : x ≡ y) → (x ≟ⁿ y) ≡ yes p
≡⇒≟ⁿ = ≡-≟-identity _≟ⁿ_

≢⇒≟ⁿ : ∀ {x y} → x ≢ y → ∃[ p ] (x ≟ⁿ y) ≡ no p
≢⇒≟ⁿ = ≢-≟-identity _≟ⁿ_

<⇒<? : ∀ {x y} → (p : x < y) → (x <?ⁿ y) ≡ yes p
<⇒<? {x} {y} p = dec-yes-irr (x <?ⁿ y) <-irrelevant p

≮⇒<? : ∀ {x y} → ¬ (x < y) → ∃[ p ] (x <?ⁿ y) ≡ no p
≮⇒<? {x} {y} p = dec-no (x <?ⁿ y) p

module _ where
  bin→ℕ : ℕ → (f : Formula₀ A) → ℕ × (List Bool → ℕ)

  module ⟨bin→ℕ⟩ where
    bin→ℕ₁ : ℕ → (x : Formula₀ A) → ℕ × (List Bool → ℕ)
    bin→ℕ₁ n x =
      let n′ , m = bin→ℕ n x in
      suc n′ , λ where
        []      → n′
        (_ ∷ a) → m a

    bin→ℕ₂ : ℕ → (x y : Formula₀ A) → ℕ × (List Bool → ℕ)
    bin→ℕ₂ n x y =
      let nˡ , mˡ = bin→ℕ n x in
      let nʳ , mʳ = bin→ℕ nˡ y in
      suc nʳ , λ where
        []          → nʳ
        (false ∷ a) → mˡ a
        (true ∷ a)  → mʳ a

  open ⟨bin→ℕ⟩

  bin→ℕ n (varᶠ x)   = suc n , λ _ → n
  bin→ℕ n (andᶠ x y) = bin→ℕ₂ n x y
  bin→ℕ n (orᶠ x y)  = bin→ℕ₂ n x y
  bin→ℕ n (notᶠ x)   = bin→ℕ₁ n x
  bin→ℕ n (xorᶠ x y) = bin→ℕ₂ n x y
  bin→ℕ n (iffᶠ x y) = bin→ℕ₂ n x y

module _ where
  ℕ→bin : ℕ → (f : Formula₀ A) → ℕ × (ℕ → List Bool)

  module ⟨ℕ→bin⟩ where
    ℕ→bin₁ : ℕ → (x : Formula₀ A) → ℕ × (ℕ → List Bool)
    ℕ→bin₁ n x =
      let n′ , m = ℕ→bin n x in
      suc n′ , λ a →
        case a ≟ⁿ n′ of λ where
          (yes _) → []
          (no  _) → false ∷ m a

    ℕ→bin₂ : ℕ → (x y : Formula₀ A) → ℕ × (ℕ → List Bool)
    ℕ→bin₂ n x y =
      let nˡ , mˡ = ℕ→bin n x in
      let nʳ , mʳ = ℕ→bin nˡ y in
      suc nʳ , λ a →
        case a <?ⁿ nˡ of λ where
          (yes _) → false ∷ mˡ a
          (no  _) →
            case a <?ⁿ nʳ of λ where
              (yes _) → true ∷ mʳ a
              (no  _) → []

  open ⟨ℕ→bin⟩

  ℕ→bin n (varᶠ x)   = suc n , λ _ → []
  ℕ→bin n (andᶠ x y) = ℕ→bin₂ n x y
  ℕ→bin n (orᶠ x y)  = ℕ→bin₂ n x y
  ℕ→bin n (notᶠ x)   = ℕ→bin₁ n x
  ℕ→bin n (xorᶠ x y) = ℕ→bin₂ n x y
  ℕ→bin n (iffᶠ x y) = ℕ→bin₂ n x y

module _ where
  n<fw₁ : ∀ n f → n < proj₁ (bin→ℕ {A} n f)

  module ⟨n<fw₁⟩ where
    aux₁ : ∀ n x → n < suc (proj₁ (bin→ℕ {A} n x))
    aux₁ n x = <-trans (n<fw₁ n x) ≤-refl

    aux₂ : ∀ n x y → n < suc (proj₁ (bin→ℕ {A} (proj₁ (bin→ℕ {A} n x)) y))
    aux₂ n x y = <-trans (n<fw₁ n x) (<-trans (n<fw₁ (proj₁ (bin→ℕ n x)) y) ≤-refl)

  open ⟨n<fw₁⟩

  n<fw₁ n (varᶠ x)   = ≤-refl
  n<fw₁ n (andᶠ x y) = aux₂ n x y
  n<fw₁ n (orᶠ x y)  = aux₂ n x y
  n<fw₁ n (notᶠ x)   = aux₁ n x
  n<fw₁ n (xorᶠ x y) = aux₂ n x y
  n<fw₁ n (iffᶠ x y) = aux₂ n x y

fw₁<fw₁fw₁ : ∀ n x y → proj₁ (bin→ℕ {A} n x) < proj₁ (bin→ℕ {A} (proj₁ (bin→ℕ n x)) y)
fw₁<fw₁fw₁ n x y = n<fw₁ (proj₁ (bin→ℕ n x)) y

n<fw₁fw₁ : ∀ n x y → n < proj₁ (bin→ℕ {A} (proj₁ (bin→ℕ {A} n x)) y)
n<fw₁fw₁ n x y = <-trans (n<fw₁ n x) (fw₁<fw₁fw₁ n x y)

n≤fw₂ : ∀ n f a → n ≤ proj₂ (bin→ℕ {A} n f) a
n≤fw₂ n (varᶠ x)   a            = ≤-refl
n≤fw₂ n (andᶠ x y) []           = <⇒≤ (n<fw₁fw₁ n x y)
n≤fw₂ n (andᶠ x y) (false ∷ as) = n≤fw₂ n x as
n≤fw₂ n (andᶠ x y) (true ∷ as)  = <⇒≤ (<-transˡ (n<fw₁ n x) (n≤fw₂ (proj₁ (bin→ℕ n x)) y as))
n≤fw₂ n (orᶠ x y) []            = <⇒≤ (n<fw₁fw₁ n x y)
n≤fw₂ n (orᶠ x y) (false ∷ as)  = n≤fw₂ n x as
n≤fw₂ n (orᶠ x y) (true ∷ as)   = <⇒≤ (<-transˡ (n<fw₁ n x) (n≤fw₂ (proj₁ (bin→ℕ n x)) y as))
n≤fw₂ n (notᶠ x) []             = <⇒≤ (n<fw₁ n x)
n≤fw₂ n (notᶠ x) (a ∷ as)       = n≤fw₂ n x as
n≤fw₂ n (xorᶠ x y) []           = <⇒≤ (n<fw₁fw₁ n x y)
n≤fw₂ n (xorᶠ x y) (false ∷ as) = n≤fw₂ n x as
n≤fw₂ n (xorᶠ x y) (true ∷ as)  = <⇒≤ (<-transˡ (n<fw₁ n x) (n≤fw₂ (proj₁ (bin→ℕ n x)) y as))
n≤fw₂ n (iffᶠ x y) []           = <⇒≤ (n<fw₁fw₁ n x y)
n≤fw₂ n (iffᶠ x y) (false ∷ as) = n≤fw₂ n x as
n≤fw₂ n (iffᶠ x y) (true ∷ as)  = <⇒≤ (<-transˡ (n<fw₁ n x) (n≤fw₂ (proj₁ (bin→ℕ n x)) y as))

fw₁≤fw₂fw₁ : ∀ n x y a → proj₁ (bin→ℕ {A} n x) ≤ proj₂ (bin→ℕ {A} (proj₁ (bin→ℕ n x)) y) a
fw₁≤fw₂fw₁ n x y a = n≤fw₂ (proj₁ (bin→ℕ n x)) y a

fw₂<fw₁ : ∀ n f a → proj₂ (bin→ℕ {A} n f) a < proj₁ (bin→ℕ n f)
fw₂<fw₁ n (varᶠ x)   a            = ≤-refl
fw₂<fw₁ n (andᶠ x y) []           = ≤-refl
fw₂<fw₁ n (andᶠ x y) (false ∷ as) = <-trans (fw₂<fw₁ n x as ) (<-trans (fw₁<fw₁fw₁ n x y) ≤-refl)
fw₂<fw₁ n (andᶠ x y) (true ∷ as)  = <-trans (fw₂<fw₁ (proj₁ (bin→ℕ n x)) y as) ≤-refl
fw₂<fw₁ n (orᶠ x y)  []           = ≤-refl
fw₂<fw₁ n (orᶠ x y)  (false ∷ as) = <-trans (fw₂<fw₁ n x as ) (<-trans (fw₁<fw₁fw₁ n x y) ≤-refl)
fw₂<fw₁ n (orᶠ x y)  (true ∷ as)  = <-trans (fw₂<fw₁ (proj₁ (bin→ℕ n x)) y as) ≤-refl
fw₂<fw₁ n (notᶠ x)   []           = ≤-refl
fw₂<fw₁ n (notᶠ x)   (a ∷ as)     = <-trans (fw₂<fw₁ n x as) ≤-refl
fw₂<fw₁ n (xorᶠ x y) []           = ≤-refl
fw₂<fw₁ n (xorᶠ x y) (false ∷ as) = <-trans (fw₂<fw₁ n x as ) (<-trans (fw₁<fw₁fw₁ n x y) ≤-refl)
fw₂<fw₁ n (xorᶠ x y) (true ∷ as)  = <-trans (fw₂<fw₁ (proj₁ (bin→ℕ n x)) y as) ≤-refl
fw₂<fw₁ n (iffᶠ x y) []           = ≤-refl
fw₂<fw₁ n (iffᶠ x y) (false ∷ as) = <-trans (fw₂<fw₁ n x as ) (<-trans (fw₁<fw₁fw₁ n x y) ≤-refl)
fw₂<fw₁ n (iffᶠ x y) (true ∷ as)  = <-trans (fw₂<fw₁ (proj₁ (bin→ℕ n x)) y as) ≤-refl

fw₂fw₁<fw₁fw₁ : ∀ n x y a →
  proj₂ (bin→ℕ {A} (proj₁ (bin→ℕ {A} n x)) y) a < proj₁ (bin→ℕ (proj₁ (bin→ℕ n x)) y)
fw₂fw₁<fw₁fw₁ n x y a = fw₂<fw₁ (proj₁ (bin→ℕ n x)) y a

fw₁≡bw₁ : ∀ n f → proj₁ (bin→ℕ {A} n f) ≡ proj₁ (ℕ→bin n f)
fw₁≡bw₁ n (varᶠ x) = refl
fw₁≡bw₁ n (andᶠ x y)
  rewrite fw₁≡bw₁ n x
  rewrite fw₁≡bw₁ (proj₁ (ℕ→bin n x)) y
  = refl
fw₁≡bw₁ n (orᶠ x y)
  rewrite fw₁≡bw₁ n x
  rewrite fw₁≡bw₁ (proj₁ (ℕ→bin n x)) y
  = refl
fw₁≡bw₁ n (notᶠ x) = cong suc (fw₁≡bw₁ n x)
fw₁≡bw₁ n (xorᶠ x y)
  rewrite fw₁≡bw₁ n x
  rewrite fw₁≡bw₁ (proj₁ (ℕ→bin n x)) y
  = refl
fw₁≡bw₁ n (iffᶠ x y)
  rewrite fw₁≡bw₁ n x
  rewrite fw₁≡bw₁ (proj₁ (ℕ→bin n x)) y
  = refl

fw₁fw₁≡bw₁bw₁ : ∀ n x y →
  proj₁ (bin→ℕ {A} (proj₁ (bin→ℕ {A} n x)) y) ≡ proj₁ (ℕ→bin (proj₁ (ℕ→bin n x)) y)
fw₁fw₁≡bw₁bw₁ n x y = begin
  proj₁ (bin→ℕ (proj₁ (bin→ℕ n x)) y) ≡⟨ cong (λ # → proj₁ (bin→ℕ # y)) (fw₁≡bw₁ n x) ⟩
  proj₁ (bin→ℕ (proj₁ (ℕ→bin n x)) y) ≡⟨ fw₁≡bw₁ (proj₁ (ℕ→bin n x)) y ⟩
  proj₁ (ℕ→bin (proj₁ (ℕ→bin n x)) y) ∎
  where open ≡-Reasoning

fw₂<bw₁ : ∀ n f a → proj₂ (bin→ℕ {A} n f) a < proj₁ (ℕ→bin n f)
fw₂<bw₁ n f a = begin-strict
  proj₂ (bin→ℕ n f) a <⟨ fw₂<fw₁ n f a ⟩
  proj₁ (bin→ℕ n f)   ≡⟨ fw₁≡bw₁ n f ⟩
  proj₁ (ℕ→bin n f)   ∎
  where open ≤-Reasoning

bw₁<fw₁fw₁ : ∀ n x y → proj₁ (ℕ→bin {A} n x) < proj₁ (bin→ℕ {A} (proj₁ (bin→ℕ n x)) y)
bw₁<fw₁fw₁ n x y  = begin-strict
  proj₁ (ℕ→bin n x)                   ≡⟨ sym (fw₁≡bw₁ n x) ⟩
  proj₁ (bin→ℕ n x)                   <⟨ fw₁<fw₁fw₁ n x y ⟩
  proj₁ (bin→ℕ (proj₁ (bin→ℕ n x)) y) ∎
  where open ≤-Reasoning

bw₁≤fw₂fw₁ : ∀ n x y a → proj₁ (ℕ→bin {A} n x) ≤ proj₂ (bin→ℕ {A} (proj₁ (bin→ℕ n x)) y) a
bw₁≤fw₂fw₁ n x y a = begin
  proj₁ (ℕ→bin n x)                     ≡⟨ sym (fw₁≡bw₁ n x) ⟩
  proj₁ (bin→ℕ n x)                     ≤⟨ fw₁≤fw₂fw₁ n x y a ⟩
  proj₂ (bin→ℕ (proj₁ (bin→ℕ n x)) y) a ∎
  where open ≤-Reasoning

fw₂fw₁<bw₁bw₁ : ∀ n x y a →
  proj₂ (bin→ℕ {A} (proj₁ (bin→ℕ {A} n x)) y) a < proj₁ (ℕ→bin (proj₁ (ℕ→bin n x)) y)
fw₂fw₁<bw₁bw₁ n x y a = begin-strict
  proj₂ (bin→ℕ (proj₁ (bin→ℕ n x)) y) a <⟨ fw₂fw₁<fw₁fw₁ n x y a ⟩
  proj₁ (bin→ℕ (proj₁ (bin→ℕ n x)) y)   ≡⟨ cong (λ # → proj₁ (bin→ℕ # y)) (fw₁≡bw₁ n x) ⟩
  proj₁ (bin→ℕ (proj₁ (ℕ→bin n x)) y)   ≡⟨ fw₁≡bw₁ (proj₁ (ℕ→bin n x)) y ⟩
  proj₁ (ℕ→bin (proj₁ (ℕ→bin n x)) y)   ∎
  where open ≤-Reasoning

roundtrip : ∀ n v f a →
  (makeTrue v f ∘ proj₂ (ℕ→bin {A} n f)) (proj₂ (bin→ℕ n f) a) ≡ makeTrue v f a
roundtrip n v (varᶠ x)   a = refl
roundtrip n v (andᶠ x y) []
  rewrite (proj₂ ∘ ≮⇒<? ∘ <⇒≯) (bw₁<fw₁fw₁ n x y)
  rewrite (proj₂ ∘ ≮⇒<?) (<-irrefl (fw₁fw₁≡bw₁bw₁ n x y))
  = refl
roundtrip n v (andᶠ x y) (false ∷ as)
  rewrite <⇒<? (fw₂<bw₁ n x as)
  = roundtrip n v x as
roundtrip n v (andᶠ x y) (true ∷ as)
  rewrite (proj₂ ∘ ≮⇒<? ∘ ≤⇒≯) (bw₁≤fw₂fw₁ n x y as)
  rewrite <⇒<? (fw₂fw₁<bw₁bw₁ n x y as)
  rewrite sym (fw₁≡bw₁ n x)
  = roundtrip (proj₁ (bin→ℕ n x)) v y as
roundtrip n v (orᶠ x y) []
  rewrite (proj₂ ∘ ≮⇒<? ∘ <⇒≯) (bw₁<fw₁fw₁ n x y)
  rewrite (proj₂ ∘ ≮⇒<?) (<-irrefl (fw₁fw₁≡bw₁bw₁ n x y))
  = refl
roundtrip n v (orᶠ x y) (false ∷ as)
  rewrite <⇒<? (fw₂<bw₁ n x as)
  = roundtrip n v x as
roundtrip n v (orᶠ x y) (true ∷ as)
  rewrite (proj₂ ∘ ≮⇒<? ∘ ≤⇒≯) (bw₁≤fw₂fw₁ n x y as)
  rewrite <⇒<? (fw₂fw₁<bw₁bw₁ n x y as)
  rewrite sym (fw₁≡bw₁ n x)
  = roundtrip (proj₁ (bin→ℕ n x)) v y as
roundtrip n v (notᶠ x)   []
  rewrite ≡⇒≟ⁿ (fw₁≡bw₁ n x)
  = refl
roundtrip n v (notᶠ x)   (a ∷ as)
  rewrite (proj₂ ∘ ≢⇒≟ⁿ ∘ <⇒≢) (fw₂<bw₁ n x as)
  = roundtrip n v x as
roundtrip n v (xorᶠ x y) []
  rewrite (proj₂ ∘ ≮⇒<? ∘ <⇒≯) (bw₁<fw₁fw₁ n x y)
  rewrite (proj₂ ∘ ≮⇒<?) (<-irrefl (fw₁fw₁≡bw₁bw₁ n x y))
  = refl
roundtrip n v (xorᶠ x y) (false ∷ as)
  rewrite <⇒<? (fw₂<bw₁ n x as)
  = roundtrip n v x as
roundtrip n v (xorᶠ x y) (true ∷ as)
  rewrite (proj₂ ∘ ≮⇒<? ∘ ≤⇒≯) (bw₁≤fw₂fw₁ n x y as)
  rewrite <⇒<? (fw₂fw₁<bw₁bw₁ n x y as)
  rewrite sym (fw₁≡bw₁ n x)
  = roundtrip (proj₁ (bin→ℕ n x)) v y as
roundtrip n v (iffᶠ x y) []
  rewrite (proj₂ ∘ ≮⇒<? ∘ <⇒≯) (bw₁<fw₁fw₁ n x y)
  rewrite (proj₂ ∘ ≮⇒<?) (<-irrefl (fw₁fw₁≡bw₁bw₁ n x y))
  = refl
roundtrip n v (iffᶠ x y) (false ∷ as)
  rewrite <⇒<? (fw₂<bw₁ n x as)
  = roundtrip n v x as
roundtrip n v (iffᶠ x y) (true ∷ as)
  rewrite (proj₂ ∘ ≮⇒<? ∘ ≤⇒≯) (bw₁≤fw₂fw₁ n x y as)
  rewrite <⇒<? (fw₂fw₁<bw₁bw₁ n x y as)
  rewrite sym (fw₁≡bw₁ n x)
  = roundtrip (proj₁ (bin→ℕ n x)) v y as

remap : (List Bool → ℕ) → Formula₁ → Formula₂
remap r (varᶠ x)   = varᶠ x
remap r (tmpᶠ x)   = tmpᶠ (r x)
remap r (andᶠ x y) = andᶠ (remap r x) (remap r y)
remap r (orᶠ x y)  = orᶠ (remap r x) (remap r y)
remap r (notᶠ x)   = notᶠ (remap r x)
remap r (xorᶠ x y) = xorᶠ (remap r x) (remap r y)
remap r (iffᶠ x y) = iffᶠ (remap r x) (remap r y)

evalRemap : ∀ n v t r f → eval v t (remap r (flatten n f)) ≡ eval v (t ∘ r) (flatten {A} n f)
evalRemap n v t r (varᶠ x)   = refl
evalRemap n v t r (andᶠ x y)
  rewrite sym (evalRemap (n ++ [ false ]) v t r x)
  rewrite sym (evalRemap (n ++ [ true ]) v t r y)
  = refl
evalRemap n v t r (orᶠ x y)
  rewrite sym (evalRemap (n ++ [ false ]) v t r x)
  rewrite sym (evalRemap (n ++ [ true ]) v t r y)
  = refl
evalRemap n v t r (notᶠ x)
  rewrite sym (evalRemap (n ++ [ false ]) v t r x)
  = refl
evalRemap n v t r (xorᶠ x y)
  rewrite sym (evalRemap (n ++ [ false ]) v t r x)
  rewrite sym (evalRemap (n ++ [ true ]) v t r y)
  = refl
evalRemap n v t r (iffᶠ x y)
  rewrite sym (evalRemap (n ++ [ false ]) v t r x)
  rewrite sym (evalRemap (n ++ [ true ]) v t r y)
  = refl

assign-≡ : ∀ {t₁ t₂} v → (f : Formula ⊤ A) → (∀ a → t₁ a ≡ t₂ a) → eval v t₁ f ≡ eval v t₂ f
assign-≡ {t₁} {t₂} v (varᶠ x)   p = refl
assign-≡ {t₁} {t₂} v (tmpᶠ x)   p = p x
assign-≡ {t₁} {t₂} v (andᶠ x y) p = cong₂ _∧_ (assign-≡ v x p) (assign-≡ v y p)
assign-≡ {t₁} {t₂} v (orᶠ x y)  p = cong₂ _∨_ (assign-≡ v x p) (assign-≡ v y p)
assign-≡ {t₁} {t₂} v (notᶠ x)   p = cong not (assign-≡ v x p)
assign-≡ {t₁} {t₂} v (xorᶠ x y) p = cong₂ _xor_ (assign-≡ v x p) (assign-≡ v y p)
assign-≡ {t₁} {t₂} v (iffᶠ x y) p = cong₂ _↔_ (assign-≡ v x p) (assign-≡ v y p)

makeTrue-ℕ : (ℕ → Bool) → Formula ⊥ A → (ℕ → Bool)
makeTrue-ℕ v f = makeTrue v f ∘ proj₂ (ℕ→bin 0 f)

transform₂ : Formula₀ A → Formula₂
transform₂ f = remap (proj₂ (bin→ℕ 0 f)) (transform₁ f)

transform₂-✓ : ∀ v t f → eval v (makeTrue-ℕ {A} v f) (transform₂ f) ≡ eval v t f
transform₂-✓ v t f
  rewrite roundtrip 0 v f []
  rewrite evalRemap [] v (makeTrue v f ∘ proj₂ (ℕ→bin 0 f)) (proj₂ (bin→ℕ 0 f)) f
  rewrite assign-≡ v (flatten [] f) (roundtrip 0 v f)
  rewrite sym (transform₁-✓ v t f)
  = refl
