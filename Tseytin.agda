-- XXX - duplication in rewrite-based proofs (e.g., makeTrue-✓₁ or roundtrip)

module Tseytin where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; _xor_ ; _≟_)
open import Data.Bool.Properties using (∧-identityʳ ; ∧-idem)
open import Data.Empty using (⊥)
open import Data.List using (List ; _∷_ ; [] ; [_] ; _++_ ; length)
open import Data.List.Relation.Binary.Equality.DecPropositional (_≟_) using (_≡?_)
open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s ; _<_ ; _+_ ; _∸_ ; _⊔_)
  renaming (_≟_ to _≟ⁿ_ ; _<?_ to _<?ⁿ_)
open import Data.Nat.Properties using (
    ≤-refl ; <-irrefl ; <-trans ; <-transˡ ; n<1+n ; m≤m+n ; m⊔n≤o⇒m≤o ; m⊔n≤o⇒n≤o ;
    <⇒≢ ; <⇒≯ ; <⇒≤ ; ≤⇒≯ ; <-irrelevant ; module ≤-Reasoning ;
    m+n∸m≡n
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

-- original
data Formula₀ : Set where
  var₀ : ℕ → Formula₀
  and₀ : Formula₀ → Formula₀ → Formula₀
  or₀  : Formula₀ → Formula₀ → Formula₀
  not₀ : Formula₀ → Formula₀
  xor₀ : Formula₀ → Formula₀ → Formula₀
  iff₀ : Formula₀ → Formula₀ → Formula₀

eval₀ : (ℕ → Bool) → Formula₀ → Bool
eval₀ v (var₀ x)   = v x
eval₀ v (and₀ x y) = eval₀ v x ∧ eval₀ v y
eval₀ v (or₀ x y)  = eval₀ v x ∨ eval₀ v y
eval₀ v (not₀ x)   = not (eval₀ v x)
eval₀ v (xor₀ x y) = eval₀ v x xor eval₀ v y
eval₀ v (iff₀ x y) = eval₀ v x ↔ eval₀ v y

-- temporaries with binary identifiers, CNF patterns
data Formula₁ : Set where
  var₁ : ℕ → Formula₁
  tmp₁ : List Bool → Formula₁
  and₁ : Formula₁ → Formula₁ → Formula₁
  or₁  : Formula₁ → Formula₁ → Formula₁
  not₁ : Formula₁ → Formula₁

eval₁ : (ℕ → Bool) → (List Bool → Bool) → Formula₁ → Bool
eval₁ v t (var₁ x)   = v x
eval₁ v t (tmp₁ x)   = t x
eval₁ v t (and₁ x y) = eval₁ v t x ∧ eval₁ v t y
eval₁ v t (or₁ x y)  = eval₁ v t x ∨ eval₁ v t y
eval₁ v t (not₁ x)   = not (eval₁ v t x)

-- temporaries with ℕ identifiers
data Formula₂ : Set where
  var₂ : ℕ → Formula₂
  tmp₂ : ℕ → Formula₂
  and₂ : Formula₂ → Formula₂ → Formula₂
  or₂  : Formula₂ → Formula₂ → Formula₂
  not₂ : Formula₂ → Formula₂

eval₂ : (ℕ → Bool) → (ℕ → Bool) → Formula₂ → Bool
eval₂ v t (var₂ x)   = v x
eval₂ v t (tmp₂ x)   = t x
eval₂ v t (and₂ x y) = eval₂ v t x ∧ eval₂ v t y
eval₂ v t (or₂ x y)  = eval₂ v t x ∨ eval₂ v t y
eval₂ v t (not₂ x)   = not (eval₂ v t x)

-- temporaries turned into variables
data Formula₃ : Set where
  var₃ : ℕ → Formula₃
  and₃ : Formula₃ → Formula₃ → Formula₃
  or₃  : Formula₃ → Formula₃ → Formula₃
  not₃ : Formula₃ → Formula₃

eval₃ : (ℕ → Bool) → Formula₃ → Bool
eval₃ v (var₃ x)   = v x
eval₃ v (and₃ x y) = eval₃ v x ∧ eval₃ v y
eval₃ v (or₃ x y)  = eval₃ v x ∨ eval₃ v y
eval₃ v (not₃ x)   = not (eval₃ v x)

x↔x : ∀ x → (x ↔ x) ≡ true
x↔x false = refl
x↔x true  = refl

x↔t≡x : ∀ x → (x ↔ true) ≡ x
x↔t≡x false = refl
x↔t≡x true  = refl

x↔f≡¬x : ∀ x → (x ↔ false) ≡ not x
x↔f≡¬x false = refl
x↔f≡¬x true  = refl

var-pat : (x r : Formula₁) → Formula₁
var-pat x r = and₁ (or₁ x (not₁ r)) (or₁ (not₁ x) r)

var-pat-✓ : ∀ x r → (r ↔ x) ≡ (x ∨ not r) ∧ (not x ∨ r)
var-pat-✓ false r = trans (x↔f≡¬x r) (sym (∧-identityʳ (not r)))
var-pat-✓ true  r = x↔t≡x r

∧-pat : (x y r : Formula₁) → Formula₁
∧-pat x y r = and₁ (or₁ (not₁ x) (or₁ (not₁ y) r)) (and₁ (or₁ x (not₁ r)) (or₁ y (not₁ r)))

∧-pat-✓ : ∀ x y r → (r ↔ x ∧ y) ≡ (not x ∨ not y ∨ r) ∧ (x ∨ not r) ∧ (y ∨ not r)
∧-pat-✓ false false r = trans (x↔f≡¬x r) (sym (∧-idem (not r)))
∧-pat-✓ false true  r = trans (x↔f≡¬x r) (sym (∧-identityʳ (not r)))
∧-pat-✓ true false  r = x↔f≡¬x r
∧-pat-✓ true true   r = trans (x↔t≡x r) (sym (∧-identityʳ r))

∨-pat : (x y r : Formula₁) → Formula₁
∨-pat x y r = and₁ (or₁ x (or₁ y (not₁ r))) (and₁ (or₁ (not₁ x) r) (or₁ (not₁ y) r))

∨-pat-✓ : ∀ x y r → (r ↔ x ∨ y) ≡ (x ∨ y ∨ not r) ∧ (not x ∨ r) ∧ (not y ∨ r)
∨-pat-✓ false false r = trans (x↔f≡¬x r) (sym (∧-identityʳ (not r)))
∨-pat-✓ false true  r = x↔t≡x r
∨-pat-✓ true  false r = trans (x↔t≡x r) (sym (∧-identityʳ r))
∨-pat-✓ true  true  r = trans (x↔t≡x r) (sym (∧-idem r))

not-pat : (x r : Formula₁) → Formula₁
not-pat x r = and₁ (or₁ (not₁ x) (not₁ r)) (or₁ x r)

not-pat-✓ : ∀ x r → (r ↔ not x) ≡ (not x ∨ not r) ∧ (x ∨ r)
not-pat-✓ false r = x↔t≡x r
not-pat-✓ true  r = trans (x↔f≡¬x r) (sym (∧-identityʳ (not r)))

xor-pat : (x y r : Formula₁) → Formula₁
xor-pat x y r =
  and₁ (or₁ (not₁ x) (or₁ (not₁ y) (not₁ r)))
  (and₁ (or₁ x (or₁ y (not₁ r)))
  (and₁ (or₁ x (or₁ (not₁ y) r))
  (or₁ (not₁ x) (or₁ y r))))

xor-pat-✓ : ∀ x y r →
  (r ↔ x xor y) ≡ (not x ∨ not y ∨ not r) ∧ (x ∨ y ∨ not r) ∧ (x ∨ not y ∨ r) ∧ (not x ∨ y ∨ r)
xor-pat-✓ false false r = trans (x↔f≡¬x r) (sym (∧-identityʳ (not r)))
xor-pat-✓ false true  r = trans (x↔t≡x r) (sym (∧-identityʳ r))
xor-pat-✓ true  false r = x↔t≡x r
xor-pat-✓ true  true  r = trans (x↔f≡¬x r) (sym (∧-identityʳ (not r)))

↔-pat : (x y r : Formula₁) → Formula₁
↔-pat x y r =
  and₁ (or₁ x (or₁ y r))
  (and₁ (or₁ (not₁ x) (or₁ (not₁ y) r))
  (and₁ (or₁ (not₁ x) (or₁ y (not₁ r)))
  (or₁ x (or₁ (not₁ y) (not₁ r)))))

↔-pat-✓ : ∀ x y r →
  (r ↔ (x ↔ y)) ≡ (x ∨ y ∨ r) ∧ (not x ∨ not y ∨ r) ∧ (not x ∨ y ∨ not r) ∧ (x ∨ not y ∨ not r)
↔-pat-✓ false false r = trans (x↔t≡x r) (sym (∧-identityʳ r))
↔-pat-✓ false true  r = x↔f≡¬x r
↔-pat-✓ true  false r = trans (x↔f≡¬x r) (sym (∧-identityʳ (not r)))
↔-pat-✓ true  true  r = trans (x↔t≡x r) (sym (∧-identityʳ r))

flatten : List Bool → Formula₀ → Formula₁

flatten₀ : List Bool → ℕ → Formula₁
flatten₀ n x = var-pat (tmp₁ n) (var₁ x)

flatten₁ : List Bool → (Formula₁ → Formula₁ → Formula₁) → Formula₀ → Formula₁
flatten₁ n p x =
  let s = flatten (n ++ [ false ]) x in
  and₁ (p (tmp₁ (n ++ [ false ])) (tmp₁ n)) s

flatten₂ : List Bool → (Formula₁ → Formula₁ → Formula₁ → Formula₁) → Formula₀ → Formula₀ → Formula₁
flatten₂ n p x y =
  let sˡ = flatten (n ++ [ false ]) x in
  let sʳ = flatten (n ++ [ true ]) y in
  (and₁ (and₁ (p (tmp₁ (n ++ [ false ])) (tmp₁ (n ++ [ true ])) (tmp₁ n)) sˡ) sʳ)

flatten n (var₀ x)   = flatten₀ n x
flatten n (and₀ x y) = flatten₂ n ∧-pat x y
flatten n (or₀ x y)  = flatten₂ n ∨-pat x y
flatten n (not₀ x)   = flatten₁ n not-pat x
flatten n (xor₀ x y) = flatten₂ n xor-pat x y
flatten n (iff₀ x y) = flatten₂ n ↔-pat x y

module _ where
  makeTrue₁ : (ℕ → Bool) → Formula₀ → (List Bool → Bool)

  module ⟨makeTrue₁⟩ where
    aux₁ : (ℕ → Bool) → (Bool → Bool) → Formula₀ → (List Bool → Bool)
    aux₁ v op x =
      let t′ = makeTrue₁ v x in
        λ where
          []      → op (t′ [])
          (_ ∷ n) → t′ n

    aux₂ : (ℕ → Bool) → (Bool → Bool → Bool) → Formula₀ → Formula₀ → (List Bool → Bool)
    aux₂ v op x y =
      let tˡ = makeTrue₁ v x in
      let tʳ = makeTrue₁ v y in
        λ where
          []          → op (tˡ []) (tʳ [])
          (false ∷ n) → tˡ n
          (true ∷ n)  → tʳ n

  open ⟨makeTrue₁⟩

  makeTrue₁ v (var₀ x)   = λ _ → v x
  makeTrue₁ v (and₀ x y) = aux₂ v _∧_ x y
  makeTrue₁ v (or₀ x y)  = aux₂ v _∨_ x y
  makeTrue₁ v (not₀ x)   = aux₁ v not x
  makeTrue₁ v (xor₀ x y) = aux₂ v _xor_ x y
  makeTrue₁ v (iff₀ x y) = aux₂ v _↔_ x y

evalCons : ∀ m n v t f → eval₁ v t (flatten (m ∷ n) f) ≡ eval₁ v (t ∘ (m ∷_)) (flatten n f)
evalCons m n v t (var₀ x) = refl
evalCons m n v t (and₀ x y)
  rewrite sym (evalCons m (n ++ [ false ]) v t x)
  rewrite sym (evalCons m (n ++ [ true ]) v t y)
  = refl
evalCons m n v t (or₀ x y)
  rewrite sym (evalCons m (n ++ [ false ]) v t x)
  rewrite sym (evalCons m (n ++ [ true ]) v t y)
  = refl
evalCons m n v t (not₀ x)
  rewrite sym (evalCons m (n ++ [ false ]) v t x)
  = refl
evalCons m n v t (xor₀ x y)
  rewrite sym (evalCons m (n ++ [ false ]) v t x)
  rewrite sym (evalCons m (n ++ [ true ]) v t y)
  = refl
evalCons m n v t (iff₀ x y)
  rewrite sym (evalCons m (n ++ [ false ]) v t x)
  rewrite sym (evalCons m (n ++ [ true ]) v t y)
  = refl

makeTrue₁-✓₁ : ∀ v f → eval₁ v (makeTrue₁ v f) (flatten [] f) ≡ true
makeTrue₁-✓₁ v (var₀ x)
  rewrite sym (var-pat-✓ (v x) (v x))
  = x↔x (v x)
makeTrue₁-✓₁ v (and₀ x y)
  rewrite sym (∧-pat-✓ (makeTrue₁ v (and₀ x y) [ false ]) (makeTrue₁ v (and₀ x y) [ true ])
    (makeTrue₁ v (and₀ x y) []))
  rewrite evalCons false [] v (makeTrue₁ v (and₀ x y)) x
  rewrite evalCons true [] v (makeTrue₁ v (and₀ x y)) y
  rewrite makeTrue₁-✓₁ v x
  rewrite makeTrue₁-✓₁ v y
  rewrite x↔x (makeTrue₁ v x [] ∧ makeTrue₁ v y [])
  = refl
makeTrue₁-✓₁ v (or₀ x y)
  rewrite sym (∨-pat-✓ (makeTrue₁ v (or₀ x y) [ false ]) (makeTrue₁ v (or₀ x y) [ true ])
    (makeTrue₁ v (or₀ x y) []))
  rewrite evalCons false [] v (makeTrue₁ v (or₀ x y)) x
  rewrite evalCons true [] v (makeTrue₁ v (or₀ x y)) y
  rewrite makeTrue₁-✓₁ v x
  rewrite makeTrue₁-✓₁ v y
  rewrite x↔x (makeTrue₁ v x [] ∨ makeTrue₁ v y [])
  = refl
makeTrue₁-✓₁ v (not₀ x)
  rewrite sym (not-pat-✓ (makeTrue₁ v (not₀ x) [ false ]) (makeTrue₁ v (not₀ x) []))
  rewrite evalCons false [] v (makeTrue₁ v (not₀ x)) x
  rewrite makeTrue₁-✓₁ v x
  rewrite x↔x (not (makeTrue₁ v x []))
  = refl
makeTrue₁-✓₁ v (xor₀ x y)
  rewrite sym (xor-pat-✓ (makeTrue₁ v (xor₀ x y) [ false ]) (makeTrue₁ v (xor₀ x y) [ true ])
    (makeTrue₁ v (xor₀ x y) []))
  rewrite evalCons false [] v (makeTrue₁ v (xor₀ x y)) x
  rewrite evalCons true [] v (makeTrue₁ v (xor₀ x y)) y
  rewrite makeTrue₁-✓₁ v x
  rewrite makeTrue₁-✓₁ v y
  rewrite x↔x (makeTrue₁ v x [] xor makeTrue₁ v y [])
  = refl
makeTrue₁-✓₁ v (iff₀ x y)
  rewrite sym (↔-pat-✓ (makeTrue₁ v (iff₀ x y) [ false ]) (makeTrue₁ v (iff₀ x y) [ true ])
    (makeTrue₁ v (iff₀ x y) []))
  rewrite evalCons false [] v (makeTrue₁ v (iff₀ x y)) x
  rewrite evalCons true [] v (makeTrue₁ v (iff₀ x y)) y
  rewrite makeTrue₁-✓₁ v x
  rewrite makeTrue₁-✓₁ v y
  rewrite x↔x (makeTrue₁ v x [] ↔ makeTrue₁ v y [])
  = refl

makeTrue₁-✓₂ : ∀ v f → makeTrue₁ v f [] ≡ eval₀ v f
makeTrue₁-✓₂ v (var₀ x)   = refl
makeTrue₁-✓₂ v (and₀ x y) rewrite makeTrue₁-✓₂ v x | makeTrue₁-✓₂ v y = refl
makeTrue₁-✓₂ v (or₀ x y)  rewrite makeTrue₁-✓₂ v x | makeTrue₁-✓₂ v y = refl
makeTrue₁-✓₂ v (not₀ x)   rewrite makeTrue₁-✓₂ v x = refl
makeTrue₁-✓₂ v (xor₀ x y) rewrite makeTrue₁-✓₂ v x | makeTrue₁-✓₂ v y = refl
makeTrue₁-✓₂ v (iff₀ x y) rewrite makeTrue₁-✓₂ v x | makeTrue₁-✓₂ v y = refl

transform₁ : Formula₀ → Formula₁
transform₁ f = and₁ (tmp₁ []) (flatten [] f)

transform₁-✓ : ∀ v f → eval₁ v (makeTrue₁ v f) (transform₁ f) ≡ eval₀ v f
transform₁-✓ v f
  rewrite makeTrue₁-✓₁ v f
  rewrite makeTrue₁-✓₂ v f
  = ∧-identityʳ (eval₀ v f)

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
  bin→ℕ : ℕ → (f : Formula₀) → ℕ × (List Bool → ℕ)

  module ⟨bin→ℕ⟩ where
    aux₁ : ℕ → (x : Formula₀) → ℕ × (List Bool → ℕ)
    aux₁ n x =
      let n′ , m = bin→ℕ n x in
      suc n′ , λ where
        []      → n′
        (_ ∷ a) → m a

    aux₂ : ℕ → (x y : Formula₀) → ℕ × (List Bool → ℕ)
    aux₂ n x y =
      let nˡ , mˡ = bin→ℕ n x in
      let nʳ , mʳ = bin→ℕ nˡ y in
      suc nʳ , λ where
        []          → nʳ
        (false ∷ a) → mˡ a
        (true ∷ a)  → mʳ a

  open ⟨bin→ℕ⟩

  bin→ℕ n (var₀ x)   = suc n , λ _ → n
  bin→ℕ n (and₀ x y) = aux₂ n x y
  bin→ℕ n (or₀ x y)  = aux₂ n x y
  bin→ℕ n (not₀ x)   = aux₁ n x
  bin→ℕ n (xor₀ x y) = aux₂ n x y
  bin→ℕ n (iff₀ x y) = aux₂ n x y

module _ where
  ℕ→bin : ℕ → (f : Formula₀) → ℕ × (ℕ → List Bool)

  module ⟨ℕ→bin⟩ where
    aux₁ : ℕ → (x : Formula₀) → ℕ × (ℕ → List Bool)
    aux₁ n x =
      let n′ , m = ℕ→bin n x in
      suc n′ , λ a →
        case a ≟ⁿ n′ of λ where
          (yes _) → []
          (no  _) → false ∷ m a

    aux₂ : ℕ → (x y : Formula₀) → ℕ × (ℕ → List Bool)
    aux₂ n x y =
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

  ℕ→bin n (var₀ x)   = suc n , λ _ → []
  ℕ→bin n (and₀ x y) = aux₂ n x y
  ℕ→bin n (or₀ x y)  = aux₂ n x y
  ℕ→bin n (not₀ x)   = aux₁ n x
  ℕ→bin n (xor₀ x y) = aux₂ n x y
  ℕ→bin n (iff₀ x y) = aux₂ n x y

module _ where
  n<fw₁ : ∀ n f → n < proj₁ (bin→ℕ n f)

  module ⟨n<fw₁⟩ where
    aux₁ : ∀ n x → n < suc (proj₁ (bin→ℕ n x))
    aux₁ n x = <-trans (n<fw₁ n x) ≤-refl

    aux₂ : ∀ n x y → n < suc (proj₁ (bin→ℕ (proj₁ (bin→ℕ n x)) y))
    aux₂ n x y = <-trans (n<fw₁ n x) (<-trans (n<fw₁ (proj₁ (bin→ℕ n x)) y) ≤-refl)

  open ⟨n<fw₁⟩

  n<fw₁ n (var₀ x)   = ≤-refl
  n<fw₁ n (and₀ x y) = aux₂ n x y
  n<fw₁ n (or₀ x y)  = aux₂ n x y
  n<fw₁ n (not₀ x)   = aux₁ n x
  n<fw₁ n (xor₀ x y) = aux₂ n x y
  n<fw₁ n (iff₀ x y) = aux₂ n x y

fw₁<fw₁fw₁ : ∀ n x y → proj₁ (bin→ℕ n x) < proj₁ (bin→ℕ (proj₁ (bin→ℕ n x)) y)
fw₁<fw₁fw₁ n x y = n<fw₁ (proj₁ (bin→ℕ n x)) y

n<fw₁fw₁ : ∀ n x y → n < proj₁ (bin→ℕ (proj₁ (bin→ℕ n x)) y)
n<fw₁fw₁ n x y = <-trans (n<fw₁ n x) (fw₁<fw₁fw₁ n x y)

n≤fw₂ : ∀ n f a → n ≤ proj₂ (bin→ℕ n f) a
n≤fw₂ n (var₀ x)   a            = ≤-refl
n≤fw₂ n (and₀ x y) []           = <⇒≤ (n<fw₁fw₁ n x y)
n≤fw₂ n (and₀ x y) (false ∷ as) = n≤fw₂ n x as
n≤fw₂ n (and₀ x y) (true ∷ as)  = <⇒≤ (<-transˡ (n<fw₁ n x) (n≤fw₂ (proj₁ (bin→ℕ n x)) y as))
n≤fw₂ n (or₀ x y) []            = <⇒≤ (n<fw₁fw₁ n x y)
n≤fw₂ n (or₀ x y) (false ∷ as)  = n≤fw₂ n x as
n≤fw₂ n (or₀ x y) (true ∷ as)   = <⇒≤ (<-transˡ (n<fw₁ n x) (n≤fw₂ (proj₁ (bin→ℕ n x)) y as))
n≤fw₂ n (not₀ x) []             = <⇒≤ (n<fw₁ n x)
n≤fw₂ n (not₀ x) (a ∷ as)       = n≤fw₂ n x as
n≤fw₂ n (xor₀ x y) []           = <⇒≤ (n<fw₁fw₁ n x y)
n≤fw₂ n (xor₀ x y) (false ∷ as) = n≤fw₂ n x as
n≤fw₂ n (xor₀ x y) (true ∷ as)  = <⇒≤ (<-transˡ (n<fw₁ n x) (n≤fw₂ (proj₁ (bin→ℕ n x)) y as))
n≤fw₂ n (iff₀ x y) []           = <⇒≤ (n<fw₁fw₁ n x y)
n≤fw₂ n (iff₀ x y) (false ∷ as) = n≤fw₂ n x as
n≤fw₂ n (iff₀ x y) (true ∷ as)  = <⇒≤ (<-transˡ (n<fw₁ n x) (n≤fw₂ (proj₁ (bin→ℕ n x)) y as))

fw₁≤fw₂fw₁ : ∀ n x y a → proj₁ (bin→ℕ n x) ≤ proj₂ (bin→ℕ (proj₁ (bin→ℕ n x)) y) a
fw₁≤fw₂fw₁ n x y a = n≤fw₂ (proj₁ (bin→ℕ n x)) y a

fw₂<fw₁ : ∀ n f a → proj₂ (bin→ℕ n f) a < proj₁ (bin→ℕ n f)
fw₂<fw₁ n (var₀ x)   a            = ≤-refl
fw₂<fw₁ n (and₀ x y) []           = ≤-refl
fw₂<fw₁ n (and₀ x y) (false ∷ as) = <-trans (fw₂<fw₁ n x as ) (<-trans (fw₁<fw₁fw₁ n x y) ≤-refl)
fw₂<fw₁ n (and₀ x y) (true ∷ as)  = <-trans (fw₂<fw₁ (proj₁ (bin→ℕ n x)) y as) ≤-refl
fw₂<fw₁ n (or₀ x y)  []           = ≤-refl
fw₂<fw₁ n (or₀ x y)  (false ∷ as) = <-trans (fw₂<fw₁ n x as ) (<-trans (fw₁<fw₁fw₁ n x y) ≤-refl)
fw₂<fw₁ n (or₀ x y)  (true ∷ as)  = <-trans (fw₂<fw₁ (proj₁ (bin→ℕ n x)) y as) ≤-refl
fw₂<fw₁ n (not₀ x)   []           = ≤-refl
fw₂<fw₁ n (not₀ x)   (a ∷ as)     = <-trans (fw₂<fw₁ n x as) ≤-refl
fw₂<fw₁ n (xor₀ x y) []           = ≤-refl
fw₂<fw₁ n (xor₀ x y) (false ∷ as) = <-trans (fw₂<fw₁ n x as ) (<-trans (fw₁<fw₁fw₁ n x y) ≤-refl)
fw₂<fw₁ n (xor₀ x y) (true ∷ as)  = <-trans (fw₂<fw₁ (proj₁ (bin→ℕ n x)) y as) ≤-refl
fw₂<fw₁ n (iff₀ x y) []           = ≤-refl
fw₂<fw₁ n (iff₀ x y) (false ∷ as) = <-trans (fw₂<fw₁ n x as ) (<-trans (fw₁<fw₁fw₁ n x y) ≤-refl)
fw₂<fw₁ n (iff₀ x y) (true ∷ as)  = <-trans (fw₂<fw₁ (proj₁ (bin→ℕ n x)) y as) ≤-refl

fw₂fw₁<fw₁fw₁ : ∀ n x y a →
  proj₂ (bin→ℕ (proj₁ (bin→ℕ n x)) y) a < proj₁ (bin→ℕ (proj₁ (bin→ℕ n x)) y)
fw₂fw₁<fw₁fw₁ n x y a = fw₂<fw₁ (proj₁ (bin→ℕ n x)) y a

fw₁≡bw₁ : ∀ n f → proj₁ (bin→ℕ n f) ≡ proj₁ (ℕ→bin n f)
fw₁≡bw₁ n (var₀ x) = refl
fw₁≡bw₁ n (and₀ x y)
  rewrite fw₁≡bw₁ n x
  rewrite fw₁≡bw₁ (proj₁ (ℕ→bin n x)) y
  = refl
fw₁≡bw₁ n (or₀ x y)
  rewrite fw₁≡bw₁ n x
  rewrite fw₁≡bw₁ (proj₁ (ℕ→bin n x)) y
  = refl
fw₁≡bw₁ n (not₀ x) = cong suc (fw₁≡bw₁ n x)
fw₁≡bw₁ n (xor₀ x y)
  rewrite fw₁≡bw₁ n x
  rewrite fw₁≡bw₁ (proj₁ (ℕ→bin n x)) y
  = refl
fw₁≡bw₁ n (iff₀ x y)
  rewrite fw₁≡bw₁ n x
  rewrite fw₁≡bw₁ (proj₁ (ℕ→bin n x)) y
  = refl

fw₁fw₁≡bw₁bw₁ : ∀ n x y →
  proj₁ (bin→ℕ (proj₁ (bin→ℕ n x)) y) ≡ proj₁ (ℕ→bin (proj₁ (ℕ→bin n x)) y)
fw₁fw₁≡bw₁bw₁ n x y = begin
  proj₁ (bin→ℕ (proj₁ (bin→ℕ n x)) y) ≡⟨ cong (λ # → proj₁ (bin→ℕ # y)) (fw₁≡bw₁ n x) ⟩
  proj₁ (bin→ℕ (proj₁ (ℕ→bin n x)) y) ≡⟨ fw₁≡bw₁ (proj₁ (ℕ→bin n x)) y ⟩
  proj₁ (ℕ→bin (proj₁ (ℕ→bin n x)) y) ∎
  where open ≡-Reasoning

fw₂<bw₁ : ∀ n f a → proj₂ (bin→ℕ n f) a < proj₁ (ℕ→bin n f)
fw₂<bw₁ n f a = begin-strict
  proj₂ (bin→ℕ n f) a <⟨ fw₂<fw₁ n f a ⟩
  proj₁ (bin→ℕ n f)   ≡⟨ fw₁≡bw₁ n f ⟩
  proj₁ (ℕ→bin n f)   ∎
  where open ≤-Reasoning

bw₁<fw₁fw₁ : ∀ n x y → proj₁ (ℕ→bin n x) < proj₁ (bin→ℕ (proj₁ (bin→ℕ n x)) y)
bw₁<fw₁fw₁ n x y  = begin-strict
  proj₁ (ℕ→bin n x)                   ≡⟨ sym (fw₁≡bw₁ n x) ⟩
  proj₁ (bin→ℕ n x)                   <⟨ fw₁<fw₁fw₁ n x y ⟩
  proj₁ (bin→ℕ (proj₁ (bin→ℕ n x)) y) ∎
  where open ≤-Reasoning

bw₁≤fw₂fw₁ : ∀ n x y a → proj₁ (ℕ→bin n x) ≤ proj₂ (bin→ℕ (proj₁ (bin→ℕ n x)) y) a
bw₁≤fw₂fw₁ n x y a = begin
  proj₁ (ℕ→bin n x)                     ≡⟨ sym (fw₁≡bw₁ n x) ⟩
  proj₁ (bin→ℕ n x)                     ≤⟨ fw₁≤fw₂fw₁ n x y a ⟩
  proj₂ (bin→ℕ (proj₁ (bin→ℕ n x)) y) a ∎
  where open ≤-Reasoning

fw₂fw₁<bw₁bw₁ : ∀ n x y a →
  proj₂ (bin→ℕ (proj₁ (bin→ℕ n x)) y) a < proj₁ (ℕ→bin (proj₁ (ℕ→bin n x)) y)
fw₂fw₁<bw₁bw₁ n x y a = begin-strict
  proj₂ (bin→ℕ (proj₁ (bin→ℕ n x)) y) a <⟨ fw₂fw₁<fw₁fw₁ n x y a ⟩
  proj₁ (bin→ℕ (proj₁ (bin→ℕ n x)) y)   ≡⟨ cong (λ # → proj₁ (bin→ℕ # y)) (fw₁≡bw₁ n x) ⟩
  proj₁ (bin→ℕ (proj₁ (ℕ→bin n x)) y)   ≡⟨ fw₁≡bw₁ (proj₁ (ℕ→bin n x)) y ⟩
  proj₁ (ℕ→bin (proj₁ (ℕ→bin n x)) y)   ∎
  where open ≤-Reasoning

roundtrip : ∀ n v f a →
  (makeTrue₁ v f ∘ proj₂ (ℕ→bin n f)) (proj₂ (bin→ℕ n f) a) ≡ makeTrue₁ v f a
roundtrip n v (var₀ x)   a = refl
roundtrip n v (and₀ x y) []
  rewrite (proj₂ ∘ ≮⇒<? ∘ <⇒≯) (bw₁<fw₁fw₁ n x y)
  rewrite (proj₂ ∘ ≮⇒<?) (<-irrefl (fw₁fw₁≡bw₁bw₁ n x y))
  = refl
roundtrip n v (and₀ x y) (false ∷ as)
  rewrite <⇒<? (fw₂<bw₁ n x as)
  = roundtrip n v x as
roundtrip n v (and₀ x y) (true ∷ as)
  rewrite (proj₂ ∘ ≮⇒<? ∘ ≤⇒≯) (bw₁≤fw₂fw₁ n x y as)
  rewrite <⇒<? (fw₂fw₁<bw₁bw₁ n x y as)
  rewrite sym (fw₁≡bw₁ n x)
  = roundtrip (proj₁ (bin→ℕ n x)) v y as
roundtrip n v (or₀ x y) []
  rewrite (proj₂ ∘ ≮⇒<? ∘ <⇒≯) (bw₁<fw₁fw₁ n x y)
  rewrite (proj₂ ∘ ≮⇒<?) (<-irrefl (fw₁fw₁≡bw₁bw₁ n x y))
  = refl
roundtrip n v (or₀ x y) (false ∷ as)
  rewrite <⇒<? (fw₂<bw₁ n x as)
  = roundtrip n v x as
roundtrip n v (or₀ x y) (true ∷ as)
  rewrite (proj₂ ∘ ≮⇒<? ∘ ≤⇒≯) (bw₁≤fw₂fw₁ n x y as)
  rewrite <⇒<? (fw₂fw₁<bw₁bw₁ n x y as)
  rewrite sym (fw₁≡bw₁ n x)
  = roundtrip (proj₁ (bin→ℕ n x)) v y as
roundtrip n v (not₀ x)   []
  rewrite ≡⇒≟ⁿ (fw₁≡bw₁ n x)
  = refl
roundtrip n v (not₀ x)   (a ∷ as)
  rewrite (proj₂ ∘ ≢⇒≟ⁿ ∘ <⇒≢) (fw₂<bw₁ n x as)
  = roundtrip n v x as
roundtrip n v (xor₀ x y) []
  rewrite (proj₂ ∘ ≮⇒<? ∘ <⇒≯) (bw₁<fw₁fw₁ n x y)
  rewrite (proj₂ ∘ ≮⇒<?) (<-irrefl (fw₁fw₁≡bw₁bw₁ n x y))
  = refl
roundtrip n v (xor₀ x y) (false ∷ as)
  rewrite <⇒<? (fw₂<bw₁ n x as)
  = roundtrip n v x as
roundtrip n v (xor₀ x y) (true ∷ as)
  rewrite (proj₂ ∘ ≮⇒<? ∘ ≤⇒≯) (bw₁≤fw₂fw₁ n x y as)
  rewrite <⇒<? (fw₂fw₁<bw₁bw₁ n x y as)
  rewrite sym (fw₁≡bw₁ n x)
  = roundtrip (proj₁ (bin→ℕ n x)) v y as
roundtrip n v (iff₀ x y) []
  rewrite (proj₂ ∘ ≮⇒<? ∘ <⇒≯) (bw₁<fw₁fw₁ n x y)
  rewrite (proj₂ ∘ ≮⇒<?) (<-irrefl (fw₁fw₁≡bw₁bw₁ n x y))
  = refl
roundtrip n v (iff₀ x y) (false ∷ as)
  rewrite <⇒<? (fw₂<bw₁ n x as)
  = roundtrip n v x as
roundtrip n v (iff₀ x y) (true ∷ as)
  rewrite (proj₂ ∘ ≮⇒<? ∘ ≤⇒≯) (bw₁≤fw₂fw₁ n x y as)
  rewrite <⇒<? (fw₂fw₁<bw₁bw₁ n x y as)
  rewrite sym (fw₁≡bw₁ n x)
  = roundtrip (proj₁ (bin→ℕ n x)) v y as

remap₁ : (List Bool → ℕ) → Formula₁ → Formula₂
remap₁ r (var₁ x)   = var₂ x
remap₁ r (tmp₁ x)   = tmp₂ (r x)
remap₁ r (and₁ x y) = and₂ (remap₁ r x) (remap₁ r y)
remap₁ r (or₁ x y)  = or₂ (remap₁ r x) (remap₁ r y)
remap₁ r (not₁ x)   = not₂ (remap₁ r x)

evalRemap₁ : ∀ n v t r f → eval₂ v t (remap₁ r (flatten n f)) ≡ eval₁ v (t ∘ r) (flatten n f)
evalRemap₁ n v t r (var₀ x)   = refl
evalRemap₁ n v t r (and₀ x y)
  rewrite sym (evalRemap₁ (n ++ [ false ]) v t r x)
  rewrite sym (evalRemap₁ (n ++ [ true ]) v t r y)
  = refl
evalRemap₁ n v t r (or₀ x y)
  rewrite sym (evalRemap₁ (n ++ [ false ]) v t r x)
  rewrite sym (evalRemap₁ (n ++ [ true ]) v t r y)
  = refl
evalRemap₁ n v t r (not₀ x)
  rewrite sym (evalRemap₁ (n ++ [ false ]) v t r x)
  = refl
evalRemap₁ n v t r (xor₀ x y)
  rewrite sym (evalRemap₁ (n ++ [ false ]) v t r x)
  rewrite sym (evalRemap₁ (n ++ [ true ]) v t r y)
  = refl
evalRemap₁ n v t r (iff₀ x y)
  rewrite sym (evalRemap₁ (n ++ [ false ]) v t r x)
  rewrite sym (evalRemap₁ (n ++ [ true ]) v t r y)
  = refl

assign-≡ : ∀ {t₁ t₂} v → (f : Formula₁) → (∀ a → t₁ a ≡ t₂ a) → eval₁ v t₁ f ≡ eval₁ v t₂ f
assign-≡ {t₁} {t₂} v (var₁ x)   p = refl
assign-≡ {t₁} {t₂} v (tmp₁ x)   p = p x
assign-≡ {t₁} {t₂} v (and₁ x y) p = cong₂ _∧_ (assign-≡ v x p) (assign-≡ v y p)
assign-≡ {t₁} {t₂} v (or₁ x y)  p = cong₂ _∨_ (assign-≡ v x p) (assign-≡ v y p)
assign-≡ {t₁} {t₂} v (not₁ x)   p = cong not (assign-≡ v x p)

makeTrue₂ : (ℕ → Bool) → Formula₀ → (ℕ → Bool)
makeTrue₂ v f = makeTrue₁ v f ∘ proj₂ (ℕ→bin 0 f)

transform₂ : Formula₀ → Formula₂
transform₂ f = remap₁ (proj₂ (bin→ℕ 0 f)) (transform₁ f)

transform₂-✓ : ∀ v f → eval₂ v (makeTrue₂ v f) (transform₂ f) ≡ eval₀ v f
transform₂-✓ v f
  rewrite roundtrip 0 v f []
  rewrite evalRemap₁ [] v (makeTrue₁ v f ∘ proj₂ (ℕ→bin 0 f)) (proj₂ (bin→ℕ 0 f)) f
  rewrite assign-≡ v (flatten [] f) (roundtrip 0 v f)
  rewrite sym (transform₁-✓ v f)
  = refl

nextVar : Formula₂ → ℕ
nextVar (var₂ x)   = suc x
nextVar (tmp₂ x)   = 0
nextVar (and₂ x y) = nextVar x ⊔ nextVar y
nextVar (or₂ x y)  = nextVar x ⊔ nextVar y
nextVar (not₂ x)   = nextVar x

merge : ℕ → (ℕ → Bool) → (ℕ → Bool) → (ℕ → Bool)
merge b v t a =
  case a <?ⁿ b of λ where
    (yes _) → v a
    (no  _) → t (a ∸ b)

remap₂ : ℕ → Formula₂ → Formula₃
remap₂ b (var₂ x)   = var₃ x
remap₂ b (tmp₂ x)   = var₃ (b + x)
remap₂ b (and₂ x y) = and₃ (remap₂ b x) (remap₂ b y)
remap₂ b (or₂ x y)  = or₃ (remap₂ b x) (remap₂ b y)
remap₂ b (not₂ x)   = not₃ (remap₂ b x)

foo : ∀ {b} v t f → nextVar f ≤ b → eval₃ (merge b v t) (remap₂ b f) ≡ eval₂ v t f
foo {b} v t (var₂ x)   p
  rewrite <⇒<? p
  = refl
foo {b} v t (tmp₂ x)   p
  rewrite (proj₂ ∘ ≮⇒<? ∘ ≤⇒≯) (m≤m+n b x)
  rewrite m+n∸m≡n b x
  = refl
foo {b} v t (and₂ x y) p
  rewrite foo v t x (m⊔n≤o⇒m≤o (nextVar x) (nextVar y) p)
  rewrite foo v t y (m⊔n≤o⇒n≤o (nextVar x) (nextVar y) p)
  = refl
foo {b} v t (or₂ x y)  p
  rewrite foo v t x (m⊔n≤o⇒m≤o (nextVar x) (nextVar y) p)
  rewrite foo v t y (m⊔n≤o⇒n≤o (nextVar x) (nextVar y) p)
  = refl
foo {b} v t (not₂ x)   p
  rewrite foo v t x p
  = refl

makeTrue₃ : (ℕ → Bool) → Formula₀ → (ℕ → Bool)
makeTrue₃ v f = merge (nextVar (transform₂ f)) v (makeTrue₂ v f)

transform₃ : Formula₀ → Formula₃
-- XXX - more efficient than "let", right?
transform₃ f = (λ f₂ → remap₂ (nextVar f₂) f₂) (transform₂ f)

transform₃-✓ : ∀ v f → eval₃ (makeTrue₃ v f) (transform₃ f) ≡ eval₀ v f
transform₃-✓ v f
  rewrite foo v (makeTrue₂ v f) (transform₂ f) ≤-refl
  rewrite sym (transform₂-✓ v f)
  = refl
