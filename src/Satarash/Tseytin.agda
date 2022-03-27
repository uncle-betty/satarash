-- XXX - fix duplication in rewrite-based proofs (e.g., makeTrue-✓₁ or roundtrip)

module Satarash.Tseytin where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; _xor_ ; _≟_)
open import Data.Bool.Properties
  using (∧-identityʳ ; ∧-idem ; ∨-identityʳ ; ∧-assoc ; ∧-distribʳ-∨ ; ∧-comm)
open import Data.Empty using (⊥)
open import Data.List using (List ; _∷_ ; [] ; [_] ; _++_ ; length)
open import Data.List.Relation.Binary.Equality.DecPropositional (_≟_) using (_≡?_)
open import Data.Maybe using (Maybe ; nothing ; just ; _>>=_ ; map)
open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s ; _<_ ; _+_ ; _∸_ ; _⊔_)
  renaming (_≟_ to _≟ⁿ_ ; _<?_ to _<?ⁿ_)
open import Data.Nat.Properties using (
    ≤-refl ; <-irrefl ; <-trans ; <-transˡ ; n<1+n ; m≤m+n ; m⊔n≤o⇒m≤o ; m⊔n≤o⇒n≤o ;
    <⇒≢ ; <⇒≯ ; <⇒≤ ; ≤⇒≯ ; <-irrelevant ; module ≤-Reasoning ;
    m+n∸m≡n
  )
open import Data.Product using (∃-syntax ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_ ; case_of_ ; flip)
open import Relation.Binary.PropositionalEquality using (
    _≡_ ; refl ; sym ; cong ; cong₂ ; trans ; _≢_ ; ≢-sym ;
    ≡-≟-identity ; ≢-≟-identity ; module ≡-Reasoning
  )
open import Relation.Nullary using (¬_ ; Dec ; yes ; no ; _because_ ; ofʸ ; ofⁿ)
open import Relation.Nullary.Decidable using (dec-yes-irr ; dec-no)
open import Relation.Nullary.Negation using (contradiction)
open import Tactic.Cong using (cong!)

bitsᶜ : ℕ
bitsᶜ = 24

import Satarash.Verifier bitsᶜ as V
import Satarash.Parser as P

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

-- structural constraints, temporaries with binary identifiers, CNF patterns
data Formula₁ : ℕ → Set where
  var₁ : ℕ → Formula₁ 3
  tmp₁ : List Bool → Formula₁ 3
  and₁ : {m n : ℕ} → Formula₁ m → Formula₁ n → Formula₁ 0
  or₁  : {m n : ℕ} → Formula₁ (suc m) → Formula₁ (suc n) → Formula₁ 1
  not₁ : Formula₁ 3 → Formula₁ 2

eval₁ : {l : ℕ} → (ℕ → Bool) → (List Bool → Bool) → Formula₁ l → Bool
eval₁ v t (var₁ x)   = v x
eval₁ v t (tmp₁ x)   = t x
eval₁ v t (and₁ x y) = eval₁ v t x ∧ eval₁ v t y
eval₁ v t (or₁ x y)  = eval₁ v t x ∨ eval₁ v t y
eval₁ v t (not₁ x)   = not (eval₁ v t x)

-- temporaries with ℕ identifiers
data Formula₂ : ℕ → Set where
  var₂ : ℕ → Formula₂ 3
  tmp₂ : ℕ → Formula₂ 3
  and₂ : {m n : ℕ} → Formula₂ m → Formula₂ n → Formula₂ 0
  or₂  : {m n : ℕ} → Formula₂ (suc m) → Formula₂ (suc n) → Formula₂ 1
  not₂ : Formula₂ 3 → Formula₂ 2

eval₂ : {l : ℕ} → (ℕ → Bool) → (ℕ → Bool) → Formula₂ l → Bool
eval₂ v t (var₂ x)   = v x
eval₂ v t (tmp₂ x)   = t x
eval₂ v t (and₂ x y) = eval₂ v t x ∧ eval₂ v t y
eval₂ v t (or₂ x y)  = eval₂ v t x ∨ eval₂ v t y
eval₂ v t (not₂ x)   = not (eval₂ v t x)

-- temporaries turned into variables
data Formula₃ : ℕ → Set where
  var₃ : ℕ → Formula₃ 3
  and₃ : {m n : ℕ} → Formula₃ m → Formula₃ n → Formula₃ 0
  or₃  : {m n : ℕ} → Formula₃ (suc m) → Formula₃ (suc n) → Formula₃ 1
  not₃ : Formula₃ 3 → Formula₃ 2

eval₃ : {l : ℕ} → (ℕ → Bool) → Formula₃ l → Bool
eval₃ v (var₃ x)   = v x
eval₃ v (and₃ x y) = eval₃ v x ∧ eval₃ v y
eval₃ v (or₃ x y)  = eval₃ v x ∨ eval₃ v y
eval₃ v (not₃ x)   = not (eval₃ v x)

-- list of clauses
Formula₄ : Set
Formula₄ = List V.Clause

eval₄ : (ℕ → Bool) → Formula₄ → Bool
eval₄ = P.eval-∷ bitsᶜ

-- verifier's representation
Formula₅ : Set
Formula₅ = V.Formula

eval₅ : (ℕ → Bool) → Formula₅ → Bool
eval₅ = V.eval

x↔x : ∀ x → (x ↔ x) ≡ true
x↔x false = refl
x↔x true  = refl

x↔t≡x : ∀ x → (x ↔ true) ≡ x
x↔t≡x false = refl
x↔t≡x true  = refl

x↔f≡¬x : ∀ x → (x ↔ false) ≡ not x
x↔f≡¬x false = refl
x↔f≡¬x true  = refl

var-pat : (x r : Formula₁ 3) → Formula₁ 0
var-pat x r = and₁ (or₁ x (not₁ r)) (or₁ (not₁ x) r)

var-pat-✓ : ∀ x r → (r ↔ x) ≡ (x ∨ not r) ∧ (not x ∨ r)
var-pat-✓ false r = trans (x↔f≡¬x r) (sym (∧-identityʳ (not r)))
var-pat-✓ true  r = x↔t≡x r

∧-pat : (x y r : Formula₁ 3) → Formula₁ 0
∧-pat x y r = and₁ (or₁ (not₁ x) (or₁ (not₁ y) r)) (and₁ (or₁ x (not₁ r)) (or₁ y (not₁ r)))

∧-pat-✓ : ∀ x y r → (r ↔ x ∧ y) ≡ (not x ∨ not y ∨ r) ∧ (x ∨ not r) ∧ (y ∨ not r)
∧-pat-✓ false false r = trans (x↔f≡¬x r) (sym (∧-idem (not r)))
∧-pat-✓ false true  r = trans (x↔f≡¬x r) (sym (∧-identityʳ (not r)))
∧-pat-✓ true false  r = x↔f≡¬x r
∧-pat-✓ true true   r = trans (x↔t≡x r) (sym (∧-identityʳ r))

∨-pat : (x y r : Formula₁ 3) → Formula₁ 0
∨-pat x y r = and₁ (or₁ x (or₁ y (not₁ r))) (and₁ (or₁ (not₁ x) r) (or₁ (not₁ y) r))

∨-pat-✓ : ∀ x y r → (r ↔ x ∨ y) ≡ (x ∨ y ∨ not r) ∧ (not x ∨ r) ∧ (not y ∨ r)
∨-pat-✓ false false r = trans (x↔f≡¬x r) (sym (∧-identityʳ (not r)))
∨-pat-✓ false true  r = x↔t≡x r
∨-pat-✓ true  false r = trans (x↔t≡x r) (sym (∧-identityʳ r))
∨-pat-✓ true  true  r = trans (x↔t≡x r) (sym (∧-idem r))

not-pat : (x r : Formula₁ 3) → Formula₁ 0
not-pat x r = and₁ (or₁ (not₁ x) (not₁ r)) (or₁ x r)

not-pat-✓ : ∀ x r → (r ↔ not x) ≡ (not x ∨ not r) ∧ (x ∨ r)
not-pat-✓ false r = x↔t≡x r
not-pat-✓ true  r = trans (x↔f≡¬x r) (sym (∧-identityʳ (not r)))

xor-pat : (x y r : Formula₁ 3) → Formula₁ 0
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

↔-pat : (x y r : Formula₁ 3) → Formula₁ 0
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

flatten : List Bool → Formula₀ → Formula₁ 0

flatten₀ : List Bool → ℕ → Formula₁ 0
flatten₀ n x = var-pat (tmp₁ n) (var₁ x)

flatten₁ : List Bool → (Formula₁ 3 → Formula₁ 3 → Formula₁ 0) → Formula₀ → Formula₁ 0
flatten₁ n p x =
  let s = flatten (n ++ [ false ]) x in
  and₁ (p (tmp₁ (n ++ [ false ])) (tmp₁ n)) s

flatten₂ : List Bool → (Formula₁ 3 → Formula₁ 3 → Formula₁ 3 → Formula₁ 0) → Formula₀ → Formula₀ →
  Formula₁ 0
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

transform₁ : Formula₀ → Formula₁ 0
transform₁ f = and₁ (tmp₁ []) (flatten [] f)

transform₁-✓ : ∀ v f → eval₁ v (makeTrue₁ v f) (transform₁ f) ≡ eval₀ v f
transform₁-✓ v f
  rewrite makeTrue₁-✓₁ v f
  rewrite makeTrue₁-✓₂ v f
  = ∧-identityʳ (eval₀ v f)

≡⇒≡? : ∀ {x y} → (p : x ≡ y) → x ≡? y ≡ yes p
≡⇒≡? = ≡-≟-identity _≡?_

≢⇒≡? : ∀ {x y} → (p : x ≢ y) → x ≡? y ≡ no p
≢⇒≡? = ≢-≟-identity _≡?_

≡⇒≟ⁿ : ∀ {x y} → (p : x ≡ y) → (x ≟ⁿ y) ≡ yes p
≡⇒≟ⁿ = ≡-≟-identity _≟ⁿ_

≢⇒≟ⁿ : ∀ {x y} → (p : x ≢ y) → (x ≟ⁿ y) ≡ no p
≢⇒≟ⁿ = ≢-≟-identity _≟ⁿ_

<⇒<? : ∀ {x y} → (p : x < y) → (x <?ⁿ y) ≡ yes p
<⇒<? {x} {y} p = dec-yes-irr (x <?ⁿ y) <-irrelevant p

≮⇒<? : ∀ {x y} → (p : ¬ (x < y)) → (x <?ⁿ y) ≡ no p
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
  rewrite (≮⇒<? ∘ <⇒≯) (bw₁<fw₁fw₁ n x y)
  rewrite ≮⇒<? (<-irrefl (fw₁fw₁≡bw₁bw₁ n x y))
  = refl
roundtrip n v (and₀ x y) (false ∷ as)
  rewrite <⇒<? (fw₂<bw₁ n x as)
  = roundtrip n v x as
roundtrip n v (and₀ x y) (true ∷ as)
  rewrite (≮⇒<? ∘ ≤⇒≯) (bw₁≤fw₂fw₁ n x y as)
  rewrite <⇒<? (fw₂fw₁<bw₁bw₁ n x y as)
  rewrite sym (fw₁≡bw₁ n x)
  = roundtrip (proj₁ (bin→ℕ n x)) v y as
roundtrip n v (or₀ x y) []
  rewrite (≮⇒<? ∘ <⇒≯) (bw₁<fw₁fw₁ n x y)
  rewrite ≮⇒<? (<-irrefl (fw₁fw₁≡bw₁bw₁ n x y))
  = refl
roundtrip n v (or₀ x y) (false ∷ as)
  rewrite <⇒<? (fw₂<bw₁ n x as)
  = roundtrip n v x as
roundtrip n v (or₀ x y) (true ∷ as)
  rewrite (≮⇒<? ∘ ≤⇒≯) (bw₁≤fw₂fw₁ n x y as)
  rewrite <⇒<? (fw₂fw₁<bw₁bw₁ n x y as)
  rewrite sym (fw₁≡bw₁ n x)
  = roundtrip (proj₁ (bin→ℕ n x)) v y as
roundtrip n v (not₀ x)   []
  rewrite ≡⇒≟ⁿ (fw₁≡bw₁ n x)
  = refl
roundtrip n v (not₀ x)   (a ∷ as)
  rewrite (≢⇒≟ⁿ ∘ <⇒≢) (fw₂<bw₁ n x as)
  = roundtrip n v x as
roundtrip n v (xor₀ x y) []
  rewrite (≮⇒<? ∘ <⇒≯) (bw₁<fw₁fw₁ n x y)
  rewrite ≮⇒<? (<-irrefl (fw₁fw₁≡bw₁bw₁ n x y))
  = refl
roundtrip n v (xor₀ x y) (false ∷ as)
  rewrite <⇒<? (fw₂<bw₁ n x as)
  = roundtrip n v x as
roundtrip n v (xor₀ x y) (true ∷ as)
  rewrite (≮⇒<? ∘ ≤⇒≯) (bw₁≤fw₂fw₁ n x y as)
  rewrite <⇒<? (fw₂fw₁<bw₁bw₁ n x y as)
  rewrite sym (fw₁≡bw₁ n x)
  = roundtrip (proj₁ (bin→ℕ n x)) v y as
roundtrip n v (iff₀ x y) []
  rewrite (≮⇒<? ∘ <⇒≯) (bw₁<fw₁fw₁ n x y)
  rewrite ≮⇒<? (<-irrefl (fw₁fw₁≡bw₁bw₁ n x y))
  = refl
roundtrip n v (iff₀ x y) (false ∷ as)
  rewrite <⇒<? (fw₂<bw₁ n x as)
  = roundtrip n v x as
roundtrip n v (iff₀ x y) (true ∷ as)
  rewrite (≮⇒<? ∘ ≤⇒≯) (bw₁≤fw₂fw₁ n x y as)
  rewrite <⇒<? (fw₂fw₁<bw₁bw₁ n x y as)
  rewrite sym (fw₁≡bw₁ n x)
  = roundtrip (proj₁ (bin→ℕ n x)) v y as

remap₁ : {l : ℕ} → (List Bool → ℕ) → Formula₁ l → Formula₂ l
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

assign-≡ : ∀ {l t₁ t₂} v → (f : Formula₁ l) → (∀ a → t₁ a ≡ t₂ a) → eval₁ v t₁ f ≡ eval₁ v t₂ f
assign-≡ {t₁} {t₂} v (var₁ x)   p = refl
assign-≡ {t₁} {t₂} v (tmp₁ x)   p = p x
assign-≡ {t₁} {t₂} v (and₁ x y) p = cong₂ _∧_ (assign-≡ v x p) (assign-≡ v y p)
assign-≡ {t₁} {t₂} v (or₁ x y)  p = cong₂ _∨_ (assign-≡ v x p) (assign-≡ v y p)
assign-≡ {t₁} {t₂} v (not₁ x)   p = cong not (assign-≡ v x p)

makeTrue₂ : (ℕ → Bool) → Formula₀ → (ℕ → Bool)
makeTrue₂ v f = makeTrue₁ v f ∘ proj₂ (ℕ→bin 0 f)

transform₂ : Formula₀ → Formula₂ 0
transform₂ f = remap₁ (proj₂ (bin→ℕ 0 f)) (transform₁ f)

transform₂-✓ : ∀ v f → eval₂ v (makeTrue₂ v f) (transform₂ f) ≡ eval₀ v f
transform₂-✓ v f
  rewrite roundtrip 0 v f []
  rewrite evalRemap₁ [] v (makeTrue₁ v f ∘ proj₂ (ℕ→bin 0 f)) (proj₂ (bin→ℕ 0 f)) f
  rewrite assign-≡ v (flatten [] f) (roundtrip 0 v f)
  rewrite sym (transform₁-✓ v f)
  = refl

nextVar : {l : ℕ} → Formula₂ l → ℕ
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

remap₂ : {l : ℕ} → ℕ → Formula₂ l → Formula₃ l
remap₂ b (var₂ x)   = var₃ x
remap₂ b (tmp₂ x)   = var₃ (b + x)
remap₂ b (and₂ x y) = and₃ (remap₂ b x) (remap₂ b y)
remap₂ b (or₂ x y)  = or₃ (remap₂ b x) (remap₂ b y)
remap₂ b (not₂ x)   = not₃ (remap₂ b x)

mergeRemap : ∀ {b l} v t f → nextVar f ≤ b → eval₃ (merge b v t) (remap₂ {l} b f) ≡ eval₂ v t f
mergeRemap {b} v t (var₂ x)   p
  rewrite <⇒<? p
  = refl
mergeRemap {b} v t (tmp₂ x)   p
  rewrite (≮⇒<? ∘ ≤⇒≯) (m≤m+n b x)
  rewrite m+n∸m≡n b x
  = refl
mergeRemap {b} v t (and₂ x y) p
  rewrite mergeRemap v t x (m⊔n≤o⇒m≤o (nextVar x) (nextVar y) p)
  rewrite mergeRemap v t y (m⊔n≤o⇒n≤o (nextVar x) (nextVar y) p)
  = refl
mergeRemap {b} v t (or₂ x y)  p
  rewrite mergeRemap v t x (m⊔n≤o⇒m≤o (nextVar x) (nextVar y) p)
  rewrite mergeRemap v t y (m⊔n≤o⇒n≤o (nextVar x) (nextVar y) p)
  = refl
mergeRemap {b} v t (not₂ x)   p
  rewrite mergeRemap v t x p
  = refl

makeTrue₃ : (ℕ → Bool) → Formula₀ → (ℕ → Bool)
makeTrue₃ v f = merge (nextVar (transform₂ f)) v (makeTrue₂ v f)

transform₃ : Formula₀ → Formula₃ 0
-- XXX - more efficient than "let"?
transform₃ f = (λ f₂ → remap₂ (nextVar f₂) f₂) (transform₂ f)

transform₃-✓ : ∀ v f → eval₃ (makeTrue₃ v f) (transform₃ f) ≡ eval₀ v f
transform₃-✓ v f
  rewrite mergeRemap v (makeTrue₂ v f) (transform₂ f) ≤-refl
  rewrite sym (transform₂-✓ v f)
  = refl

to-∷-∨ : {l : ℕ} → (f : Formula₃ (suc l)) → List V.Literal
to-∷-∨ (var₃ x)        = [ V.pos x ]
to-∷-∨ (not₃ (var₃ x)) = [ V.neg x ]
to-∷-∨ (or₃ x y)       = to-∷-∨ x ++ to-∷-∨ y

to-∷-∧ : (f : Formula₃ 0) → List V.Clause
to-∷-∧ (and₃ {zero}  {zero} x y)  = to-∷-∧ x ++ to-∷-∧ y
to-∷-∧ (and₃ {zero}  {suc n} x y) = to-∷-∧ x ++ [ to-∷-∨ y ]
to-∷-∧ (and₃ {suc m} {zero} x y)  = [ to-∷-∨ x ] ++ to-∷-∧ y
to-∷-∧ (and₃ {suc m} {suc n} x y) = [ to-∷-∨ x ] ++ [ to-∷-∨ y ]

++⇒∧ : ∀ v x y → eval₄ v (x ++ y) ≡ eval₄ v x ∧ eval₄ v y
++⇒∧ v []       y = refl
++⇒∧ v (x ∷ xs) y
  rewrite ++⇒∧ v xs y
  = sym (∧-assoc (V.evalᶜ v x) (eval₄ v xs) (eval₄ v y))

to-∷-∨-✓ : ∀ {l} v f → eval₄ v [ to-∷-∨ {l} f ] ≡ eval₃ v f
to-∷-∨-✓ v (var₃ x)        = trans (∧-identityʳ (v x ∨ false)) (∨-identityʳ (v x))
to-∷-∨-✓ v (not₃ (var₃ x)) = trans (∧-identityʳ ((not (v x)) ∨ false)) (∨-identityʳ (not (v x)))
to-∷-∨-✓ v (or₃ x y)
  rewrite V.++⇒∨ v (to-∷-∨ x) (to-∷-∨ y)
  rewrite sym (to-∷-∨-✓ v x)
  rewrite sym (to-∷-∨-✓ v y)
  = ∧-distribʳ-∨ true (V.evalᶜ v (to-∷-∨ x)) (V.evalᶜ v (to-∷-∨ y))

to-∷-∧-✓ : ∀ v f → eval₄ v (to-∷-∧ f) ≡ eval₃ v f
to-∷-∧-✓ v (and₃ {zero}  {zero}  x y)
  rewrite ++⇒∧ v (to-∷-∧ x) (to-∷-∧ y)
  rewrite to-∷-∧-✓ v x
  rewrite to-∷-∧-✓ v y
  = refl
to-∷-∧-✓ v (and₃ {zero}  {suc n} x y)
  rewrite ++⇒∧ v (to-∷-∧ x) [ to-∷-∨ y ]
  rewrite to-∷-∧-✓ v x
  rewrite to-∷-∨-✓ v y
  = refl
to-∷-∧-✓ v (and₃ {suc m} {zero}  x y)
  rewrite ++⇒∧ v [ to-∷-∨ x ] (to-∷-∧ y)
  rewrite to-∷-∨-✓ v x
  rewrite to-∷-∧-✓ v y
  = refl
to-∷-∧-✓ v (and₃ {suc m} {suc n} x y)
  rewrite sym (to-∷-∨-✓ v x)
  rewrite sym (to-∷-∨-✓ v y)
  rewrite ∧-identityʳ (V.evalᶜ v (to-∷-∨ x))
  = refl

transform₄ : Formula₀ → Formula₄
transform₄ f = to-∷-∧ (transform₃ f)

transform₄-✓ : ∀ v f → eval₄ (makeTrue₃ v f) (transform₄ f) ≡ eval₀ v f
transform₄-✓ v f
 rewrite to-∷-∧-✓ (makeTrue₃ v f) (transform₃ f)
 rewrite sym (transform₃-✓ v f)
 = refl

unsat₄-✓ : ∀ f → (∀ v → eval₄ v (transform₄ f) ≡ false) → (∀ v → eval₀ v f ≡ false)
unsat₄-✓ f p v = sym (trans (sym (p (makeTrue₃ v f))) (transform₄-✓ v f))

transform₅ : Formula₀ → Maybe Formula₅
transform₅ f = P.from-∷ bitsᶜ (transform₄ f)

transform₅-✓ : ∀ v f₀ f₅ → transform₅ f₀ ≡ just f₅ → eval₅ (makeTrue₃ v f₀) f₅ ≡ eval₀ v f₀
transform₅-✓ v f₀ f₅ p
  rewrite P.from-∷-✓ bitsᶜ (makeTrue₃ v f₀) (transform₄ f₀) f₅ p
  rewrite sym (transform₄-✓ v f₀)
  = refl

unsat₅-✓ : ∀ f₀ f₅ → transform₅ f₀ ≡ just f₅ → (∀ v → eval₅ v f₅ ≡ false) →
  (∀ v → eval₀ v f₀ ≡ false)
unsat₅-✓ f₀ f₅ p₁ p₂ v = sym (trans (sym (p₂ (makeTrue₃ v f₀))) (transform₅-✓ v f₀ f₅ p₁))
