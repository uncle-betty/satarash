-- XXX - fix duplication in rewrite-based proofs (e.g., makeTrue-✓₁ or roundtrip)

module Satarash.Tseytin where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; _xor_ ; if_then_else_ ; _≟_)
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

import Satarash.Verifier as V
import Satarash.Parser as P

infix 4 _⇔_

_⇔_ : (x y : Bool) → Bool
false ⇔ false = true
false ⇔ true  = false
true  ⇔ false = false
true  ⇔ true  = true

infix 4 _⇒_

_⇒_ : (x y : Bool) → Bool
false ⇒ false = true
false ⇒ true  = true
true  ⇒ false = false
true  ⇒ true  = true

-- original
data Formula₀ : Set where
  con₀ : Bool → Formula₀
  var₀ : ℕ → Formula₀
  and₀ : Formula₀ → Formula₀ → Formula₀
  or₀  : Formula₀ → Formula₀ → Formula₀
  not₀ : Formula₀ → Formula₀
  xor₀ : Formula₀ → Formula₀ → Formula₀
  iff₀ : Formula₀ → Formula₀ → Formula₀
  imp₀ : Formula₀ → Formula₀ → Formula₀
  ite₀ : Formula₀ → Formula₀ → Formula₀ → Formula₀

eval₀ : (ℕ → Bool) → Formula₀ → Bool
eval₀ v (con₀ x)     = x
eval₀ v (var₀ x)     = v x
eval₀ v (and₀ x y)   = eval₀ v x ∧ eval₀ v y
eval₀ v (or₀ x y)    = eval₀ v x ∨ eval₀ v y
eval₀ v (not₀ x)     = not (eval₀ v x)
eval₀ v (xor₀ x y)   = eval₀ v x xor eval₀ v y
eval₀ v (iff₀ x y)   = eval₀ v x ⇔ eval₀ v y
eval₀ v (imp₀ x y)   = eval₀ v x ⇒ eval₀ v y
eval₀ v (ite₀ x y z) = if eval₀ v x then eval₀ v y else eval₀ v z

-- fewer operations, folded constants
data Formula₁ : Set where
  var₁ : ℕ → Formula₁
  and₁ : Formula₁ → Formula₁ → Formula₁
  or₁  : Formula₁ → Formula₁ → Formula₁
  not₁ : Formula₁ → Formula₁
  xor₁ : Formula₁ → Formula₁ → Formula₁

eval₁ : (ℕ → Bool) → Formula₁ → Bool
eval₁ v (var₁ x)   = v x
eval₁ v (and₁ x y) = eval₁ v x ∧ eval₁ v y
eval₁ v (or₁ x y)  = eval₁ v x ∨ eval₁ v y
eval₁ v (not₁ x)   = not (eval₁ v x)
eval₁ v (xor₁ x y) = eval₁ v x xor eval₁ v y

-- structural constraints, temporaries with binary identifiers, CNF patterns
data Formula₂ : ℕ → Set where
  var₂ : ℕ → Formula₂ 3
  tmp₂ : List Bool → Formula₂ 3
  and₂ : {m n : ℕ} → Formula₂ m → Formula₂ n → Formula₂ 0
  or₂  : {m n : ℕ} → Formula₂ (suc m) → Formula₂ (suc n) → Formula₂ 1
  not₂ : Formula₂ 3 → Formula₂ 2

eval₂ : {l : ℕ} → (ℕ → Bool) → (List Bool → Bool) → Formula₂ l → Bool
eval₂ v t (var₂ x)   = v x
eval₂ v t (tmp₂ x)   = t x
eval₂ v t (and₂ x y) = eval₂ v t x ∧ eval₂ v t y
eval₂ v t (or₂ x y)  = eval₂ v t x ∨ eval₂ v t y
eval₂ v t (not₂ x)   = not (eval₂ v t x)

-- temporaries with ℕ identifiers
data Formula₃ : ℕ → Set where
  var₃ : ℕ → Formula₃ 3
  tmp₃ : ℕ → Formula₃ 3
  and₃ : {m n : ℕ} → Formula₃ m → Formula₃ n → Formula₃ 0
  or₃  : {m n : ℕ} → Formula₃ (suc m) → Formula₃ (suc n) → Formula₃ 1
  not₃ : Formula₃ 3 → Formula₃ 2

eval₃ : {l : ℕ} → (ℕ → Bool) → (ℕ → Bool) → Formula₃ l → Bool
eval₃ v t (var₃ x)   = v x
eval₃ v t (tmp₃ x)   = t x
eval₃ v t (and₃ x y) = eval₃ v t x ∧ eval₃ v t y
eval₃ v t (or₃ x y)  = eval₃ v t x ∨ eval₃ v t y
eval₃ v t (not₃ x)   = not (eval₃ v t x)

-- temporaries turned into variables
data Formula₄ : ℕ → Set where
  var₄ : ℕ → Formula₄ 3
  and₄ : {m n : ℕ} → Formula₄ m → Formula₄ n → Formula₄ 0
  or₄  : {m n : ℕ} → Formula₄ (suc m) → Formula₄ (suc n) → Formula₄ 1
  not₄ : Formula₄ 3 → Formula₄ 2

eval₄ : {l : ℕ} → (ℕ → Bool) → Formula₄ l → Bool
eval₄ v (var₄ x)   = v x
eval₄ v (and₄ x y) = eval₄ v x ∧ eval₄ v y
eval₄ v (or₄ x y)  = eval₄ v x ∨ eval₄ v y
eval₄ v (not₄ x)   = not (eval₄ v x)

-- list of clauses
Formula₅ : Set
Formula₅ = List V.Clause

eval₅ : (ℕ → Bool) → Formula₅ → Bool
eval₅ = P.eval-∷

-- verifier's representation
Formula₆ : Set
Formula₆ = V.Formula

eval₆ : (ℕ → Bool) → Formula₆ → Bool
eval₆ = V.eval

x⇔x : ∀ x → (x ⇔ x) ≡ true
x⇔x false = refl
x⇔x true  = refl

x⇔t≡x : ∀ x → (x ⇔ true) ≡ x
x⇔t≡x false = refl
x⇔t≡x true  = refl

x⇔f≡¬x : ∀ x → (x ⇔ false) ≡ not x
x⇔f≡¬x false = refl
x⇔f≡¬x true  = refl

var-pat : (x r : Formula₂ 3) → Formula₂ 0
var-pat x r = and₂ (or₂ x (not₂ r)) (or₂ (not₂ x) r)

var-pat-✓ : ∀ x r → (r ⇔ x) ≡ (x ∨ not r) ∧ (not x ∨ r)
var-pat-✓ false r = trans (x⇔f≡¬x r) (sym (∧-identityʳ (not r)))
var-pat-✓ true  r = x⇔t≡x r

∧-pat : (x y r : Formula₂ 3) → Formula₂ 0
∧-pat x y r = and₂ (or₂ (not₂ x) (or₂ (not₂ y) r)) (and₂ (or₂ x (not₂ r)) (or₂ y (not₂ r)))

∧-pat-✓ : ∀ x y r → (r ⇔ x ∧ y) ≡ (not x ∨ not y ∨ r) ∧ (x ∨ not r) ∧ (y ∨ not r)
∧-pat-✓ false false r = trans (x⇔f≡¬x r) (sym (∧-idem (not r)))
∧-pat-✓ false true  r = trans (x⇔f≡¬x r) (sym (∧-identityʳ (not r)))
∧-pat-✓ true false  r = x⇔f≡¬x r
∧-pat-✓ true true   r = trans (x⇔t≡x r) (sym (∧-identityʳ r))

∨-pat : (x y r : Formula₂ 3) → Formula₂ 0
∨-pat x y r = and₂ (or₂ x (or₂ y (not₂ r))) (and₂ (or₂ (not₂ x) r) (or₂ (not₂ y) r))

∨-pat-✓ : ∀ x y r → (r ⇔ x ∨ y) ≡ (x ∨ y ∨ not r) ∧ (not x ∨ r) ∧ (not y ∨ r)
∨-pat-✓ false false r = trans (x⇔f≡¬x r) (sym (∧-identityʳ (not r)))
∨-pat-✓ false true  r = x⇔t≡x r
∨-pat-✓ true  false r = trans (x⇔t≡x r) (sym (∧-identityʳ r))
∨-pat-✓ true  true  r = trans (x⇔t≡x r) (sym (∧-idem r))

not-pat : (x r : Formula₂ 3) → Formula₂ 0
not-pat x r = and₂ (or₂ (not₂ x) (not₂ r)) (or₂ x r)

not-pat-✓ : ∀ x r → (r ⇔ not x) ≡ (not x ∨ not r) ∧ (x ∨ r)
not-pat-✓ false r = x⇔t≡x r
not-pat-✓ true  r = trans (x⇔f≡¬x r) (sym (∧-identityʳ (not r)))

xor-pat : (x y r : Formula₂ 3) → Formula₂ 0
xor-pat x y r =
  and₂ (or₂ (not₂ x) (or₂ (not₂ y) (not₂ r)))
  (and₂ (or₂ x (or₂ y (not₂ r)))
  (and₂ (or₂ x (or₂ (not₂ y) r))
  (or₂ (not₂ x) (or₂ y r))))

xor-pat-✓ : ∀ x y r →
  (r ⇔ x xor y) ≡ (not x ∨ not y ∨ not r) ∧ (x ∨ y ∨ not r) ∧ (x ∨ not y ∨ r) ∧ (not x ∨ y ∨ r)
xor-pat-✓ false false r = trans (x⇔f≡¬x r) (sym (∧-identityʳ (not r)))
xor-pat-✓ false true  r = trans (x⇔t≡x r) (sym (∧-identityʳ r))
xor-pat-✓ true  false r = x⇔t≡x r
xor-pat-✓ true  true  r = trans (x⇔f≡¬x r) (sym (∧-identityʳ (not r)))

⇔-pat : (x y r : Formula₂ 3) → Formula₂ 0
⇔-pat x y r =
  and₂ (or₂ x (or₂ y r))
  (and₂ (or₂ (not₂ x) (or₂ (not₂ y) r))
  (and₂ (or₂ (not₂ x) (or₂ y (not₂ r)))
  (or₂ x (or₂ (not₂ y) (not₂ r)))))

⇔-pat-✓ : ∀ x y r →
  (r ⇔ (x ⇔ y)) ≡ (x ∨ y ∨ r) ∧ (not x ∨ not y ∨ r) ∧ (not x ∨ y ∨ not r) ∧ (x ∨ not y ∨ not r)
⇔-pat-✓ false false r = trans (x⇔t≡x r) (sym (∧-identityʳ r))
⇔-pat-✓ false true  r = x⇔f≡¬x r
⇔-pat-✓ true  false r = trans (x⇔f≡¬x r) (sym (∧-identityʳ (not r)))
⇔-pat-✓ true  true  r = trans (x⇔t≡x r) (sym (∧-identityʳ r))

flatten : List Bool → Formula₁ → Formula₂ 0

flatten₀ : List Bool → ℕ → Formula₂ 0
flatten₀ n x = var-pat (tmp₂ n) (var₂ x)

flatten₁ : List Bool → (Formula₂ 3 → Formula₂ 3 → Formula₂ 0) → Formula₁ → Formula₂ 0
flatten₁ n p x =
  let s = flatten (n ++ [ false ]) x in
  and₂ (p (tmp₂ (n ++ [ false ])) (tmp₂ n)) s

flatten₂ : List Bool → (Formula₂ 3 → Formula₂ 3 → Formula₂ 3 → Formula₂ 0) → Formula₁ → Formula₁ →
  Formula₂ 0
flatten₂ n p x y =
  let sˡ = flatten (n ++ [ false ]) x in
  let sʳ = flatten (n ++ [ true ]) y in
  (and₂ (and₂ (p (tmp₂ (n ++ [ false ])) (tmp₂ (n ++ [ true ])) (tmp₂ n)) sˡ) sʳ)

flatten n (var₁ x)   = flatten₀ n x
flatten n (and₁ x y) = flatten₂ n ∧-pat x y
flatten n (or₁ x y)  = flatten₂ n ∨-pat x y
flatten n (not₁ x)   = flatten₁ n not-pat x
flatten n (xor₁ x y) = flatten₂ n xor-pat x y

module _ where
  makeTrue₂ : (ℕ → Bool) → Formula₁ → (List Bool → Bool)

  module ⟨makeTrue₂⟩ where
    aux₁ : (ℕ → Bool) → (Bool → Bool) → Formula₁ → (List Bool → Bool)
    aux₁ v op x =
      let t′ = makeTrue₂ v x in
        λ where
          []      → op (t′ [])
          (_ ∷ n) → t′ n

    aux₂ : (ℕ → Bool) → (Bool → Bool → Bool) → Formula₁ → Formula₁ → (List Bool → Bool)
    aux₂ v op x y =
      let tˡ = makeTrue₂ v x in
      let tʳ = makeTrue₂ v y in
        λ where
          []          → op (tˡ []) (tʳ [])
          (false ∷ n) → tˡ n
          (true ∷ n)  → tʳ n

  open ⟨makeTrue₂⟩

  makeTrue₂ v (var₁ x)   = λ _ → v x
  makeTrue₂ v (and₁ x y) = aux₂ v _∧_ x y
  makeTrue₂ v (or₁ x y)  = aux₂ v _∨_ x y
  makeTrue₂ v (not₁ x)   = aux₁ v not x
  makeTrue₂ v (xor₁ x y) = aux₂ v _xor_ x y

evalCons : ∀ m n v t f → eval₂ v t (flatten (m ∷ n) f) ≡ eval₂ v (t ∘ (m ∷_)) (flatten n f)
evalCons m n v t (var₁ x) = refl
evalCons m n v t (and₁ x y)
  rewrite sym (evalCons m (n ++ [ false ]) v t x)
  rewrite sym (evalCons m (n ++ [ true ]) v t y)
  = refl
evalCons m n v t (or₁ x y)
  rewrite sym (evalCons m (n ++ [ false ]) v t x)
  rewrite sym (evalCons m (n ++ [ true ]) v t y)
  = refl
evalCons m n v t (not₁ x)
  rewrite sym (evalCons m (n ++ [ false ]) v t x)
  = refl
evalCons m n v t (xor₁ x y)
  rewrite sym (evalCons m (n ++ [ false ]) v t x)
  rewrite sym (evalCons m (n ++ [ true ]) v t y)
  = refl

makeTrue₂-✓₁ : ∀ v f → eval₂ v (makeTrue₂ v f) (flatten [] f) ≡ true
makeTrue₂-✓₁ v (var₁ x)
  rewrite sym (var-pat-✓ (v x) (v x))
  = x⇔x (v x)
makeTrue₂-✓₁ v (and₁ x y)
  rewrite sym (∧-pat-✓ (makeTrue₂ v (and₁ x y) [ false ]) (makeTrue₂ v (and₁ x y) [ true ])
    (makeTrue₂ v (and₁ x y) []))
  rewrite evalCons false [] v (makeTrue₂ v (and₁ x y)) x
  rewrite evalCons true [] v (makeTrue₂ v (and₁ x y)) y
  rewrite makeTrue₂-✓₁ v x
  rewrite makeTrue₂-✓₁ v y
  rewrite x⇔x (makeTrue₂ v x [] ∧ makeTrue₂ v y [])
  = refl
makeTrue₂-✓₁ v (or₁ x y)
  rewrite sym (∨-pat-✓ (makeTrue₂ v (or₁ x y) [ false ]) (makeTrue₂ v (or₁ x y) [ true ])
    (makeTrue₂ v (or₁ x y) []))
  rewrite evalCons false [] v (makeTrue₂ v (or₁ x y)) x
  rewrite evalCons true [] v (makeTrue₂ v (or₁ x y)) y
  rewrite makeTrue₂-✓₁ v x
  rewrite makeTrue₂-✓₁ v y
  rewrite x⇔x (makeTrue₂ v x [] ∨ makeTrue₂ v y [])
  = refl
makeTrue₂-✓₁ v (not₁ x)
  rewrite sym (not-pat-✓ (makeTrue₂ v (not₁ x) [ false ]) (makeTrue₂ v (not₁ x) []))
  rewrite evalCons false [] v (makeTrue₂ v (not₁ x)) x
  rewrite makeTrue₂-✓₁ v x
  rewrite x⇔x (not (makeTrue₂ v x []))
  = refl
makeTrue₂-✓₁ v (xor₁ x y)
  rewrite sym (xor-pat-✓ (makeTrue₂ v (xor₁ x y) [ false ]) (makeTrue₂ v (xor₁ x y) [ true ])
    (makeTrue₂ v (xor₁ x y) []))
  rewrite evalCons false [] v (makeTrue₂ v (xor₁ x y)) x
  rewrite evalCons true [] v (makeTrue₂ v (xor₁ x y)) y
  rewrite makeTrue₂-✓₁ v x
  rewrite makeTrue₂-✓₁ v y
  rewrite x⇔x (makeTrue₂ v x [] xor makeTrue₂ v y [])
  = refl

makeTrue₂-✓₂ : ∀ v f → makeTrue₂ v f [] ≡ eval₁ v f
makeTrue₂-✓₂ v (var₁ x)   = refl
makeTrue₂-✓₂ v (and₁ x y) rewrite makeTrue₂-✓₂ v x | makeTrue₂-✓₂ v y = refl
makeTrue₂-✓₂ v (or₁ x y)  rewrite makeTrue₂-✓₂ v x | makeTrue₂-✓₂ v y = refl
makeTrue₂-✓₂ v (not₁ x)   rewrite makeTrue₂-✓₂ v x = refl
makeTrue₂-✓₂ v (xor₁ x y) rewrite makeTrue₂-✓₂ v x | makeTrue₂-✓₂ v y = refl

transform₂ : Formula₁ → Formula₂ 0
transform₂ f = and₂ (tmp₂ []) (flatten [] f)

transform₂-✓ : ∀ v f → eval₂ v (makeTrue₂ v f) (transform₂ f) ≡ eval₁ v f
transform₂-✓ v f
  rewrite makeTrue₂-✓₁ v f
  rewrite makeTrue₂-✓₂ v f
  = ∧-identityʳ (eval₁ v f)

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
  bin→ℕ : ℕ → (f : Formula₁) → ℕ × (List Bool → ℕ)

  module ⟨bin→ℕ⟩ where
    aux₁ : ℕ → (x : Formula₁) → ℕ × (List Bool → ℕ)
    aux₁ n x =
      let n′ , m = bin→ℕ n x in
      suc n′ , λ where
        []      → n′
        (_ ∷ a) → m a

    aux₂ : ℕ → (x y : Formula₁) → ℕ × (List Bool → ℕ)
    aux₂ n x y =
      let nˡ , mˡ = bin→ℕ n x in
      let nʳ , mʳ = bin→ℕ nˡ y in
      suc nʳ , λ where
        []          → nʳ
        (false ∷ a) → mˡ a
        (true ∷ a)  → mʳ a

  open ⟨bin→ℕ⟩

  bin→ℕ n (var₁ x)   = suc n , λ _ → n
  bin→ℕ n (and₁ x y) = aux₂ n x y
  bin→ℕ n (or₁ x y)  = aux₂ n x y
  bin→ℕ n (not₁ x)   = aux₁ n x
  bin→ℕ n (xor₁ x y) = aux₂ n x y

module _ where
  ℕ→bin : ℕ → (f : Formula₁) → ℕ × (ℕ → List Bool)

  module ⟨ℕ→bin⟩ where
    aux₁ : ℕ → (x : Formula₁) → ℕ × (ℕ → List Bool)
    aux₁ n x =
      let n′ , m = ℕ→bin n x in
      suc n′ , λ a →
        case a ≟ⁿ n′ of λ where
          (yes _) → []
          (no  _) → false ∷ m a

    aux₂ : ℕ → (x y : Formula₁) → ℕ × (ℕ → List Bool)
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

  ℕ→bin n (var₁ x)   = suc n , λ _ → []
  ℕ→bin n (and₁ x y) = aux₂ n x y
  ℕ→bin n (or₁ x y)  = aux₂ n x y
  ℕ→bin n (not₁ x)   = aux₁ n x
  ℕ→bin n (xor₁ x y) = aux₂ n x y

module _ where
  n<fw₁ : ∀ n f → n < proj₁ (bin→ℕ n f)

  module ⟨n<fw₁⟩ where
    aux₁ : ∀ n x → n < suc (proj₁ (bin→ℕ n x))
    aux₁ n x = <-trans (n<fw₁ n x) ≤-refl

    aux₂ : ∀ n x y → n < suc (proj₁ (bin→ℕ (proj₁ (bin→ℕ n x)) y))
    aux₂ n x y = <-trans (n<fw₁ n x) (<-trans (n<fw₁ (proj₁ (bin→ℕ n x)) y) ≤-refl)

  open ⟨n<fw₁⟩

  n<fw₁ n (var₁ x)   = ≤-refl
  n<fw₁ n (and₁ x y) = aux₂ n x y
  n<fw₁ n (or₁ x y)  = aux₂ n x y
  n<fw₁ n (not₁ x)   = aux₁ n x
  n<fw₁ n (xor₁ x y) = aux₂ n x y

fw₁<fw₁fw₁ : ∀ n x y → proj₁ (bin→ℕ n x) < proj₁ (bin→ℕ (proj₁ (bin→ℕ n x)) y)
fw₁<fw₁fw₁ n x y = n<fw₁ (proj₁ (bin→ℕ n x)) y

n<fw₁fw₁ : ∀ n x y → n < proj₁ (bin→ℕ (proj₁ (bin→ℕ n x)) y)
n<fw₁fw₁ n x y = <-trans (n<fw₁ n x) (fw₁<fw₁fw₁ n x y)

n≤fw₂ : ∀ n f a → n ≤ proj₂ (bin→ℕ n f) a
n≤fw₂ n (var₁ x)   a            = ≤-refl
n≤fw₂ n (and₁ x y) []           = <⇒≤ (n<fw₁fw₁ n x y)
n≤fw₂ n (and₁ x y) (false ∷ as) = n≤fw₂ n x as
n≤fw₂ n (and₁ x y) (true ∷ as)  = <⇒≤ (<-transˡ (n<fw₁ n x) (n≤fw₂ (proj₁ (bin→ℕ n x)) y as))
n≤fw₂ n (or₁ x y) []            = <⇒≤ (n<fw₁fw₁ n x y)
n≤fw₂ n (or₁ x y) (false ∷ as)  = n≤fw₂ n x as
n≤fw₂ n (or₁ x y) (true ∷ as)   = <⇒≤ (<-transˡ (n<fw₁ n x) (n≤fw₂ (proj₁ (bin→ℕ n x)) y as))
n≤fw₂ n (not₁ x) []             = <⇒≤ (n<fw₁ n x)
n≤fw₂ n (not₁ x) (a ∷ as)       = n≤fw₂ n x as
n≤fw₂ n (xor₁ x y) []           = <⇒≤ (n<fw₁fw₁ n x y)
n≤fw₂ n (xor₁ x y) (false ∷ as) = n≤fw₂ n x as
n≤fw₂ n (xor₁ x y) (true ∷ as)  = <⇒≤ (<-transˡ (n<fw₁ n x) (n≤fw₂ (proj₁ (bin→ℕ n x)) y as))

fw₁≤fw₂fw₁ : ∀ n x y a → proj₁ (bin→ℕ n x) ≤ proj₂ (bin→ℕ (proj₁ (bin→ℕ n x)) y) a
fw₁≤fw₂fw₁ n x y a = n≤fw₂ (proj₁ (bin→ℕ n x)) y a

fw₂<fw₁ : ∀ n f a → proj₂ (bin→ℕ n f) a < proj₁ (bin→ℕ n f)
fw₂<fw₁ n (var₁ x)   a            = ≤-refl
fw₂<fw₁ n (and₁ x y) []           = ≤-refl
fw₂<fw₁ n (and₁ x y) (false ∷ as) = <-trans (fw₂<fw₁ n x as ) (<-trans (fw₁<fw₁fw₁ n x y) ≤-refl)
fw₂<fw₁ n (and₁ x y) (true ∷ as)  = <-trans (fw₂<fw₁ (proj₁ (bin→ℕ n x)) y as) ≤-refl
fw₂<fw₁ n (or₁ x y)  []           = ≤-refl
fw₂<fw₁ n (or₁ x y)  (false ∷ as) = <-trans (fw₂<fw₁ n x as ) (<-trans (fw₁<fw₁fw₁ n x y) ≤-refl)
fw₂<fw₁ n (or₁ x y)  (true ∷ as)  = <-trans (fw₂<fw₁ (proj₁ (bin→ℕ n x)) y as) ≤-refl
fw₂<fw₁ n (not₁ x)   []           = ≤-refl
fw₂<fw₁ n (not₁ x)   (a ∷ as)     = <-trans (fw₂<fw₁ n x as) ≤-refl
fw₂<fw₁ n (xor₁ x y) []           = ≤-refl
fw₂<fw₁ n (xor₁ x y) (false ∷ as) = <-trans (fw₂<fw₁ n x as ) (<-trans (fw₁<fw₁fw₁ n x y) ≤-refl)
fw₂<fw₁ n (xor₁ x y) (true ∷ as)  = <-trans (fw₂<fw₁ (proj₁ (bin→ℕ n x)) y as) ≤-refl

fw₂fw₁<fw₁fw₁ : ∀ n x y a →
  proj₂ (bin→ℕ (proj₁ (bin→ℕ n x)) y) a < proj₁ (bin→ℕ (proj₁ (bin→ℕ n x)) y)
fw₂fw₁<fw₁fw₁ n x y a = fw₂<fw₁ (proj₁ (bin→ℕ n x)) y a

fw₁≡bw₁ : ∀ n f → proj₁ (bin→ℕ n f) ≡ proj₁ (ℕ→bin n f)
fw₁≡bw₁ n (var₁ x) = refl
fw₁≡bw₁ n (and₁ x y)
  rewrite fw₁≡bw₁ n x
  rewrite fw₁≡bw₁ (proj₁ (ℕ→bin n x)) y
  = refl
fw₁≡bw₁ n (or₁ x y)
  rewrite fw₁≡bw₁ n x
  rewrite fw₁≡bw₁ (proj₁ (ℕ→bin n x)) y
  = refl
fw₁≡bw₁ n (not₁ x) = cong suc (fw₁≡bw₁ n x)
fw₁≡bw₁ n (xor₁ x y)
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
  (makeTrue₂ v f ∘ proj₂ (ℕ→bin n f)) (proj₂ (bin→ℕ n f) a) ≡ makeTrue₂ v f a
roundtrip n v (var₁ x)   a = refl
roundtrip n v (and₁ x y) []
  rewrite (≮⇒<? ∘ <⇒≯) (bw₁<fw₁fw₁ n x y)
  rewrite ≮⇒<? (<-irrefl (fw₁fw₁≡bw₁bw₁ n x y))
  = refl
roundtrip n v (and₁ x y) (false ∷ as)
  rewrite <⇒<? (fw₂<bw₁ n x as)
  = roundtrip n v x as
roundtrip n v (and₁ x y) (true ∷ as)
  rewrite (≮⇒<? ∘ ≤⇒≯) (bw₁≤fw₂fw₁ n x y as)
  rewrite <⇒<? (fw₂fw₁<bw₁bw₁ n x y as)
  rewrite sym (fw₁≡bw₁ n x)
  = roundtrip (proj₁ (bin→ℕ n x)) v y as
roundtrip n v (or₁ x y) []
  rewrite (≮⇒<? ∘ <⇒≯) (bw₁<fw₁fw₁ n x y)
  rewrite ≮⇒<? (<-irrefl (fw₁fw₁≡bw₁bw₁ n x y))
  = refl
roundtrip n v (or₁ x y) (false ∷ as)
  rewrite <⇒<? (fw₂<bw₁ n x as)
  = roundtrip n v x as
roundtrip n v (or₁ x y) (true ∷ as)
  rewrite (≮⇒<? ∘ ≤⇒≯) (bw₁≤fw₂fw₁ n x y as)
  rewrite <⇒<? (fw₂fw₁<bw₁bw₁ n x y as)
  rewrite sym (fw₁≡bw₁ n x)
  = roundtrip (proj₁ (bin→ℕ n x)) v y as
roundtrip n v (not₁ x)   []
  rewrite ≡⇒≟ⁿ (fw₁≡bw₁ n x)
  = refl
roundtrip n v (not₁ x)   (a ∷ as)
  rewrite (≢⇒≟ⁿ ∘ <⇒≢) (fw₂<bw₁ n x as)
  = roundtrip n v x as
roundtrip n v (xor₁ x y) []
  rewrite (≮⇒<? ∘ <⇒≯) (bw₁<fw₁fw₁ n x y)
  rewrite ≮⇒<? (<-irrefl (fw₁fw₁≡bw₁bw₁ n x y))
  = refl
roundtrip n v (xor₁ x y) (false ∷ as)
  rewrite <⇒<? (fw₂<bw₁ n x as)
  = roundtrip n v x as
roundtrip n v (xor₁ x y) (true ∷ as)
  rewrite (≮⇒<? ∘ ≤⇒≯) (bw₁≤fw₂fw₁ n x y as)
  rewrite <⇒<? (fw₂fw₁<bw₁bw₁ n x y as)
  rewrite sym (fw₁≡bw₁ n x)
  = roundtrip (proj₁ (bin→ℕ n x)) v y as

remap₂ : {l : ℕ} → (List Bool → ℕ) → Formula₂ l → Formula₃ l
remap₂ r (var₂ x)   = var₃ x
remap₂ r (tmp₂ x)   = tmp₃ (r x)
remap₂ r (and₂ x y) = and₃ (remap₂ r x) (remap₂ r y)
remap₂ r (or₂ x y)  = or₃ (remap₂ r x) (remap₂ r y)
remap₂ r (not₂ x)   = not₃ (remap₂ r x)

evalRemap₂ : ∀ n v t r f → eval₃ v t (remap₂ r (flatten n f)) ≡ eval₂ v (t ∘ r) (flatten n f)
evalRemap₂ n v t r (var₁ x)   = refl
evalRemap₂ n v t r (and₁ x y)
  rewrite sym (evalRemap₂ (n ++ [ false ]) v t r x)
  rewrite sym (evalRemap₂ (n ++ [ true ]) v t r y)
  = refl
evalRemap₂ n v t r (or₁ x y)
  rewrite sym (evalRemap₂ (n ++ [ false ]) v t r x)
  rewrite sym (evalRemap₂ (n ++ [ true ]) v t r y)
  = refl
evalRemap₂ n v t r (not₁ x)
  rewrite sym (evalRemap₂ (n ++ [ false ]) v t r x)
  = refl
evalRemap₂ n v t r (xor₁ x y)
  rewrite sym (evalRemap₂ (n ++ [ false ]) v t r x)
  rewrite sym (evalRemap₂ (n ++ [ true ]) v t r y)
  = refl

assign-≡ : ∀ {l t₁ t₂} v → (f : Formula₂ l) → (∀ a → t₁ a ≡ t₂ a) → eval₂ v t₁ f ≡ eval₂ v t₂ f
assign-≡ {t₁} {t₂} v (var₂ x)   p = refl
assign-≡ {t₁} {t₂} v (tmp₂ x)   p = p x
assign-≡ {t₁} {t₂} v (and₂ x y) p = cong₂ _∧_ (assign-≡ v x p) (assign-≡ v y p)
assign-≡ {t₁} {t₂} v (or₂ x y)  p = cong₂ _∨_ (assign-≡ v x p) (assign-≡ v y p)
assign-≡ {t₁} {t₂} v (not₂ x)   p = cong not (assign-≡ v x p)

makeTrue₃ : (ℕ → Bool) → Formula₁ → (ℕ → Bool)
makeTrue₃ v f = makeTrue₂ v f ∘ proj₂ (ℕ→bin 0 f)

transform₃ : Formula₁ → Formula₃ 0
transform₃ f = remap₂ (proj₂ (bin→ℕ 0 f)) (transform₂ f)

transform₃-✓ : ∀ v f → eval₃ v (makeTrue₃ v f) (transform₃ f) ≡ eval₁ v f
transform₃-✓ v f
  rewrite roundtrip 0 v f []
  rewrite evalRemap₂ [] v (makeTrue₂ v f ∘ proj₂ (ℕ→bin 0 f)) (proj₂ (bin→ℕ 0 f)) f
  rewrite assign-≡ v (flatten [] f) (roundtrip 0 v f)
  rewrite sym (transform₂-✓ v f)
  = refl

nextVar : {l : ℕ} → Formula₃ l → ℕ
nextVar (var₃ x)   = suc x
nextVar (tmp₃ x)   = 0
nextVar (and₃ x y) = nextVar x ⊔ nextVar y
nextVar (or₃ x y)  = nextVar x ⊔ nextVar y
nextVar (not₃ x)   = nextVar x

merge : ℕ → (ℕ → Bool) → (ℕ → Bool) → (ℕ → Bool)
merge b v t a =
  case a <?ⁿ b of λ where
    (yes _) → v a
    (no  _) → t (a ∸ b)

remap₃ : {l : ℕ} → ℕ → Formula₃ l → Formula₄ l
remap₃ b (var₃ x)   = var₄ x
remap₃ b (tmp₃ x)   = var₄ (b + x)
remap₃ b (and₃ x y) = and₄ (remap₃ b x) (remap₃ b y)
remap₃ b (or₃ x y)  = or₄ (remap₃ b x) (remap₃ b y)
remap₃ b (not₃ x)   = not₄ (remap₃ b x)

mergeRemap : ∀ {b l} v t f → nextVar f ≤ b → eval₄ (merge b v t) (remap₃ {l} b f) ≡ eval₃ v t f
mergeRemap {b} v t (var₃ x)   p
  rewrite <⇒<? p
  = refl
mergeRemap {b} v t (tmp₃ x)   p
  rewrite (≮⇒<? ∘ ≤⇒≯) (m≤m+n b x)
  rewrite m+n∸m≡n b x
  = refl
mergeRemap {b} v t (and₃ x y) p
  rewrite mergeRemap v t x (m⊔n≤o⇒m≤o (nextVar x) (nextVar y) p)
  rewrite mergeRemap v t y (m⊔n≤o⇒n≤o (nextVar x) (nextVar y) p)
  = refl
mergeRemap {b} v t (or₃ x y)  p
  rewrite mergeRemap v t x (m⊔n≤o⇒m≤o (nextVar x) (nextVar y) p)
  rewrite mergeRemap v t y (m⊔n≤o⇒n≤o (nextVar x) (nextVar y) p)
  = refl
mergeRemap {b} v t (not₃ x)   p
  rewrite mergeRemap v t x p
  = refl

makeTrue₄ : (ℕ → Bool) → Formula₁ → (ℕ → Bool)
makeTrue₄ v f = merge (nextVar (transform₃ f)) v (makeTrue₃ v f)

transform₄ : Formula₁ → Formula₄ 0
-- XXX - more efficient than "let"?
transform₄ f = (λ f₃ → remap₃ (nextVar f₃) f₃) (transform₃ f)

transform₄-✓ : ∀ v f → eval₄ (makeTrue₄ v f) (transform₄ f) ≡ eval₁ v f
transform₄-✓ v f
  rewrite mergeRemap v (makeTrue₃ v f) (transform₃ f) ≤-refl
  rewrite sym (transform₃-✓ v f)
  = refl

to-∷-∨ : {l : ℕ} → (f : Formula₄ (suc l)) → List V.Literal
to-∷-∨ (var₄ x)        = [ V.pos x ]
to-∷-∨ (not₄ (var₄ x)) = [ V.neg x ]
to-∷-∨ (or₄ x y)       = to-∷-∨ x ++ to-∷-∨ y

to-∷-∧ : (f : Formula₄ 0) → List V.Clause
to-∷-∧ (and₄ {zero}  {zero} x y)  = to-∷-∧ x ++ to-∷-∧ y
to-∷-∧ (and₄ {zero}  {suc n} x y) = to-∷-∧ x ++ [ to-∷-∨ y ]
to-∷-∧ (and₄ {suc m} {zero} x y)  = [ to-∷-∨ x ] ++ to-∷-∧ y
to-∷-∧ (and₄ {suc m} {suc n} x y) = [ to-∷-∨ x ] ++ [ to-∷-∨ y ]

++⇒∧ : ∀ v x y → eval₅ v (x ++ y) ≡ eval₅ v x ∧ eval₅ v y
++⇒∧ v []       y = refl
++⇒∧ v (x ∷ xs) y
  rewrite ++⇒∧ v xs y
  = sym (∧-assoc (V.evalᶜ v x) (eval₅ v xs) (eval₅ v y))

to-∷-∨-✓ : ∀ {l} v f → eval₅ v [ to-∷-∨ {l} f ] ≡ eval₄ v f
to-∷-∨-✓ v (var₄ x)        = trans (∧-identityʳ (v x ∨ false)) (∨-identityʳ (v x))
to-∷-∨-✓ v (not₄ (var₄ x)) = trans (∧-identityʳ ((not (v x)) ∨ false)) (∨-identityʳ (not (v x)))
to-∷-∨-✓ v (or₄ x y)
  rewrite V.++⇒∨ v (to-∷-∨ x) (to-∷-∨ y)
  rewrite sym (to-∷-∨-✓ v x)
  rewrite sym (to-∷-∨-✓ v y)
  = ∧-distribʳ-∨ true (V.evalᶜ v (to-∷-∨ x)) (V.evalᶜ v (to-∷-∨ y))

to-∷-∧-✓ : ∀ v f → eval₅ v (to-∷-∧ f) ≡ eval₄ v f
to-∷-∧-✓ v (and₄ {zero}  {zero}  x y)
  rewrite ++⇒∧ v (to-∷-∧ x) (to-∷-∧ y)
  rewrite to-∷-∧-✓ v x
  rewrite to-∷-∧-✓ v y
  = refl
to-∷-∧-✓ v (and₄ {zero}  {suc n} x y)
  rewrite ++⇒∧ v (to-∷-∧ x) [ to-∷-∨ y ]
  rewrite to-∷-∧-✓ v x
  rewrite to-∷-∨-✓ v y
  = refl
to-∷-∧-✓ v (and₄ {suc m} {zero}  x y)
  rewrite ++⇒∧ v [ to-∷-∨ x ] (to-∷-∧ y)
  rewrite to-∷-∨-✓ v x
  rewrite to-∷-∧-✓ v y
  = refl
to-∷-∧-✓ v (and₄ {suc m} {suc n} x y)
  rewrite sym (to-∷-∨-✓ v x)
  rewrite sym (to-∷-∨-✓ v y)
  rewrite ∧-identityʳ (V.evalᶜ v (to-∷-∨ x))
  = refl

transform₅ : Formula₁ → Formula₅
transform₅ f = to-∷-∧ (transform₄ f)

transform₅-✓ : ∀ v f → eval₅ (makeTrue₄ v f) (transform₅ f) ≡ eval₁ v f
transform₅-✓ v f
 rewrite to-∷-∧-✓ (makeTrue₄ v f) (transform₄ f)
 rewrite sym (transform₄-✓ v f)
 = refl

unsat₅-✓ : ∀ f → (∀ v → eval₅ v (transform₅ f) ≡ false) → (∀ v → eval₁ v f ≡ false)
unsat₅-✓ f p v = sym (trans (sym (p (makeTrue₄ v f))) (transform₅-✓ v f))

transform₆ : Formula₁ → Maybe Formula₆
transform₆ f = P.from-∷ (transform₅ f)

transform₆-✓ : ∀ v f₁ f₆ → transform₆ f₁ ≡ just f₆ → eval₆ (makeTrue₄ v f₁) f₆ ≡ eval₁ v f₁
transform₆-✓ v f₁ f₆ p
  rewrite P.from-∷-✓ (makeTrue₄ v f₁) (transform₅ f₁) f₆ p
  rewrite sym (transform₅-✓ v f₁)
  = refl

unsat₆-✓ : ∀ f₁ f₆ → transform₆ f₁ ≡ just f₆ → (∀ v → eval₆ v f₆ ≡ false) →
  (∀ v → eval₁ v f₁ ≡ false)
unsat₆-✓ f₁ f₆ p₁ p₂ v = sym (trans (sym (p₂ (makeTrue₄ v f₁))) (transform₆-✓ v f₁ f₆ p₁))
