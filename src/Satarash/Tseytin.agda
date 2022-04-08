module Satarash.Tseytin where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; _xor_ ; if_then_else_ ; _≟_)
open import Data.Bool.Properties
  using (∧-identityʳ ; ∧-idem ; ∨-identityʳ ; ∧-assoc ; ∧-distribʳ-∨ ; ∧-comm ; ∨-comm)
open import Data.Empty using (⊥)
open import Data.List using (List ; _∷_ ; [] ; [_] ; _++_ ; length)
open import Data.List.Relation.Binary.Equality.DecPropositional (_≟_) using (_≡?_)
open import Data.Maybe using (Maybe ; nothing ; just ; _>>=_ ; map)
open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s ; _<_ ; _≮_ ; _+_ ; _∸_ ; _⊔_)
  renaming (_≟_ to _≟ⁿ_ ; _<?_ to _<?ⁿ_)
open import Data.Nat.Properties using (
    ≤-refl ; <-irrefl ; <-asym ; <-trans ; <-transˡ ; n<1+n ; m≤m+n ; m⊔n≤o⇒m≤o ; m⊔n≤o⇒n≤o ;
    <⇒≢ ; <⇒≯ ; <⇒≤ ; ≤⇒≯ ; <-irrelevant ; module ≤-Reasoning ;
    m+n∸m≡n
  )
open import Data.Nat.Show using () renaming (show to showⁿ)
open import Data.Product using (∃-syntax ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_ ; case_of_ ; flip ; _$_)
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

show₀ : Formula₀ → String
show₀ (con₀ true)  = "(con true)"
show₀ (con₀ false) = "(con false)"
show₀ (var₀ x)     = "(var " ++ˢ showⁿ x ++ˢ ")"
show₀ (and₀ x y)   = "(and " ++ˢ show₀ x ++ˢ " " ++ˢ show₀ y ++ˢ ")"
show₀ (or₀ x y)    = "(or " ++ˢ show₀ x ++ˢ " " ++ˢ show₀ y ++ˢ ")"
show₀ (not₀ x)     = "(not " ++ˢ show₀ x ++ˢ ")"
show₀ (xor₀ x y)   = "(xor " ++ˢ show₀ x ++ˢ " " ++ˢ show₀ y ++ˢ ")"
show₀ (iff₀ x y)   = "(iff " ++ˢ show₀ x ++ˢ " " ++ˢ show₀ y ++ˢ ")"
show₀ (imp₀ x y)   = "(imp " ++ˢ show₀ x ++ˢ " " ++ˢ show₀ y ++ˢ ")"
show₀ (ite₀ x y z) = "(ite " ++ˢ show₀ x ++ˢ " " ++ˢ show₀ y ++ˢ show₀ z ++ˢ ")"

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

-- fewer operations
data Formula₁ : Set where
  con₁ : Bool → Formula₁
  var₁ : ℕ → Formula₁
  and₁ : Formula₁ → Formula₁ → Formula₁
  or₁  : Formula₁ → Formula₁ → Formula₁
  not₁ : Formula₁ → Formula₁
  xor₁ : Formula₁ → Formula₁ → Formula₁

eval₁ : (ℕ → Bool) → Formula₁ → Bool
eval₁ v (con₁ x)   = x
eval₁ v (var₁ x)   = v x
eval₁ v (and₁ x y) = eval₁ v x ∧ eval₁ v y
eval₁ v (or₁ x y)  = eval₁ v x ∨ eval₁ v y
eval₁ v (not₁ x)   = not (eval₁ v x)
eval₁ v (xor₁ x y) = eval₁ v x xor eval₁ v y

-- folded constants
data Formula₂ : Set where
  var₂ : ℕ → Formula₂
  and₂ : Formula₂ → Formula₂ → Formula₂
  or₂  : Formula₂ → Formula₂ → Formula₂
  not₂ : Formula₂ → Formula₂
  xor₂ : Formula₂ → Formula₂ → Formula₂

eval₂ : (ℕ → Bool) → Formula₂ → Bool
eval₂ v (var₂ x)   = v x
eval₂ v (and₂ x y) = eval₂ v x ∧ eval₂ v y
eval₂ v (or₂ x y)  = eval₂ v x ∨ eval₂ v y
eval₂ v (not₂ x)   = not (eval₂ v x)
eval₂ v (xor₂ x y) = eval₂ v x xor eval₂ v y

-- structural constraints, temporaries with binary identifiers, CNF patterns
data Formula₃ : ℕ → Set where
  var₃ : ℕ → Formula₃ 3
  tmp₃ : List Bool → Formula₃ 3
  and₃ : {m n : ℕ} → Formula₃ m → Formula₃ n → Formula₃ 0
  or₃  : {m n : ℕ} → Formula₃ (suc m) → Formula₃ (suc n) → Formula₃ 1
  not₃ : Formula₃ 3 → Formula₃ 2

eval₃ : {l : ℕ} → (ℕ → Bool) → (List Bool → Bool) → Formula₃ l → Bool
eval₃ v t (var₃ x)   = v x
eval₃ v t (tmp₃ x)   = t x
eval₃ v t (and₃ x y) = eval₃ v t x ∧ eval₃ v t y
eval₃ v t (or₃ x y)  = eval₃ v t x ∨ eval₃ v t y
eval₃ v t (not₃ x)   = not (eval₃ v t x)

-- temporaries with ℕ identifiers
data Formula₄ : ℕ → Set where
  var₄ : ℕ → Formula₄ 3
  tmp₄ : ℕ → Formula₄ 3
  and₄ : {m n : ℕ} → Formula₄ m → Formula₄ n → Formula₄ 0
  or₄  : {m n : ℕ} → Formula₄ (suc m) → Formula₄ (suc n) → Formula₄ 1
  not₄ : Formula₄ 3 → Formula₄ 2

eval₄ : {l : ℕ} → (ℕ → Bool) → (ℕ → Bool) → Formula₄ l → Bool
eval₄ v t (var₄ x)   = v x
eval₄ v t (tmp₄ x)   = t x
eval₄ v t (and₄ x y) = eval₄ v t x ∧ eval₄ v t y
eval₄ v t (or₄ x y)  = eval₄ v t x ∨ eval₄ v t y
eval₄ v t (not₄ x)   = not (eval₄ v t x)

-- temporaries turned into variables
data Formula₅ : ℕ → Set where
  var₅ : ℕ → Formula₅ 3
  and₅ : {m n : ℕ} → Formula₅ m → Formula₅ n → Formula₅ 0
  or₅  : {m n : ℕ} → Formula₅ (suc m) → Formula₅ (suc n) → Formula₅ 1
  not₅ : Formula₅ 3 → Formula₅ 2

eval₅ : {l : ℕ} → (ℕ → Bool) → Formula₅ l → Bool
eval₅ v (var₅ x)   = v x
eval₅ v (and₅ x y) = eval₅ v x ∧ eval₅ v y
eval₅ v (or₅ x y)  = eval₅ v x ∨ eval₅ v y
eval₅ v (not₅ x)   = not (eval₅ v x)

-- list of clauses
Formula₆ : Set
Formula₆ = List V.Clause

eval₆ : (ℕ → Bool) → Formula₆ → Bool
eval₆ = P.eval-∷

-- verifier's representation
Formula₇ : Set
Formula₇ = V.Formula

eval₇ : (ℕ → Bool) → Formula₇ → Bool
eval₇ = V.eval

transform₁ : Formula₀ → Formula₁
transform₁ (con₀ x)     = con₁ x
transform₁ (var₀ x)     = var₁ x
transform₁ (and₀ x y)   = and₁ (transform₁ x) (transform₁ y)
transform₁ (or₀ x y)    = or₁ (transform₁ x) (transform₁ y)
transform₁ (not₀ x)     = not₁ (transform₁ x)
transform₁ (xor₀ x y)   = xor₁ (transform₁ x) (transform₁ y)
transform₁ (iff₀ x y)   = not₁ (xor₁ (transform₁ x) (transform₁ y))
transform₁ (imp₀ x y)   = or₁ (not₁ (transform₁ x)) (transform₁ y)
transform₁ (ite₀ x y z) =
  let x₁ = transform₁ x in
  or₁ (and₁ x₁ (transform₁ y)) (and₁ (not₁ x₁) (transform₁ z))

transform₁-✓ : ∀ v f → eval₁ v (transform₁ f) ≡ eval₀ v f
transform₁-✓ v (con₀ x)     = refl
transform₁-✓ v (var₀ x)     = refl
transform₁-✓ v (and₀ x y)   = cong₂ _∧_ (transform₁-✓ v x) (transform₁-✓ v y)
transform₁-✓ v (or₀ x y)    = cong₂ _∨_ (transform₁-✓ v x) (transform₁-✓ v y)
transform₁-✓ v (not₀ x)     = cong not (transform₁-✓ v x)
transform₁-✓ v (xor₀ x y)   = cong₂ _xor_ (transform₁-✓ v x) (transform₁-✓ v y)
transform₁-✓ v (iff₀ x y)
  rewrite transform₁-✓ v x
  rewrite transform₁-✓ v y
  with eval₀ v x | eval₀ v y
...  | false     | false     = refl
...  | false     | true      = refl
...  | true      | false     = refl
...  | true      | true      = refl
transform₁-✓ v (imp₀ x y)
  rewrite transform₁-✓ v x
  rewrite transform₁-✓ v y
  with eval₀ v x | eval₀ v y
...  | false     | false     = refl
...  | false     | true      = refl
...  | true      | false     = refl
...  | true      | true      = refl
transform₁-✓ v (ite₀ x y z)
  rewrite transform₁-✓ v x
  rewrite transform₁-✓ v y
  rewrite transform₁-✓ v z
  with eval₀ v x
...  | false = refl
...  | true  = ∨-identityʳ (eval₀ v y)

data ConOrNot : Set where
  isCon : Bool → ConOrNot
  isNot : ConOrNot

conOrNot : Formula₁ → ConOrNot
conOrNot (con₁ x) = isCon x
conOrNot _        = isNot

conOrNot-✓ : ∀ v {f b} → conOrNot f ≡ isCon b → eval₁ v f ≡ b
conOrNot-✓ v {con₁ .b} {b} refl = refl

record FoldRules₁ : Set where
  field
    rule₁ : Formula₁
    rule₂ : Formula₁

foldRules-not : FoldRules₁
foldRules-not = record {
    rule₁ = con₁ false ;
    rule₂ = con₁ true
  }

record FoldRules₂ : Set where
  field
    rule₁ : (bˣ bʸ : Bool) → Formula₁
    rule₂ : (y′ : Formula₁) → Formula₁
    rule₃ : (y′ : Formula₁) → Formula₁
    rule₄ : (x′ : Formula₁) → Formula₁
    rule₅ : (x′ : Formula₁) → Formula₁

foldRules-∧ : FoldRules₂
foldRules-∧ = record {
    rule₁ = λ bˣ bʸ → con₁ (bˣ ∧ bʸ) ;
    rule₂ = λ y′ → y′ ;
    rule₃ = λ y′ → con₁ false ;
    rule₄ = λ x′ → x′  ;
    rule₅ = λ x′ → con₁ false
  }

foldRules-∨ : FoldRules₂
foldRules-∨ = record {
    rule₁ = λ bˣ bʸ → con₁ (bˣ ∨ bʸ) ;
    rule₂ = λ y′ → con₁ true ;
    rule₃ = λ y′ → y′ ;
    rule₄ = λ x′ → con₁ true ;
    rule₅ = λ x′ → x′
  }

foldRules-xor : FoldRules₂
foldRules-xor = record {
    rule₁ = λ bˣ bʸ → con₁ (bˣ xor bʸ) ;
    rule₂ = λ y′ → not₁ y′ ;
    rule₃ = λ y′ → y′ ;
    rule₄ = λ x′ → not₁ x′ ;
    rule₅ = λ x′ → x′
  }

foldConst : Formula₁ → Formula₁
foldConst₁ : (Formula₁ → Formula₁) → Formula₁ → FoldRules₁ → Formula₁
foldConst₂ : (Formula₁ → Formula₁ → Formula₁) → Formula₁ → Formula₁ → FoldRules₂ → Formula₁

foldConst₁ c x r =
  let x′ = foldConst x in
  case conOrNot x′ of λ where
    (isCon true)  → rule₁ r
    (isCon false) → rule₂ r
    isNot         → c x′
  where open FoldRules₁

foldConst₂ c x y r =
  let x′ = foldConst x in
  let y′ = foldConst y in
  case conOrNot x′ , conOrNot y′ of λ where
    (isCon bˣ    , isCon bʸ)    → rule₁ r bˣ bʸ
    (isCon true  , isNot)       → rule₂ r y′
    (isCon false , isNot)       → rule₃ r y′
    (isNot       , isCon true)  → rule₄ r x′
    (isNot       , isCon false) → rule₅ r x′
    (isNot       , isNot)       → c x′ y′
  where open FoldRules₂

foldConst (con₁ x)   = con₁ x
foldConst (var₁ x)   = var₁ x
foldConst (and₁ x y) = foldConst₂ and₁ x y foldRules-∧
foldConst (or₁ x y)  = foldConst₂ or₁ x y foldRules-∨
foldConst (not₁ x)   = foldConst₁ not₁ x foldRules-not
foldConst (xor₁ x y) = foldConst₂ xor₁ x y foldRules-xor

foldConst-✓ : ∀ v f → eval₁ v (foldConst f) ≡ eval₁ v f

foldConst₁-not-✓ : ∀ v x → eval₁ v (foldConst₁ not₁ x foldRules-not) ≡ eval₁ v (not₁ x)
foldConst₁-not-✓ v x
  with conOrNot (foldConst x) in eq
...  | isCon true  = cong not (trans (sym (conOrNot-✓ v eq)) (foldConst-✓ v x))
...  | isCon false = cong not (trans (sym (conOrNot-✓ v eq)) (foldConst-✓ v x))
...  | isNot       = cong not (foldConst-✓ v x)

foldConst₂-∧-✓ : ∀ v x y → eval₁ v (foldConst₂ and₁ x y foldRules-∧) ≡ eval₁ v (and₁ x y)
foldConst₂-∧-✓ v x y
  with conOrNot (foldConst x) in eqˣ | conOrNot (foldConst y) in eqʸ
...  | isCon bˣ                      | isCon bʸ                      =
  let pˣ = trans (sym (conOrNot-✓ v eqˣ)) (foldConst-✓ v x) in
  let pʸ = trans (sym (conOrNot-✓ v eqʸ)) (foldConst-✓ v y) in
  cong₂ _∧_ pˣ pʸ
...  | isCon true                    | isNot                         =
  let pˣ = trans (sym (conOrNot-✓ v eqˣ)) (foldConst-✓ v x) in
  cong₂ _∧_ pˣ (foldConst-✓ v y)
...  | isCon false                   | isNot                         =
  let pˣ = trans (sym (conOrNot-✓ v eqˣ)) (foldConst-✓ v x) in
  cong₂ _∧_ pˣ (foldConst-✓ v y)
...  | isNot                         | isCon true                    =
  flip trans (∧-comm (eval₁ v y) (eval₁ v x)) $
  let pʸ = trans (sym (conOrNot-✓ v eqʸ)) (foldConst-✓ v y) in
  cong₂ _∧_ pʸ (foldConst-✓ v x)
...  | isNot                         | isCon false                   =
  flip trans (∧-comm (eval₁ v y) (eval₁ v x)) $
  let pʸ = trans (sym (conOrNot-✓ v eqʸ)) (foldConst-✓ v y) in
  cong₂ _∧_ pʸ (foldConst-✓ v x)
...  | isNot                         | isNot                         =
  cong₂ _∧_ (foldConst-✓ v x) (foldConst-✓ v y)

foldConst₂-∨-✓ : ∀ v x y → eval₁ v (foldConst₂ or₁ x y foldRules-∨) ≡ eval₁ v (or₁ x y)
foldConst₂-∨-✓ v x y
  with conOrNot (foldConst x) in eqˣ | conOrNot (foldConst y) in eqʸ
...  | isCon bˣ                      | isCon bʸ                      =
  let pˣ = trans (sym (conOrNot-✓ v eqˣ)) (foldConst-✓ v x) in
  let pʸ = trans (sym (conOrNot-✓ v eqʸ)) (foldConst-✓ v y) in
  cong₂ _∨_ pˣ pʸ
...  | isCon true                    | isNot                         =
  let pˣ = trans (sym (conOrNot-✓ v eqˣ)) (foldConst-✓ v x) in
  cong₂ _∨_ pˣ (foldConst-✓ v y)
...  | isCon false                   | isNot                         =
  let pˣ = trans (sym (conOrNot-✓ v eqˣ)) (foldConst-✓ v x) in
  cong₂ _∨_ pˣ (foldConst-✓ v y)
...  | isNot                         | isCon true                    =
  flip trans (∨-comm (eval₁ v y) (eval₁ v x)) $
  let pʸ = trans (sym (conOrNot-✓ v eqʸ)) (foldConst-✓ v y) in
  cong₂ _∨_ pʸ (foldConst-✓ v x)
...  | isNot                         | isCon false                   =
  flip trans (∨-comm (eval₁ v y) (eval₁ v x)) $
  let pʸ = trans (sym (conOrNot-✓ v eqʸ)) (foldConst-✓ v y) in
  cong₂ _∨_ pʸ (foldConst-✓ v x)
...  | isNot                         | isNot                         =
  cong₂ _∨_ (foldConst-✓ v x) (foldConst-✓ v y)

xor-comm : ∀ x y → x xor y ≡ y xor x
xor-comm false false = refl
xor-comm false true  = refl
xor-comm true  false = refl
xor-comm true  true  = refl

foldConst₂-xor-✓ : ∀ v x y → eval₁ v (foldConst₂ xor₁ x y foldRules-xor) ≡ eval₁ v (xor₁ x y)
foldConst₂-xor-✓ v x y
  with conOrNot (foldConst x) in eqˣ | conOrNot (foldConst y) in eqʸ
...  | isCon bˣ                      | isCon bʸ                      =
  let pˣ = trans (sym (conOrNot-✓ v eqˣ)) (foldConst-✓ v x) in
  let pʸ = trans (sym (conOrNot-✓ v eqʸ)) (foldConst-✓ v y) in
  cong₂ _xor_ pˣ pʸ
...  | isCon true                    | isNot                         =
  let pˣ = trans (sym (conOrNot-✓ v eqˣ)) (foldConst-✓ v x) in
  cong₂ _xor_ pˣ (foldConst-✓ v y)
...  | isCon false                   | isNot                         =
  let pˣ = trans (sym (conOrNot-✓ v eqˣ)) (foldConst-✓ v x) in
  cong₂ _xor_ pˣ (foldConst-✓ v y)
...  | isNot                         | isCon true                    =
  flip trans (xor-comm (eval₁ v y) (eval₁ v x)) $
  let pʸ = trans (sym (conOrNot-✓ v eqʸ)) (foldConst-✓ v y) in
  cong₂ _xor_ pʸ (foldConst-✓ v x)
...  | isNot                         | isCon false                   =
  flip trans (xor-comm (eval₁ v y) (eval₁ v x)) $
  let pʸ = trans (sym (conOrNot-✓ v eqʸ)) (foldConst-✓ v y) in
  cong₂ _xor_ pʸ (foldConst-✓ v x)
...  | isNot                         | isNot                         =
  cong₂ _xor_ (foldConst-✓ v x) (foldConst-✓ v y)

foldConst-✓ v (con₁ x)   = refl
foldConst-✓ v (var₁ x)   = refl
foldConst-✓ v (and₁ x y) = foldConst₂-∧-✓ v x y
foldConst-✓ v (or₁ x y)  = foldConst₂-∨-✓ v x y
foldConst-✓ v (not₁ x)   = foldConst₁-not-✓ v x
foldConst-✓ v (xor₁ x y) = foldConst₂-xor-✓ v x y

remConst : Formula₁ → Formula₂
remConst (con₁ true)  = or₂ (var₂ 0) (not₂ (var₂ 0))
remConst (con₁ false) = and₂ (var₂ 0) (not₂ (var₂ 0))
remConst (var₁ x)     = var₂ x
remConst (and₁ x y)   = and₂ (remConst x) (remConst y)
remConst (or₁ x y)    = or₂ (remConst x) (remConst y)
remConst (not₁ x)     = not₂ (remConst x)
remConst (xor₁ x y)   = xor₂ (remConst x) (remConst y)

remConst-✓ : ∀ v f → eval₂ v (remConst f) ≡ eval₁ v f
remConst-✓ v (con₁ true)
  with v 0
...  | true  = refl
...  | false = refl
remConst-✓ v (con₁ false)
  with v 0
...  | true  = refl
...  | false = refl
remConst-✓ v (var₁ x)     = refl
remConst-✓ v (and₁ x y)   = cong₂ _∧_ (remConst-✓ v x) (remConst-✓ v y)
remConst-✓ v (or₁ x y)    = cong₂ _∨_ (remConst-✓ v x) (remConst-✓ v y)
remConst-✓ v (not₁ x)     = cong not (remConst-✓ v x)
remConst-✓ v (xor₁ x y)   = cong₂ _xor_ (remConst-✓ v x) (remConst-✓ v y)

transform₂ : Formula₀ → Formula₂
transform₂ = remConst ∘ foldConst ∘ transform₁

transform₂-✓ : ∀ v f → eval₂ v (transform₂ f) ≡ eval₀ v f
transform₂-✓ v f =
  begin
    eval₂ v (transform₂ f)                        ≡⟨⟩
    eval₂ v (remConst (foldConst (transform₁ f))) ≡⟨ remConst-✓ v (foldConst (transform₁ f)) ⟩
    eval₁ v (foldConst (transform₁ f))            ≡⟨ foldConst-✓ v (transform₁ f) ⟩
    eval₁ v (transform₁ f)                        ≡⟨ transform₁-✓ v f ⟩
    eval₀ v f                                     ∎
  where open ≡-Reasoning

x⇔x : ∀ x → (x ⇔ x) ≡ true
x⇔x false = refl
x⇔x true  = refl

x⇔t≡x : ∀ x → (x ⇔ true) ≡ x
x⇔t≡x false = refl
x⇔t≡x true  = refl

x⇔f≡¬x : ∀ x → (x ⇔ false) ≡ not x
x⇔f≡¬x false = refl
x⇔f≡¬x true  = refl

var-pat : (x r : Formula₃ 3) → Formula₃ 0
var-pat x r = and₃ (or₃ x (not₃ r)) (or₃ (not₃ x) r)

var-pat-✓ : ∀ x r → (r ⇔ x) ≡ (x ∨ not r) ∧ (not x ∨ r)
var-pat-✓ false r = trans (x⇔f≡¬x r) (sym (∧-identityʳ (not r)))
var-pat-✓ true  r = x⇔t≡x r

∧-pat : (x y r : Formula₃ 3) → Formula₃ 0
∧-pat x y r = and₃ (or₃ (not₃ x) (or₃ (not₃ y) r)) (and₃ (or₃ x (not₃ r)) (or₃ y (not₃ r)))

∧-pat-✓ : ∀ x y r → (r ⇔ x ∧ y) ≡ (not x ∨ not y ∨ r) ∧ (x ∨ not r) ∧ (y ∨ not r)
∧-pat-✓ false false r = trans (x⇔f≡¬x r) (sym (∧-idem (not r)))
∧-pat-✓ false true  r = trans (x⇔f≡¬x r) (sym (∧-identityʳ (not r)))
∧-pat-✓ true false  r = x⇔f≡¬x r
∧-pat-✓ true true   r = trans (x⇔t≡x r) (sym (∧-identityʳ r))

∨-pat : (x y r : Formula₃ 3) → Formula₃ 0
∨-pat x y r = and₃ (or₃ x (or₃ y (not₃ r))) (and₃ (or₃ (not₃ x) r) (or₃ (not₃ y) r))

∨-pat-✓ : ∀ x y r → (r ⇔ x ∨ y) ≡ (x ∨ y ∨ not r) ∧ (not x ∨ r) ∧ (not y ∨ r)
∨-pat-✓ false false r = trans (x⇔f≡¬x r) (sym (∧-identityʳ (not r)))
∨-pat-✓ false true  r = x⇔t≡x r
∨-pat-✓ true  false r = trans (x⇔t≡x r) (sym (∧-identityʳ r))
∨-pat-✓ true  true  r = trans (x⇔t≡x r) (sym (∧-idem r))

not-pat : (x r : Formula₃ 3) → Formula₃ 0
not-pat x r = and₃ (or₃ (not₃ x) (not₃ r)) (or₃ x r)

not-pat-✓ : ∀ x r → (r ⇔ not x) ≡ (not x ∨ not r) ∧ (x ∨ r)
not-pat-✓ false r = x⇔t≡x r
not-pat-✓ true  r = trans (x⇔f≡¬x r) (sym (∧-identityʳ (not r)))

xor-pat : (x y r : Formula₃ 3) → Formula₃ 0
xor-pat x y r =
  and₃ (or₃ (not₃ x) (or₃ (not₃ y) (not₃ r)))
  (and₃ (or₃ x (or₃ y (not₃ r)))
  (and₃ (or₃ x (or₃ (not₃ y) r))
  (or₃ (not₃ x) (or₃ y r))))

xor-pat-✓ : ∀ x y r →
  (r ⇔ x xor y) ≡ (not x ∨ not y ∨ not r) ∧ (x ∨ y ∨ not r) ∧ (x ∨ not y ∨ r) ∧ (not x ∨ y ∨ r)
xor-pat-✓ false false r = trans (x⇔f≡¬x r) (sym (∧-identityʳ (not r)))
xor-pat-✓ false true  r = trans (x⇔t≡x r) (sym (∧-identityʳ r))
xor-pat-✓ true  false r = x⇔t≡x r
xor-pat-✓ true  true  r = trans (x⇔f≡¬x r) (sym (∧-identityʳ (not r)))

⇔-pat : (x y r : Formula₃ 3) → Formula₃ 0
⇔-pat x y r =
  and₃ (or₃ x (or₃ y r))
  (and₃ (or₃ (not₃ x) (or₃ (not₃ y) r))
  (and₃ (or₃ (not₃ x) (or₃ y (not₃ r)))
  (or₃ x (or₃ (not₃ y) (not₃ r)))))

⇔-pat-✓ : ∀ x y r →
  (r ⇔ (x ⇔ y)) ≡ (x ∨ y ∨ r) ∧ (not x ∨ not y ∨ r) ∧ (not x ∨ y ∨ not r) ∧ (x ∨ not y ∨ not r)
⇔-pat-✓ false false r = trans (x⇔t≡x r) (sym (∧-identityʳ r))
⇔-pat-✓ false true  r = x⇔f≡¬x r
⇔-pat-✓ true  false r = trans (x⇔f≡¬x r) (sym (∧-identityʳ (not r)))
⇔-pat-✓ true  true  r = trans (x⇔t≡x r) (sym (∧-identityʳ r))

module _ where
  flatten : List Bool → Formula₂ → Formula₃ 0

  private
    aux₀ : List Bool → ℕ → Formula₃ 0
    aux₀ n x = var-pat (tmp₃ n) (var₃ x)

    aux₁ : List Bool → (Formula₃ 3 → Formula₃ 3 → Formula₃ 0) → Formula₂ → Formula₃ 0
    aux₁ n p x =
      let s = flatten (n ++ [ false ]) x in
      and₃ (p (tmp₃ (n ++ [ false ])) (tmp₃ n)) s

    aux₂ : List Bool → (Formula₃ 3 → Formula₃ 3 → Formula₃ 3 → Formula₃ 0) → Formula₂ → Formula₂ →
      Formula₃ 0
    aux₂ n p x y =
      let sˡ = flatten (n ++ [ false ]) x in
      let sʳ = flatten (n ++ [ true ]) y in
      (and₃ (and₃ (p (tmp₃ (n ++ [ false ])) (tmp₃ (n ++ [ true ])) (tmp₃ n)) sˡ) sʳ)

  flatten n (var₂ x)   = aux₀ n x
  flatten n (and₂ x y) = aux₂ n ∧-pat x y
  flatten n (or₂ x y)  = aux₂ n ∨-pat x y
  flatten n (not₂ x)   = aux₁ n not-pat x
  flatten n (xor₂ x y) = aux₂ n xor-pat x y

module _ where
  makeTrue₃ : (ℕ → Bool) → Formula₂ → (List Bool → Bool)

  module ⟨makeTrue₃⟩ where
    aux₁ : (ℕ → Bool) → (Bool → Bool) → Formula₂ → (List Bool → Bool)
    aux₁ v op x =
      let t′ = makeTrue₃ v x in
        λ where
          []      → op (t′ [])
          (_ ∷ n) → t′ n

    aux₂ : (ℕ → Bool) → (Bool → Bool → Bool) → Formula₂ → Formula₂ → (List Bool → Bool)
    aux₂ v op x y =
      let tˡ = makeTrue₃ v x in
      let tʳ = makeTrue₃ v y in
        λ where
          []          → op (tˡ []) (tʳ [])
          (false ∷ n) → tˡ n
          (true ∷ n)  → tʳ n

  open ⟨makeTrue₃⟩

  makeTrue₃ v (var₂ x)   = λ _ → v x
  makeTrue₃ v (and₂ x y) = aux₂ v _∧_ x y
  makeTrue₃ v (or₂ x y)  = aux₂ v _∨_ x y
  makeTrue₃ v (not₂ x)   = aux₁ v not x
  makeTrue₃ v (xor₂ x y) = aux₂ v _xor_ x y

evalCons : ∀ m n v t f → eval₃ v t (flatten (m ∷ n) f) ≡ eval₃ v (t ∘ (m ∷_)) (flatten n f)
evalCons m n v t (var₂ x) = refl
evalCons m n v t (and₂ x y)
  rewrite sym (evalCons m (n ++ [ false ]) v t x)
  rewrite sym (evalCons m (n ++ [ true ]) v t y)
  = refl
evalCons m n v t (or₂ x y)
  rewrite sym (evalCons m (n ++ [ false ]) v t x)
  rewrite sym (evalCons m (n ++ [ true ]) v t y)
  = refl
evalCons m n v t (not₂ x)
  rewrite sym (evalCons m (n ++ [ false ]) v t x)
  = refl
evalCons m n v t (xor₂ x y)
  rewrite sym (evalCons m (n ++ [ false ]) v t x)
  rewrite sym (evalCons m (n ++ [ true ]) v t y)
  = refl

module _ where
  makeTrue₃-✓₁ : ∀ v f → eval₃ v (makeTrue₃ v f) (flatten [] f) ≡ true

  private
    aux₁ : ∀ v op x →
      (op (makeTrue₃ v x []) ⇔ op (makeTrue₃ v x [])) ∧
      eval₃ v (⟨makeTrue₃⟩.aux₁ v op x) (flatten [ false ] x) ≡ true
    aux₁ v op x
      rewrite x⇔x (op (makeTrue₃ v x []))
      rewrite evalCons false [] v (⟨makeTrue₃⟩.aux₁ v op x) x
      rewrite makeTrue₃-✓₁ v x
      = refl

    aux₂ : ∀ v op x y →
      ((op (makeTrue₃ v x []) (makeTrue₃ v y []) ⇔ op (makeTrue₃ v x []) (makeTrue₃ v y [])) ∧
      eval₃ v (⟨makeTrue₃⟩.aux₂ v op x y) (flatten [ false ] x)) ∧
      eval₃ v (⟨makeTrue₃⟩.aux₂ v op x y) (flatten [ true ] y) ≡ true
    aux₂ v op x y
      rewrite x⇔x (op (makeTrue₃ v x []) (makeTrue₃ v y []))
      rewrite evalCons false [] v (⟨makeTrue₃⟩.aux₂ v op x y) x
      rewrite evalCons true [] v (⟨makeTrue₃⟩.aux₂ v op x y) y
      rewrite makeTrue₃-✓₁ v x
      rewrite makeTrue₃-✓₁ v y
      = refl

  makeTrue₃-✓₁ v (var₂ x)
    rewrite sym (var-pat-✓ (v x) (v x))
    = x⇔x (v x)
  makeTrue₃-✓₁ v (and₂ x y)
    rewrite sym (∧-pat-✓ (makeTrue₃ v (and₂ x y) [ false ]) (makeTrue₃ v (and₂ x y) [ true ])
      (makeTrue₃ v (and₂ x y) []))
    = aux₂ v _∧_ x y
  makeTrue₃-✓₁ v (or₂ x y)
    rewrite sym (∨-pat-✓ (makeTrue₃ v (or₂ x y) [ false ]) (makeTrue₃ v (or₂ x y) [ true ])
      (makeTrue₃ v (or₂ x y) []))
    = aux₂ v _∨_ x y
  makeTrue₃-✓₁ v (not₂ x)
    rewrite sym (not-pat-✓ (makeTrue₃ v (not₂ x) [ false ]) (makeTrue₃ v (not₂ x) []))
    = aux₁ v not x
  makeTrue₃-✓₁ v (xor₂ x y)
    rewrite sym (xor-pat-✓ (makeTrue₃ v (xor₂ x y) [ false ]) (makeTrue₃ v (xor₂ x y) [ true ])
      (makeTrue₃ v (xor₂ x y) []))
    = aux₂ v _xor_ x y

makeTrue₃-✓₂ : ∀ v f → makeTrue₃ v f [] ≡ eval₂ v f
makeTrue₃-✓₂ v (var₂ x)   = refl
makeTrue₃-✓₂ v (and₂ x y) rewrite makeTrue₃-✓₂ v x | makeTrue₃-✓₂ v y = refl
makeTrue₃-✓₂ v (or₂ x y)  rewrite makeTrue₃-✓₂ v x | makeTrue₃-✓₂ v y = refl
makeTrue₃-✓₂ v (not₂ x)   rewrite makeTrue₃-✓₂ v x = refl
makeTrue₃-✓₂ v (xor₂ x y) rewrite makeTrue₃-✓₂ v x | makeTrue₃-✓₂ v y = refl

transform₃ : Formula₀ → Formula₃ 0
transform₃ f = and₃ (tmp₃ []) (flatten [] (transform₂ f))

transform₃-✓ : ∀ v f → eval₃ v (makeTrue₃ v (transform₂ f)) (transform₃ f) ≡ eval₀ v f
transform₃-✓ v f
  rewrite makeTrue₃-✓₁ v (transform₂ f)
  rewrite makeTrue₃-✓₂ v (transform₂ f)
  rewrite transform₂-✓ v f
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
  bin→ℕ : ℕ → (f : Formula₂) → ℕ × (List Bool → ℕ)

  module ⟨bin→ℕ⟩ where
    aux₁ : ℕ → (x : Formula₂) → ℕ × (List Bool → ℕ)
    aux₁ n x =
      let n′ , m = bin→ℕ n x in
      suc n′ , λ where
        []      → n′
        (_ ∷ a) → m a

    aux₂ : ℕ → (x y : Formula₂) → ℕ × (List Bool → ℕ)
    aux₂ n x y =
      let nˡ , mˡ = bin→ℕ n x in
      let nʳ , mʳ = bin→ℕ (suc nˡ) y in
      nʳ , λ where
        []          → nˡ
        (false ∷ a) → mˡ a
        (true ∷ a)  → mʳ a

  open ⟨bin→ℕ⟩

  bin→ℕ n (var₂ x)   = suc n , λ _ → n
  bin→ℕ n (and₂ x y) = aux₂ n x y
  bin→ℕ n (or₂ x y)  = aux₂ n x y
  bin→ℕ n (not₂ x)   = aux₁ n x
  bin→ℕ n (xor₂ x y) = aux₂ n x y

module _ where
  ℕ→bin : ℕ → (f : Formula₂) → ℕ × (ℕ → List Bool)

  module ⟨ℕ→bin⟩ where
    aux₁ : ℕ → (x : Formula₂) → ℕ × (ℕ → List Bool)
    aux₁ n x =
      let n′ , m = ℕ→bin n x in
      suc n′ , λ a →
        case a ≟ⁿ n′ of λ where
          (yes _) → []
          (no  _) → false ∷ m a

    aux₂ : ℕ → (x y : Formula₂) → ℕ × (ℕ → List Bool)
    aux₂ n x y =
      let nˡ , mˡ = ℕ→bin n x in
      let nʳ , mʳ = ℕ→bin (suc nˡ) y in
      nʳ , λ a →
        case a <?ⁿ nˡ of λ where
          (yes _) → false ∷ mˡ a
          (no  _) →
            case nˡ <?ⁿ a of λ where
              (yes _) → true ∷ mʳ a
              (no  _) → []

  open ⟨ℕ→bin⟩

  ℕ→bin n (var₂ x)   = suc n , λ _ → []
  ℕ→bin n (and₂ x y) = aux₂ n x y
  ℕ→bin n (or₂ x y)  = aux₂ n x y
  ℕ→bin n (not₂ x)   = aux₁ n x
  ℕ→bin n (xor₂ x y) = aux₂ n x y

<-≡ : ∀ {x y z} → x < y → y ≡ z → x < z
<-≡ p refl = p

≮-≡ : ∀ {x y z} → x ≮ y → y ≡ z → x ≮ z
≮-≡ p refl = p

≡-< : ∀ {x y z} → x ≡ y → y < z → x < z
≡-< refl p = p

module _ where
  roundtrip : ∀ n v f a → (makeTrue₃ v f ∘ proj₂ (ℕ→bin n f) ∘ proj₂ (bin→ℕ n f)) a ≡ makeTrue₃ v f a

  private
    module _ where
      p₁≡p₁ : ∀ n f → proj₁ (ℕ→bin n f) ≡ proj₁ (bin→ℕ n f)

      private
        aux₂ : ∀ n x y →
          proj₁ (ℕ→bin (suc (proj₁ (ℕ→bin n x))) y) ≡ proj₁ (bin→ℕ (suc (proj₁ (bin→ℕ n x))) y)
        aux₂ n x y rewrite p₁≡p₁ n x | p₁≡p₁ (suc (proj₁ (bin→ℕ n x))) y = refl

      p₁≡p₁ n (var₂ x)   = refl
      p₁≡p₁ n (and₂ x y) = aux₂ n x y
      p₁≡p₁ n (or₂ x y)  = aux₂ n x y
      p₁≡p₁ n (not₂ x)   = cong suc (p₁≡p₁ n x)
      p₁≡p₁ n (xor₂ x y) = aux₂ n x y

    module _ where
      n<p₁ : ∀ n f → n < proj₁ (bin→ℕ n f)

      private
        aux₁ : ∀ n x → n < proj₁ (⟨bin→ℕ⟩.aux₁ n x)
        aux₁ n x = <-trans (n<p₁ n x) (n<1+n (proj₁ (bin→ℕ n x)))

        aux₂ : ∀ n x y → n < proj₁ (⟨bin→ℕ⟩.aux₂ n x y)
        aux₂ n x y =
          begin-strict
            n                                         <⟨ n<p₁ n x ⟩
            proj₁ (bin→ℕ n x)                         <⟨ n<1+n (proj₁ (bin→ℕ n x)) ⟩
            suc (proj₁ (bin→ℕ n x))                   <⟨ n<p₁ (suc (proj₁ (bin→ℕ n x))) y ⟩
            proj₁ (bin→ℕ (suc (proj₁ (bin→ℕ n x))) y) ∎
          where open ≤-Reasoning

      n<p₁ n (var₂ x)   = n<1+n n
      n<p₁ n (and₂ x y) = aux₂ n x y
      n<p₁ n (or₂ x y)  = aux₂ n x y
      n<p₁ n (not₂ x)   = aux₁ n x
      n<p₁ n (xor₂ x y) = aux₂ n x y

    module _ where
      n≤p₂ : ∀ n f a → n ≤ proj₂ (bin→ℕ n f) a

      private
        aux₁ : ∀ n x a → n ≤ proj₂ (⟨bin→ℕ⟩.aux₁ n x) a
        aux₁ n x []      = <⇒≤ (n<p₁ n x)
        aux₁ n x (_ ∷ a) = n≤p₂ n x a

        aux₂ : ∀ n x y a → n ≤ proj₂ (⟨bin→ℕ⟩.aux₂ n x y) a
        aux₂ n x y []          = <⇒≤ (n<p₁ n x)
        aux₂ n x y (false ∷ a) = n≤p₂ n x a
        aux₂ n x y (true  ∷ a) =
          begin
            n                                           <⟨ n<p₁ n x ⟩
            proj₁ (bin→ℕ n x)                           <⟨ n<1+n (proj₁ (bin→ℕ n x)) ⟩
            suc (proj₁ (bin→ℕ n x))                     ≤⟨ n≤p₂ (suc (proj₁ (bin→ℕ n x))) y a ⟩
            proj₂ (bin→ℕ (suc (proj₁ (bin→ℕ n x))) y) a ∎
          where open ≤-Reasoning

      n≤p₂ n (var₂ x)   a = ≤-refl
      n≤p₂ n (and₂ x y) a = aux₂ n x y a
      n≤p₂ n (or₂ x y)  a = aux₂ n x y a
      n≤p₂ n (not₂ x)   a = aux₁ n x a
      n≤p₂ n (xor₂ x y) a = aux₂ n x y a

    module _ where
      p₂<p₁ : ∀ n f a → proj₂ (bin→ℕ n f) a < proj₁ (bin→ℕ n f)

      private
        aux₁ : ∀ n x a → proj₂ (⟨bin→ℕ⟩.aux₁ n x) a < proj₁ (⟨bin→ℕ⟩.aux₁ n x)
        aux₁ n x []      = n<1+n (proj₁ (bin→ℕ n x))
        aux₁ n x (_ ∷ a) = <-trans (p₂<p₁ n x a) (n<1+n (proj₁ (bin→ℕ n x)))

        aux₂ : ∀ n x y a → proj₂ (⟨bin→ℕ⟩.aux₂ n x y) a < proj₁ (⟨bin→ℕ⟩.aux₂ n x y)
        aux₂ n x y [] =
          begin-strict
            proj₁ (bin→ℕ n x)                         <⟨ n<1+n (proj₁ (bin→ℕ n x)) ⟩
            suc (proj₁ (bin→ℕ n x))                   <⟨ n<p₁ (suc (proj₁ (bin→ℕ n x))) y ⟩
            proj₁ (bin→ℕ (suc (proj₁ (bin→ℕ n x))) y) ∎
          where open ≤-Reasoning
        aux₂ n x y (false ∷ a) =
          begin-strict
            proj₂ (bin→ℕ n x) a                       <⟨ p₂<p₁ n x a ⟩
            proj₁ (bin→ℕ n x)                         <⟨ n<1+n (proj₁ (bin→ℕ n x)) ⟩
            suc (proj₁ (bin→ℕ n x))                   <⟨ n<p₁ (suc (proj₁ (bin→ℕ n x))) y ⟩
            proj₁ (bin→ℕ (suc (proj₁ (bin→ℕ n x))) y) ∎
          where open ≤-Reasoning
        aux₂ n x y (true  ∷ a) = p₂<p₁ (suc (proj₁ (bin→ℕ n x))) y a

      p₂<p₁ n (var₂ x)   a = n<1+n n
      p₂<p₁ n (and₂ x y) a = aux₂ n x y a
      p₂<p₁ n (or₂ x y)  a = aux₂ n x y a
      p₂<p₁ n (not₂ x)   a = aux₁ n x a
      p₂<p₁ n (xor₂ x y) a = aux₂ n x y a

    aux₁ : ∀ n v op x a →
      (⟨makeTrue₃⟩.aux₁ v op x ∘ proj₂ (⟨ℕ→bin⟩.aux₁ n x) ∘
        proj₂ (⟨bin→ℕ⟩.aux₁ n x)) a ≡ ⟨makeTrue₃⟩.aux₁ v op x a
    aux₁ n v op x []      with proj₁ (bin→ℕ n x) ≟ⁿ proj₁ (ℕ→bin n x)
    aux₁ n v op x []         | yes _ = refl
    aux₁ n v op x []         | no ¬p = contradiction (sym (p₁≡p₁ n x)) ¬p
    aux₁ n v op x (_ ∷ a) with proj₂ (bin→ℕ n x) a ≟ⁿ proj₁ (ℕ→bin n x)
    aux₁ n v op x (_ ∷ a)    | yes p = contradiction p ¬p
      where
      ¬p : proj₂ (bin→ℕ n x) a ≢ proj₁ (ℕ→bin n x)
      ¬p = <⇒≢ (<-≡ (p₂<p₁ n x a) (sym (p₁≡p₁ n x)))
    aux₁ n v op x (_ ∷ a)    | no _  = roundtrip n v x a

    aux₂ : ∀ n v op x y a →
      (⟨makeTrue₃⟩.aux₂ v op x y ∘ proj₂ (⟨ℕ→bin⟩.aux₂ n x y) ∘
        proj₂ (⟨bin→ℕ⟩.aux₂ n x y)) a ≡ ⟨makeTrue₃⟩.aux₂ v op x y a
    aux₂ n v op x y []          with proj₁ (bin→ℕ n x) <?ⁿ proj₁ (ℕ→bin n x)
    aux₂ n v op x y []             | yes p = contradiction p (<-irrefl (sym (p₁≡p₁ n x)))
    aux₂ n v op x y []             | no _  with proj₁ (ℕ→bin n x) <?ⁿ proj₁ (bin→ℕ n x)
    aux₂ n v op x y []             | no _     | yes p = contradiction p (<-irrefl (p₁≡p₁ n x))
    aux₂ n v op x y []             | no _     | no ¬p = refl
    aux₂ n v op x y (false ∷ a) with proj₂ (bin→ℕ n x) a <?ⁿ proj₁ (ℕ→bin n x)
    aux₂ n v op x y (false ∷ a)    | yes _ = roundtrip n v x a
    aux₂ n v op x y (false ∷ a)    | no ¬p = contradiction p ¬p
      where
      p : proj₂ (bin→ℕ n x) a < proj₁ (ℕ→bin n x)
      p = <-≡ (p₂<p₁ n x a) (sym (p₁≡p₁ n x))
    aux₂ n v op x y (true ∷ a)  with proj₂ (bin→ℕ (suc (proj₁ (bin→ℕ n x))) y) a <?ⁿ proj₁ (bin→ℕ n x)
    aux₂ n v op x y (true ∷ a)     | yes p = contradiction p ¬p
      where
      ¬p : proj₂ (bin→ℕ (suc (proj₁ (bin→ℕ n x))) y) a ≮ proj₁ (bin→ℕ n x)
      ¬p = <-asym (n≤p₂ (suc (proj₁ (bin→ℕ n x))) y a)
    aux₂ n v op x y (true ∷ a)     | no ¬p₁ with proj₂ (bin→ℕ (suc (proj₁ (bin→ℕ n x))) y) a <?ⁿ proj₁ (ℕ→bin n x)
    aux₂ n v op x y (true ∷ a)     | no ¬p₁     | yes p₂ = flip contradiction (≮-≡ ¬p₁ (sym (p₁≡p₁ n x))) p₂
    aux₂ n v op x y (true ∷ a)     | no ¬p₁     | no ¬p₂ with proj₁ (ℕ→bin n x) <?ⁿ proj₂ (bin→ℕ (suc (proj₁ (bin→ℕ n x))) y) a
    aux₂ n v op x y (true ∷ a)     | no ¬p₁     | no ¬p₂    | yes p₃ rewrite sym (p₁≡p₁ n x) = roundtrip (suc (proj₁ (ℕ→bin n x))) v y a
    aux₂ n v op x y (true ∷ a)     | no ¬p₁     | no ¬p₂    | no ¬p₃ = contradiction p₃ ¬p₃
      where
      p₃ : proj₁ (ℕ→bin n x) < proj₂ (bin→ℕ (suc (proj₁ (bin→ℕ n x))) y) a
      p₃ = ≡-< (p₁≡p₁ n x) (n≤p₂ (suc (proj₁ (bin→ℕ n x))) y a)

  roundtrip n v (var₂ x)   a = refl
  roundtrip n v (and₂ x y) a = aux₂ n v _∧_ x y a
  roundtrip n v (or₂ x y)  a = aux₂ n v _∨_ x y a
  roundtrip n v (not₂ x)   a = aux₁ n v not x a
  roundtrip n v (xor₂ x y) a = aux₂ n v _xor_ x y a

remap₃ : {l : ℕ} → (List Bool → ℕ) → Formula₃ l → Formula₄ l
remap₃ r (var₃ x)   = var₄ x
remap₃ r (tmp₃ x)   = tmp₄ (r x)
remap₃ r (and₃ x y) = and₄ (remap₃ r x) (remap₃ r y)
remap₃ r (or₃ x y)  = or₄ (remap₃ r x) (remap₃ r y)
remap₃ r (not₃ x)   = not₄ (remap₃ r x)

evalRemap₃ : ∀ n v t r f → eval₄ v t (remap₃ r (flatten n f)) ≡ eval₃ v (t ∘ r) (flatten n f)
evalRemap₃ n v t r (var₂ x)   = refl
evalRemap₃ n v t r (and₂ x y)
  rewrite sym (evalRemap₃ (n ++ [ false ]) v t r x)
  rewrite sym (evalRemap₃ (n ++ [ true ]) v t r y)
  = refl
evalRemap₃ n v t r (or₂ x y)
  rewrite sym (evalRemap₃ (n ++ [ false ]) v t r x)
  rewrite sym (evalRemap₃ (n ++ [ true ]) v t r y)
  = refl
evalRemap₃ n v t r (not₂ x)
  rewrite sym (evalRemap₃ (n ++ [ false ]) v t r x)
  = refl
evalRemap₃ n v t r (xor₂ x y)
  rewrite sym (evalRemap₃ (n ++ [ false ]) v t r x)
  rewrite sym (evalRemap₃ (n ++ [ true ]) v t r y)
  = refl

assign-≡ : ∀ {l t₁ t₂} v → (f : Formula₃ l) → (∀ a → t₁ a ≡ t₂ a) → eval₃ v t₁ f ≡ eval₃ v t₂ f
assign-≡ {t₁} {t₂} v (var₃ x)   p = refl
assign-≡ {t₁} {t₂} v (tmp₃ x)   p = p x
assign-≡ {t₁} {t₂} v (and₃ x y) p = cong₂ _∧_ (assign-≡ v x p) (assign-≡ v y p)
assign-≡ {t₁} {t₂} v (or₃ x y)  p = cong₂ _∨_ (assign-≡ v x p) (assign-≡ v y p)
assign-≡ {t₁} {t₂} v (not₃ x)   p = cong not (assign-≡ v x p)

makeTrue₄ : (ℕ → Bool) → Formula₀ → (ℕ → Bool)
makeTrue₄ v f = makeTrue₃ v (transform₂ f) ∘ proj₂ (ℕ→bin 0 (transform₂ f))

transform₄ : Formula₀ → Formula₄ 0
transform₄ f = remap₃ (proj₂ (bin→ℕ 0 (transform₂ f))) (transform₃ f)

transform₄-✓ : ∀ v f → eval₄ v (makeTrue₄ v f) (transform₄ f) ≡ eval₀ v f
transform₄-✓ v f
  with t₃-✓ ← transform₃-✓ v f
  with f₂ ← transform₂ f
  rewrite roundtrip 0 v f₂ []
  rewrite evalRemap₃ [] v (makeTrue₃ v f₂ ∘ proj₂ (ℕ→bin 0 f₂)) (proj₂ (bin→ℕ 0 f₂)) f₂
  rewrite assign-≡ v (flatten [] f₂) (roundtrip 0 v f₂)
  = t₃-✓

nextVar : {l : ℕ} → Formula₄ l → ℕ
nextVar (var₄ x)   = suc x
nextVar (tmp₄ x)   = 0
nextVar (and₄ x y) = nextVar x ⊔ nextVar y
nextVar (or₄ x y)  = nextVar x ⊔ nextVar y
nextVar (not₄ x)   = nextVar x

merge : ℕ → (ℕ → Bool) → (ℕ → Bool) → (ℕ → Bool)
merge b v t a =
  case a <?ⁿ b of λ where
    (yes _) → v a
    (no  _) → t (a ∸ b)

remap₄ : {l : ℕ} → ℕ → Formula₄ l → Formula₅ l
remap₄ b (var₄ x)   = var₅ x
remap₄ b (tmp₄ x)   = var₅ (b + x)
remap₄ b (and₄ x y) = and₅ (remap₄ b x) (remap₄ b y)
remap₄ b (or₄ x y)  = or₅ (remap₄ b x) (remap₄ b y)
remap₄ b (not₄ x)   = not₅ (remap₄ b x)

mergeRemap : ∀ {b l} v t f → nextVar f ≤ b → eval₅ (merge b v t) (remap₄ {l} b f) ≡ eval₄ v t f
mergeRemap {b} v t (var₄ x)   p
  rewrite <⇒<? p
  = refl
mergeRemap {b} v t (tmp₄ x)   p
  rewrite (≮⇒<? ∘ ≤⇒≯) (m≤m+n b x)
  rewrite m+n∸m≡n b x
  = refl
mergeRemap {b} v t (and₄ x y) p
  rewrite mergeRemap v t x (m⊔n≤o⇒m≤o (nextVar x) (nextVar y) p)
  rewrite mergeRemap v t y (m⊔n≤o⇒n≤o (nextVar x) (nextVar y) p)
  = refl
mergeRemap {b} v t (or₄ x y)  p
  rewrite mergeRemap v t x (m⊔n≤o⇒m≤o (nextVar x) (nextVar y) p)
  rewrite mergeRemap v t y (m⊔n≤o⇒n≤o (nextVar x) (nextVar y) p)
  = refl
mergeRemap {b} v t (not₄ x)   p
  rewrite mergeRemap v t x p
  = refl

makeTrue₅ : (ℕ → Bool) → Formula₀ → (ℕ → Bool)
makeTrue₅ v f = merge (nextVar (transform₄ f)) v (makeTrue₄ v f)

transform₅ : Formula₀ → Formula₅ 0
transform₅ f = (λ f₄ → remap₄ (nextVar f₄) f₄) (transform₄ f)

transform₅-✓ : ∀ v f → eval₅ (makeTrue₅ v f) (transform₅ f) ≡ eval₀ v f
transform₅-✓ v f
  rewrite mergeRemap v (makeTrue₄ v f) (transform₄ f) ≤-refl
  rewrite sym (transform₄-✓ v f)
  = refl

to-∷-∨ : {l : ℕ} → (f : Formula₅ (suc l)) → List V.Literal
to-∷-∨ (var₅ x)        = [ V.pos x ]
to-∷-∨ (not₅ (var₅ x)) = [ V.neg x ]
to-∷-∨ (or₅ x y)       = to-∷-∨ x ++ to-∷-∨ y

to-∷-∧ : (f : Formula₅ 0) → List V.Clause
to-∷-∧ (and₅ {zero}  {zero} x y)  = to-∷-∧ x ++ to-∷-∧ y
to-∷-∧ (and₅ {zero}  {suc n} x y) = to-∷-∧ x ++ [ to-∷-∨ y ]
to-∷-∧ (and₅ {suc m} {zero} x y)  = [ to-∷-∨ x ] ++ to-∷-∧ y
to-∷-∧ (and₅ {suc m} {suc n} x y) = [ to-∷-∨ x ] ++ [ to-∷-∨ y ]

++⇒∧ : ∀ v x y → eval₆ v (x ++ y) ≡ eval₆ v x ∧ eval₆ v y
++⇒∧ v []       y = refl
++⇒∧ v (x ∷ xs) y
  rewrite ++⇒∧ v xs y
  = sym (∧-assoc (V.evalᶜ v x) (eval₆ v xs) (eval₆ v y))

to-∷-∨-✓ : ∀ {l} v f → eval₆ v [ to-∷-∨ {l} f ] ≡ eval₅ v f
to-∷-∨-✓ v (var₅ x)        = trans (∧-identityʳ (v x ∨ false)) (∨-identityʳ (v x))
to-∷-∨-✓ v (not₅ (var₅ x)) = trans (∧-identityʳ ((not (v x)) ∨ false)) (∨-identityʳ (not (v x)))
to-∷-∨-✓ v (or₅ x y)
  rewrite V.++⇒∨ v (to-∷-∨ x) (to-∷-∨ y)
  rewrite sym (to-∷-∨-✓ v x)
  rewrite sym (to-∷-∨-✓ v y)
  = ∧-distribʳ-∨ true (V.evalᶜ v (to-∷-∨ x)) (V.evalᶜ v (to-∷-∨ y))

to-∷-∧-✓ : ∀ v f → eval₆ v (to-∷-∧ f) ≡ eval₅ v f
to-∷-∧-✓ v (and₅ {zero}  {zero}  x y)
  rewrite ++⇒∧ v (to-∷-∧ x) (to-∷-∧ y)
  rewrite to-∷-∧-✓ v x
  rewrite to-∷-∧-✓ v y
  = refl
to-∷-∧-✓ v (and₅ {zero}  {suc n} x y)
  rewrite ++⇒∧ v (to-∷-∧ x) [ to-∷-∨ y ]
  rewrite to-∷-∧-✓ v x
  rewrite to-∷-∨-✓ v y
  = refl
to-∷-∧-✓ v (and₅ {suc m} {zero}  x y)
  rewrite ++⇒∧ v [ to-∷-∨ x ] (to-∷-∧ y)
  rewrite to-∷-∨-✓ v x
  rewrite to-∷-∧-✓ v y
  = refl
to-∷-∧-✓ v (and₅ {suc m} {suc n} x y)
  rewrite sym (to-∷-∨-✓ v x)
  rewrite sym (to-∷-∨-✓ v y)
  rewrite ∧-identityʳ (V.evalᶜ v (to-∷-∨ x))
  = refl

transform₆ : Formula₀ → Formula₆
transform₆ f = to-∷-∧ (transform₅ f)

transform₆-✓ : ∀ v f → eval₆ (makeTrue₅ v f) (transform₆ f) ≡ eval₀ v f
transform₆-✓ v f
 rewrite to-∷-∧-✓ (makeTrue₅ v f) (transform₅ f)
 rewrite sym (transform₅-✓ v f)
 = refl

unsat₆-✓ : ∀ f → (∀ v → eval₆ v (transform₆ f) ≡ false) → (∀ v → eval₀ v f ≡ false)
unsat₆-✓ f p v = sym (trans (sym (p (makeTrue₅ v f))) (transform₆-✓ v f))

maxVar : Formula₆ → ℕ
maxVar []       = 0
maxVar (k ∷ ks) = doKlause k ⊔ maxVar ks
  where
  doKlause : V.Clause → ℕ
  doKlause []             = 0
  doKlause (V.pos x ∷ ls) = suc x ⊔ doKlause ls
  doKlause (V.neg x ∷ ls) = suc x ⊔ doKlause ls

transform₇ : Formula₀ → Maybe Formula₇
transform₇ f = P.from-∷ (transform₆ f)

transform₇-✓ : ∀ v f₀ f₇ → transform₇ f₀ ≡ just f₇ → eval₇ (makeTrue₅ v f₀) f₇ ≡ eval₀ v f₀
transform₇-✓ v f₀ f₇ p
  rewrite P.from-∷-✓ (makeTrue₅ v f₀) (transform₆ f₀) f₇ p
  rewrite sym (transform₆-✓ v f₀)
  = refl

unsat₇-✓ : ∀ f₀ f₇ → transform₇ f₀ ≡ just f₇ → (∀ v → eval₇ v f₇ ≡ false) →
  (∀ v → eval₀ v f₀ ≡ false)
unsat₇-✓ f₀ f₇ p₁ p₂ v = sym (trans (sym (p₂ (makeTrue₅ v f₀))) (transform₇-✓ v f₀ f₇ p₁))
