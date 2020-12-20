import Data.Nat

-- module LRAT (bitsᵛ : Data.Nat.ℕ) (bitsᶜ : Data.Nat.ℕ) where
module LRAT where

bitsᵛ = 1
bitsᶜ = 1

open Data.Nat using (ℕ ; zero ; suc)

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; if_then_else_)
open import Data.Bool.Properties
  using (
      ∧-zeroʳ ; ∨-zeroʳ ; ∧-identityʳ ; ∨-identityʳ ; ∧-comm ; ∨-comm ; ∧-assoc ; ∨-assoc ;
      ∧-idem ; ∧-distribʳ-∨ ; ∧-distribˡ-∨ ; ∧-inverseʳ ; ∨-∧-booleanAlgebra ; not-¬ ; ¬-not
    )
  renaming (_≟_ to _≟ᵇ_)
open import Data.List using (List) renaming ([] to []ˡ ; _∷_ to _∷ˡ_ ; _++_ to _++ˡ_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ ; _∷_ to _∷ᵃ_)
open import Data.List.Relation.Unary.Any using (Any ; here ; there)
open import Data.Maybe using (Maybe ; just ; nothing) renaming (map to mapᵐ)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁ ; map₂ ; ∃)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec using (Vec) renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_)
open import Data.Vec.Properties using () renaming (≡-dec to ≡-decᵛ)
open import Function using (_$_ ; _∘_ ; id ; case_of_)
open import Level using (0ℓ)
open import Relation.Binary using (DecSetoid)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; ≢-sym ; inspect ; [_] ; cong ; subst ; trans ; decSetoid ;
    module ≡-Reasoning)
open import Relation.Nullary using (Dec ; _because_ ; ofʸ ; ofⁿ)
open import Relation.Nullary.Negation using (contradiction)

open import Algebra.Properties.BooleanAlgebra ∨-∧-booleanAlgebra using (deMorgan₁ ; deMorgan₂)
open ≡-Reasoning

Variable : Set
Variable = Vec Bool bitsᵛ

Assignment : Set
Assignment = Variable → Bool

data Literal : Set where
  pos : Variable → Literal
  neg : Variable → Literal

Clause : Set
Clause = List Literal

data Trie : ℕ → Set where
  leaf : Clause → Trie 0
  node : {n : ℕ} → Maybe (Trie n) → Maybe (Trie n) → Trie (suc n)

Formula : Set
Formula = Maybe (Trie bitsᶜ)

Index : Set
Index = Vec Bool bitsᶜ

data Step : Set where
  del : List Index → Step
  ext : Clause → List Index → List (List Index) → Step

Proof : Set
Proof = List Step

data Result (S T : Set) : Set where
  done : S → Result S T
  more : T → Result S T
  fail : Result S T

posInjective : (v₁ v₂ : Vec Bool bitsᵛ) → pos v₁ ≡ pos v₂ → v₁ ≡ v₂
posInjective v₁ v₂ refl = refl

negInjective : (v₁ v₂ : Vec Bool bitsᵛ) → neg v₁ ≡ neg v₂ → v₁ ≡ v₂
negInjective v₁ v₂ refl = refl

infix 4 _≟ᵛ_ _≟ˡ_

_≟ᵛ_ : (v₁ v₂ : Vec Bool bitsᵛ) → Dec (v₁ ≡ v₂)
_≟ᵛ_ = ≡-decᵛ _≟ᵇ_

_≟ˡ_ : (l₁ l₂ : Literal) → Dec (l₁ ≡ l₂)
pos v₁ ≟ˡ pos v₂ with v₁ ≟ᵛ v₂
... | true  because ofʸ refl = true because ofʸ refl
... | false because ofⁿ p = false because ofⁿ (p ∘ posInjective v₁ v₂)
pos _  ≟ˡ neg _  = false because ofⁿ λ ()
neg _  ≟ˡ pos _  = false because ofⁿ λ ()
neg v₁ ≟ˡ neg v₂ with v₁ ≟ᵛ v₂
... | true  because ofʸ refl = true because ofʸ refl
... | false because ofⁿ p = false because ofⁿ (p ∘ negInjective v₁ v₂)

literalDS : DecSetoid 0ℓ 0ℓ
literalDS = decSetoid _≟ˡ_

open import Data.List.Membership.DecSetoid literalDS using (_∈_ ; _∉_ ; _∈?_)

evalˡ : Assignment → Literal → Bool
evalˡ a (pos v) = a v
evalˡ a (neg v) = not (a v)

evalᶜ : Assignment → Clause → Bool
evalᶜ a []ˡ       = false
evalᶜ a (l ∷ˡ ls) = evalˡ a l ∨ evalᶜ a ls

eval′ : (n : ℕ) → Assignment → Maybe (Trie n) → Bool
eval′ _       _ nothing             = true
eval′ zero    a (just (leaf c))     = evalᶜ a c
eval′ (suc n) a (just (node tˡ tʳ)) = eval′ n a tˡ ∧ eval′ n a tʳ

eval : Assignment → Formula → Bool
eval a f = eval′ bitsᶜ a f

lookup′ : (n : ℕ) → Maybe (Trie n) → Vec Bool n → Maybe Clause
lookup′ _       nothing            _             = nothing
lookup′ zero    (just (leaf cˡ))   []ᵛ           = just cˡ
lookup′ (suc n) (just (node tˡ _)) (false ∷ᵛ is) = lookup′ n tˡ is
lookup′ (suc n) (just (node _ tʳ)) (true ∷ᵛ is)  = lookup′ n tʳ is

lookup : Formula → Index → Maybe Clause
lookup = lookup′ bitsᶜ

insert′ : (n : ℕ) → Maybe (Trie n) → Vec Bool n → Clause → Maybe (Trie n)
insert′ zero    _                   []ᵛ           c = just (leaf c)
insert′ (suc n) nothing             (false ∷ᵛ is) c = just (node (insert′ n nothing is c) nothing)
insert′ (suc n) nothing             (true ∷ᵛ is)  c = just (node nothing (insert′ n nothing is c))
insert′ (suc n) (just (node tˡ tʳ)) (false ∷ᵛ is) c = just (node (insert′ n tˡ is c) tʳ)
insert′ (suc n) (just (node tˡ tʳ)) (true ∷ᵛ is)  c = just (node tˡ (insert′ n tʳ is c))

insert : Formula → Index → Clause → Formula
insert = insert′ bitsᶜ

remove′ : (n : ℕ) → Maybe (Trie n) → Vec Bool n → Maybe (Trie n)
remove′ zero    _                   []ᵛ           = nothing
remove′ (suc n) nothing             (_ ∷ᵛ _)      = nothing
remove′ (suc n) (just (node tˡ tʳ)) (false ∷ᵛ is) = just (node (remove′ n tˡ is) tʳ)
remove′ (suc n) (just (node tˡ tʳ)) (true ∷ᵛ is)  = just (node tˡ (remove′ n tʳ is))

remove : Formula → Index → Formula
remove = remove′ bitsᶜ

++⇒∨ : (a : Assignment) → (c₁ c₂ : Clause) → evalᶜ a (c₁ ++ˡ c₂) ≡ evalᶜ a c₁ ∨ evalᶜ a c₂
++⇒∨ _ []ˡ       _  = refl
++⇒∨ a (l ∷ˡ ls) c₂ = begin
  evalˡ a l ∨ evalᶜ a (ls ++ˡ c₂)       ≡⟨ cong (evalˡ a l ∨_) $ ++⇒∨ a ls c₂ ⟩
  evalˡ a l ∨ evalᶜ a ls ∨ evalᶜ a c₂   ≡⟨ sym $ ∨-assoc (evalˡ a l) (evalᶜ a ls) (evalᶜ a c₂) ⟩
  (evalˡ a l ∨ evalᶜ a ls) ∨ evalᶜ a c₂ ∎

++-falseˡ : (a : Assignment) → (c₁ c₂ : Clause) → evalᶜ a c₁ ≡ false →
  evalᶜ a (c₁ ++ˡ c₂) ≡ evalᶜ a c₂
++-falseˡ a c₁ c₂ p = begin
  evalᶜ a (c₁ ++ˡ c₂)     ≡⟨ ++⇒∨ a c₁ c₂ ⟩
  evalᶜ a c₁ ∨ evalᶜ a c₂ ≡⟨ cong (_∨ evalᶜ a c₂) p ⟩
  evalᶜ a c₂              ∎

notNot : (b : Bool) → not (not b) ≡ b
notNot true  = refl
notNot false = refl

notFalse : (b : Bool) → not b ≡ false → b ≡ true
notFalse true _ = refl

notTrue : (b : Bool) → not b ≡ true → b ≡ false
notTrue false _ = refl

flip : Literal → Literal
flip (pos v) = neg v
flip (neg v) = pos v

flipNot : (a : Assignment) → (l : Literal) → evalˡ a (flip l) ≡ not (evalˡ a l)
flipNot _ (pos _) = refl
flipNot a (neg v) = sym $ notNot (a v)

flipInjective : {l₁ l₂ : Literal} → flip l₁ ≡ flip l₂ → l₁ ≡ l₂
flipInjective {pos _} {pos _} refl = refl
flipInjective {neg _} {neg _} refl = refl

∧-splitTrue : (x y : Bool) → x ∧ y ≡ true → x ≡ true × y ≡ true
∧-splitTrue true  true  _  = refl , refl
∧-splitTrue false false ()

∨-splitFalse : (x y : Bool) → x ∨ y ≡ false → x ≡ false × y ≡ false
∨-splitFalse false false refl = refl , refl

∧-splitFalse : (x y : Bool) → x ∧ y ≡ false → x ≡ false ⊎ y ≡ false
∧-splitFalse false false _ = inj₁ refl
∧-splitFalse false true  _ = inj₁ refl
∧-splitFalse true false  _ = inj₂ refl

∨-splitTrue : (x y : Bool) → x ∨ y ≡ true → x ≡ true ⊎ y ≡ true
∨-splitTrue false _ refl = inj₂ refl
∨-splitTrue true  _ refl = inj₁ refl

∧-extendFalse : (x y : Bool) → x ≡ false → x ∧ y ≡ false
∧-extendFalse _ _ refl = refl

∨-extendTrue : (x y : Bool) → x ≡ true → x ∨ y ≡ true
∨-extendTrue _ _ refl = refl

∧-extendTrue : (x y : Bool) → x ≡ true → x ∧ y ≡ y
∧-extendTrue x y refl = refl

∨-extendFalse : (x y : Bool) → x ≡ false → x ∨ y ≡ y
∨-extendFalse x y refl = refl

∧-joinTrue : (x y : Bool) → x ≡ true → y ≡ true → x ∧ y ≡ true
∧-joinTrue _ _ refl refl = refl

∨-stripFalse : (x y z : Bool) → x ∨ y ∨ z ≡ false → x ∨ z ≡ false
∨-stripFalse x true  _ p = case trans (sym p) (∨-zeroʳ x) of λ ()
∨-stripFalse _ false _ p = p

anyLiteralTrue : (a : Assignment) → (l : Literal) → (c : Clause) →
  evalˡ a l ≡ true → l ∈ c → evalᶜ a c ≡ true
anyLiteralTrue a l (lᶜ ∷ˡ lsᶜ) p₁ (here refl) = begin
  evalˡ a l ∨ evalᶜ a lsᶜ ≡⟨ cong (_∨ evalᶜ a lsᶜ) p₁ ⟩
  true                    ∎
anyLiteralTrue a l (lᶜ ∷ˡ lsᶜ) p₁ (there p₂) = begin
  evalˡ a lᶜ ∨ evalᶜ a lsᶜ ≡⟨ cong (evalˡ a lᶜ ∨_) $ anyLiteralTrue a l lsᶜ p₁ p₂ ⟩
  evalˡ a lᶜ ∨ true        ≡⟨ ∨-zeroʳ (evalˡ a lᶜ) ⟩
  true                     ∎

allLiteralsFalse : (a : Assignment) → (c : Clause) →
  evalᶜ a c ≡ false → All (λ lᶜ → evalˡ a lᶜ ≡ false) c
allLiteralsFalse _ []ˡ         _ = []ᵃ
allLiteralsFalse a (lᶜ ∷ˡ lsᶜ) p
  with q₁ , q₂ ← ∨-splitFalse (evalˡ a lᶜ) (evalᶜ a lsᶜ) p
  = q₁ ∷ᵃ allLiteralsFalse a lsᶜ q₂

allFlippedTrue : (a : Assignment) → (c : Clause) →
  evalᶜ a c ≡ false → All (λ lᶜ → evalˡ a (flip lᶜ) ≡ true) c
allFlippedTrue _ []ˡ         _ = []ᵃ
allFlippedTrue a (lᶜ ∷ˡ lsᶜ) p
  with q₁ , q₂ ← ∨-splitFalse (evalˡ a lᶜ) (evalᶜ a lsᶜ) p
  = subst (λ # → evalˡ a (flip lᶜ) ≡ #) (cong not q₁) (flipNot a lᶜ) ∷ᵃ allFlippedTrue a lsᶜ q₂

removeLiteral : (c : Clause) → (l : Literal) → Clause
removeLiteral []ˡ         _ = []ˡ
removeLiteral (lᶜ ∷ˡ lsᶜ) l with lᶜ ≟ˡ l
... | true  because ofʸ _ = removeLiteral lsᶜ l
... | false because ofⁿ _ = lᶜ ∷ˡ removeLiteral lsᶜ l

removeLiteral-∧-not : (a : Assignment) → (c : Clause) →  (l : Literal) →
  evalᶜ a c ∧ not (evalˡ a l) ≡ evalᶜ a (removeLiteral c l) ∧ not (evalˡ a l)
removeLiteral-∧-not a []ˡ         _ = refl
removeLiteral-∧-not a (lᶜ ∷ˡ lsᶜ) l with lᶜ ≟ˡ l
... | true because ofʸ refl = begin
  (evalˡ a lᶜ ∨ evalᶜ a lsᶜ) ∧ not (evalˡ a lᶜ)                  ≡⟨ ∧-distribʳ-∨ (not (evalˡ a lᶜ)) (evalˡ a lᶜ) (evalᶜ a lsᶜ) ⟩
  evalˡ a lᶜ ∧ not (evalˡ a lᶜ) ∨ evalᶜ a lsᶜ ∧ not (evalˡ a lᶜ) ≡⟨ cong (_∨ evalᶜ a lsᶜ ∧ not (evalˡ a lᶜ)) $ ∧-inverseʳ (evalˡ a lᶜ) ⟩
  evalᶜ a lsᶜ ∧ not (evalˡ a lᶜ)                                 ≡⟨ removeLiteral-∧-not a lsᶜ l  ⟩
  evalᶜ a (removeLiteral lsᶜ lᶜ) ∧ not (evalˡ a lᶜ)              ∎
... | false because ofⁿ _ = begin
  (evalˡ a lᶜ ∨ evalᶜ a lsᶜ) ∧ not (evalˡ a l)                                   ≡⟨ ∧-distribʳ-∨ (not (evalˡ a l)) (evalˡ a lᶜ) (evalᶜ a lsᶜ) ⟩
  evalˡ a lᶜ ∧ not (evalˡ a l) ∨ evalᶜ a lsᶜ ∧ not (evalˡ a l)                   ≡⟨ cong (evalˡ a lᶜ ∧ not (evalˡ a l) ∨_) $ removeLiteral-∧-not a lsᶜ l ⟩
  evalˡ a lᶜ ∧ not (evalˡ a l) ∨ evalᶜ a (removeLiteral lsᶜ l) ∧ not (evalˡ a l) ≡⟨ sym $ ∧-distribʳ-∨ (not (evalˡ a l)) (evalˡ a lᶜ) (evalᶜ a (removeLiteral lsᶜ l)) ⟩
  (evalˡ a lᶜ ∨ evalᶜ a (removeLiteral lsᶜ l)) ∧ not (evalˡ a l)                 ∎

removeLiteralTrue : (a : Assignment) → (c : Clause) → (l : Literal) →
  evalᶜ a (removeLiteral c l) ≡ true → evalᶜ a c ≡ true
removeLiteralTrue a (lᶜ ∷ˡ lsᶜ) l p
  with lᶜ ≟ˡ l
... | true  because ofʸ _ = begin
  evalˡ a lᶜ ∨ evalᶜ a lsᶜ ≡⟨ cong (evalˡ a lᶜ ∨_) $ removeLiteralTrue a lsᶜ l p ⟩
  evalˡ a lᶜ ∨ true        ≡⟨ ∨-zeroʳ (evalˡ a lᶜ) ⟩
  true                     ∎
... | false because ofⁿ q
  with ∨-splitTrue (evalˡ a lᶜ) (evalᶜ a (removeLiteral lsᶜ l)) p
... | inj₁ r = begin
  evalˡ a lᶜ ∨ evalᶜ a lsᶜ ≡⟨ cong (_∨ evalᶜ a lsᶜ) $ r ⟩
  true                     ∎
... | inj₂ r = begin
  evalˡ a lᶜ ∨ evalᶜ a lsᶜ ≡⟨ (cong (evalˡ a lᶜ ∨_) $ removeLiteralTrue a lsᶜ l r) ⟩
  evalˡ a lᶜ ∨ true        ≡⟨ ∨-zeroʳ (evalˡ a lᶜ) ⟩
  true                     ∎

removeLiteral-∉ : (l : Literal) → (c : Clause) → l ∉ removeLiteral c l
removeLiteral-∉ _ []ˡ         = λ ()
removeLiteral-∉ l (lᶜ ∷ˡ lsᶜ)
  with lᶜ ≟ˡ l
... | true  because ofʸ _ = removeLiteral-∉ l lsᶜ
... | false because ofⁿ p = λ where
  (here q)  → contradiction (sym q) p
  (there q) → contradiction q (removeLiteral-∉ l lsᶜ)

duplicate′ : (n : ℕ) → (t : Maybe (Trie n)) → (i : Vec Bool n) → (c : Clause) →
  lookup′ n t i ≡ just c → ∀ a → eval′ n a t ≡ eval′ n a t ∧ evalᶜ a c
duplicate′ zero    (just (leaf cˡ))    []ᵛ           c refl a = sym $ ∧-idem (evalᶜ a c)
duplicate′ (suc n) (just (node tˡ tʳ)) (false ∷ᵛ is) c p    a = begin
  eval′ n a tˡ ∧ eval′ n a tʳ               ≡⟨ cong (_∧ (eval′ n a tʳ)) $ duplicate′ n tˡ is c p a ⟩
  (eval′ n a tˡ ∧ evalᶜ a c) ∧ eval′ n a tʳ ≡⟨ ∧-assoc (eval′ n a tˡ) (evalᶜ a c) (eval′ n a tʳ) ⟩
  eval′ n a tˡ ∧ evalᶜ a c ∧ eval′ n a tʳ   ≡⟨ cong (eval′ n a tˡ ∧_) $ ∧-comm (evalᶜ a c) (eval′ n a tʳ) ⟩
  eval′ n a tˡ ∧ eval′ n a tʳ ∧ evalᶜ a c   ≡⟨ sym $ ∧-assoc (eval′ n a tˡ) (eval′ n a tʳ) (evalᶜ a c) ⟩
  (eval′ n a tˡ ∧ eval′ n a tʳ) ∧ evalᶜ a c ∎
duplicate′ (suc n) (just (node tˡ tʳ)) (true ∷ᵛ is)  c p    a = begin
  eval′ n a tˡ ∧ eval′ n a tʳ               ≡⟨ cong ((eval′ n a tˡ) ∧_) $ duplicate′ n tʳ is c p a ⟩
  eval′ n a tˡ ∧ eval′ n a tʳ ∧ evalᶜ a c   ≡⟨ (sym $ ∧-assoc (eval′ n a tˡ) (eval′ n a tʳ) (evalᶜ a c)) ⟩
  (eval′ n a tˡ ∧ eval′ n a tʳ) ∧ evalᶜ a c ∎

duplicate : (f : Formula) → (i : Index) → (c : Clause) → lookup f i ≡ just c →
  ∀ a → eval a f ≡ eval a f ∧ evalᶜ a c
duplicate = duplicate′ bitsᶜ

andNot : (c₁ c₂ : Clause) → Clause
andNot c₁ []ˡ         = c₁
andNot c₁ (lᶜ ∷ˡ lsᶜ) = andNot (removeLiteral c₁ lᶜ) lsᶜ

andNotIntro : (a : Assignment) → (c₁ c₂ : Clause) →
  evalᶜ a c₁ ∧ not (evalᶜ a c₂) ≡ evalᶜ a (andNot c₁ c₂) ∧ not (evalᶜ a c₂)
andNotIntro a _  []ˡ         = refl
andNotIntro a c₁ (lᶜ ∷ˡ lsᶜ) = begin
  evalᶜ a c₁ ∧ not (evalˡ a lᶜ ∨ evalᶜ a lsᶜ)                                         ≡⟨ cong (evalᶜ a c₁ ∧_) $ deMorgan₂ (evalˡ a lᶜ) (evalᶜ a lsᶜ) ⟩
  evalᶜ a c₁ ∧ not (evalˡ a lᶜ) ∧ not (evalᶜ a lsᶜ)                                   ≡⟨ sym $ ∧-assoc (evalᶜ a c₁) (not (evalˡ a lᶜ)) (not (evalᶜ a lsᶜ)) ⟩
  (evalᶜ a c₁ ∧ not (evalˡ a lᶜ)) ∧ not (evalᶜ a lsᶜ)                                 ≡⟨ cong (_∧ not (evalᶜ a lsᶜ)) $ removeLiteral-∧-not a c₁ lᶜ ⟩
  (evalᶜ a (removeLiteral c₁ lᶜ) ∧ not (evalˡ a lᶜ)) ∧ not (evalᶜ a lsᶜ)              ≡⟨ ∧-assoc (evalᶜ a (removeLiteral c₁ lᶜ)) (not (evalˡ a lᶜ)) (not (evalᶜ a lsᶜ)) ⟩
  evalᶜ a (removeLiteral c₁ lᶜ) ∧ not (evalˡ a lᶜ) ∧ not (evalᶜ a lsᶜ)                ≡⟨ cong (evalᶜ a (removeLiteral c₁ lᶜ) ∧_) $ ∧-comm (not (evalˡ a lᶜ)) (not (evalᶜ a lsᶜ)) ⟩
  evalᶜ a (removeLiteral c₁ lᶜ) ∧ not (evalᶜ a lsᶜ) ∧ not (evalˡ a lᶜ)                ≡⟨ sym $ ∧-assoc (evalᶜ a (removeLiteral c₁ lᶜ)) (not (evalᶜ a lsᶜ)) (not (evalˡ a lᶜ)) ⟩
  (evalᶜ a (removeLiteral c₁ lᶜ) ∧ not (evalᶜ a lsᶜ)) ∧ not (evalˡ a lᶜ)              ≡⟨ cong (_∧ not (evalˡ a lᶜ)) $ andNotIntro a (removeLiteral c₁ lᶜ) lsᶜ ⟩
  (evalᶜ a (andNot (removeLiteral c₁ lᶜ) lsᶜ) ∧ not (evalᶜ a lsᶜ)) ∧ not (evalˡ a lᶜ) ≡⟨ ∧-assoc (evalᶜ a (andNot (removeLiteral c₁ lᶜ) lsᶜ)) (not (evalᶜ a lsᶜ)) (not (evalˡ a lᶜ)) ⟩
  evalᶜ a (andNot (removeLiteral c₁ lᶜ) lsᶜ) ∧ not (evalᶜ a lsᶜ) ∧ not (evalˡ a lᶜ)   ≡⟨ cong (evalᶜ a (andNot (removeLiteral c₁ lᶜ) lsᶜ) ∧_) $ sym $ deMorgan₂ (evalᶜ a lsᶜ) (evalˡ a lᶜ) ⟩
  evalᶜ a (andNot (removeLiteral c₁ lᶜ) lsᶜ) ∧ not (evalᶜ a lsᶜ ∨ evalˡ a lᶜ)         ≡⟨ (cong (λ # → evalᶜ a (andNot (removeLiteral c₁ lᶜ) lsᶜ) ∧ not #) $ ∨-comm (evalᶜ a lsᶜ) (evalˡ a lᶜ)) ⟩
  evalᶜ a (andNot (removeLiteral c₁ lᶜ) lsᶜ) ∧ not (evalˡ a lᶜ ∨ evalᶜ a lsᶜ)         ∎

pushUnit : (a : Assignment) → (l : Literal) → (c : Clause) →
  evalᶜ a (l ∷ˡ []ˡ) ∧ not (evalᶜ a c) ≡ not (evalᶜ a (flip l ∷ˡ c))
pushUnit a (pos v) []ˡ = begin
  (a v ∨ false) ∧ true    ≡⟨ ∧-identityʳ (a v ∨ false) ⟩
  (a v ∨ false)           ≡⟨ ∨-identityʳ (a v) ⟩
  a v                     ≡⟨ sym $ notNot (a v) ⟩
  not (not (a v))         ≡⟨ cong not $ sym $ ∨-identityʳ (not (a v)) ⟩
  not (not (a v) ∨ false) ∎
pushUnit a (neg v) []ˡ = begin
  (not (a v) ∨ false) ∧ true ≡⟨ ∧-identityʳ (not (a v) ∨ false) ⟩
  not (a v) ∨ false          ≡⟨ ∨-identityʳ (not (a v)) ⟩
  not (a v)                  ≡⟨ cong not $ sym $ ∨-identityʳ (a v) ⟩
  not (a v ∨ false)          ∎
pushUnit a l (lᶜ ∷ˡ lsᶜ) = begin
  (evalˡ a l ∨ false) ∧ not (evalˡ a lᶜ ∨ evalᶜ a lsᶜ)          ≡⟨ cong (_∧ not (evalˡ a lᶜ ∨ evalᶜ a lsᶜ)) $ ∨-identityʳ (evalˡ a l) ⟩
  evalˡ a l ∧ not (evalˡ a lᶜ ∨ evalᶜ a lsᶜ)                    ≡⟨ cong (evalˡ a l ∧_) $ deMorgan₂ (evalˡ a lᶜ) (evalᶜ a lsᶜ) ⟩
  evalˡ a l ∧ not (evalˡ a lᶜ) ∧ not (evalᶜ a lsᶜ)              ≡⟨ cong (_∧ not (evalˡ a lᶜ) ∧ not (evalᶜ a lsᶜ)) $ sym $ notNot (evalˡ a l) ⟩
  not (not (evalˡ a l)) ∧ not (evalˡ a lᶜ) ∧ not (evalᶜ a lsᶜ)  ≡⟨ cong (λ # → not # ∧ not (evalˡ a lᶜ) ∧ not (evalᶜ a lsᶜ)) $ sym $ flipNot a l ⟩
  not (evalˡ a (flip l)) ∧ not (evalˡ a lᶜ) ∧ not (evalᶜ a lsᶜ) ≡⟨ cong (not (evalˡ a (flip l)) ∧_) $ sym $ deMorgan₂ (evalˡ a lᶜ) (evalᶜ a lsᶜ) ⟩
  not (evalˡ a (flip l)) ∧ not (evalˡ a lᶜ ∨ evalᶜ a lsᶜ)       ≡⟨ sym $ deMorgan₂ (evalˡ a (flip l)) (evalˡ a lᶜ ∨ evalᶜ a lsᶜ) ⟩
  not (evalˡ a (flip l) ∨ evalˡ a lᶜ ∨ evalᶜ a lsᶜ)             ∎

checkRUP′ : (f : Formula) → (c : Clause) → (is : List Index) →
  Result (∀ a → eval a f ∧ not (evalᶜ a c) ≡ false) Clause
checkRUP′ f c []ˡ       = more c
checkRUP′ f c (i ∷ˡ is)
  with lookup f i | inspect (lookup f) i
... | nothing | _       = fail
... | just cᶠ | [ eq₁ ]
  with andNot cᶠ c | inspect (andNot cᶠ) c
checkRUP′ f c (i ∷ˡ is) | just cᶠ | [ eq₁ ] | []ˡ | [ eq₂ ] = done $ λ a → begin
  eval a f ∧ not (evalᶜ a c)                         ≡⟨ cong (_∧ not (evalᶜ a c)) $ duplicate f i cᶠ eq₁ a ⟩
  (eval a f ∧ evalᶜ a cᶠ) ∧ not (evalᶜ a c)          ≡⟨ ∧-assoc (eval a f) (evalᶜ a cᶠ) (not (evalᶜ a c)) ⟩
  eval a f ∧ evalᶜ a cᶠ ∧ not (evalᶜ a c)            ≡⟨ cong (eval a f ∧_) $ andNotIntro a cᶠ c ⟩
  eval a f ∧ evalᶜ a (andNot cᶠ c) ∧ not (evalᶜ a c) ≡⟨ cong (λ # → eval a f ∧ evalᶜ a # ∧ not (evalᶜ a c)) eq₂ ⟩
  eval a f ∧ false                                   ≡⟨ ∧-zeroʳ (eval a f) ⟩
  false                                              ∎
checkRUP′ f c (i ∷ˡ is) | just cᶠ | [ eq₁ ] | l ∷ˡ []ˡ | [ eq₂ ]
  with checkRUP′ f (flip l ∷ˡ c) is
... | done p = done $ λ a → begin
  eval a f ∧ not (evalᶜ a c)                         ≡⟨ cong (_∧ not (evalᶜ a c)) $ duplicate f i cᶠ eq₁ a ⟩
  (eval a f ∧ evalᶜ a cᶠ) ∧ not (evalᶜ a c)          ≡⟨ ∧-assoc (eval a f) (evalᶜ a cᶠ) (not (evalᶜ a c)) ⟩
  eval a f ∧ evalᶜ a cᶠ ∧ not (evalᶜ a c)            ≡⟨ cong (eval a f ∧_) $ andNotIntro a cᶠ c ⟩
  eval a f ∧ evalᶜ a (andNot cᶠ c) ∧ not (evalᶜ a c) ≡⟨ cong (λ # → eval a f ∧ evalᶜ a # ∧ not (evalᶜ a c)) eq₂ ⟩
  eval a f ∧ (evalˡ a l ∨ false) ∧ not (evalᶜ a c)   ≡⟨ cong (eval a f ∧_) $ pushUnit a l c ⟩
  eval a f ∧ not (evalˡ a (flip l) ∨ evalᶜ a c)      ≡⟨ p a ⟩
  false                                              ∎
... | more cʳ = more cʳ
... | fail    = fail
checkRUP′ _ _ _ | _ | _ | _ | _ = fail

checkRUP : (f : Formula) → (c : Clause) → (is : List Index) →
  Result (∀ a → eval a f ≡ eval a f ∧ evalᶜ a c) Clause
checkRUP f c is
  with checkRUP′ f c is
... | fail    = fail
... | more cʳ = more cʳ
... | done p  = done $ λ a → case ∧-splitFalse (eval a f) (not (evalᶜ a c)) (p a) of λ where
    (inj₁ q) → trans q $ sym $ ∧-extendFalse (eval a f) (evalᶜ a c) q
    (inj₂ q) → begin
      eval a f             ≡⟨ sym $ ∧-identityʳ (eval a f) ⟩
      eval a f ∧ true      ≡⟨ sym $ cong (eval a f ∧_) $ notFalse (evalᶜ a c) q ⟩
      eval a f ∧ evalᶜ a c ∎

nextIndex′ : (n : ℕ) → Maybe (Trie n) → Maybe (Vec Bool n)
nextIndex′ zero    nothing           = just []ᵛ
nextIndex′ zero    (just _)          = nothing
nextIndex′ (suc n) nothing
  with nextIndex′ n nothing
... | just isʳ = just $ false ∷ᵛ isʳ
... | nothing  = nothing
nextIndex′ (suc n) (just (node tˡ tʳ))
  with nextIndex′ n tˡ
... | just isʳ = just $ false ∷ᵛ isʳ
... | nothing
  with nextIndex′ n tʳ
... | just isʳ = just $ true ∷ᵛ isʳ
... | nothing  = nothing

nextIndex : Formula → Maybe Index
nextIndex f = nextIndex′ bitsᶜ f

nextIndexLeft′ : (n : ℕ) → (tˡ tʳ : Maybe (Trie n)) → (is : Vec Bool n) →
  nextIndex′ (suc n) (just (node tˡ tʳ)) ≡ just (false ∷ᵛ is) → nextIndex′ n tˡ ≡ just is
nextIndexLeft′ n tˡ tʳ is p
  with nextIndex′ n tˡ
... | just isʳ = case p of λ { refl → refl }
... | nothing
  with nextIndex′ n tʳ
... | just isʳ = case p of λ ()
... | nothing  = case p of λ ()

nextIndexRight′ : (n : ℕ) → (tˡ tʳ : Maybe (Trie n)) → (is : Vec Bool n) →
  nextIndex′ (suc n) (just (node tˡ tʳ)) ≡ just (true ∷ᵛ is) → nextIndex′ n tʳ ≡ just is
nextIndexRight′ n tˡ tʳ is p
  with nextIndex′ n tˡ
... | just isʳ = case p of λ ()
... | nothing
  with nextIndex′ n tʳ
... | just isʳ = case p of λ { refl → refl }
... | nothing  = case p of λ ()

insertEmpty′ : (n : ℕ) → (a : Assignment) → (is : Vec Bool n) → (c : Clause) →
  eval′ n a (insert′ n nothing is c) ≡ evalᶜ a c
insertEmpty′ zero    _ []ᵛ           _ = refl
insertEmpty′ (suc n) a (false ∷ᵛ is) c = begin
  eval′ n a (insert′ n nothing is c) ∧ true ≡⟨ ∧-identityʳ (eval′ n a (insert′ n nothing is c)) ⟩
  eval′ n a (insert′ n nothing is c)        ≡⟨ insertEmpty′ n a is c ⟩
  evalᶜ a c                                 ∎
insertEmpty′ (suc n) a (true ∷ᵛ is)  c = insertEmpty′ n a is c

append⇒∧′ : (n : ℕ) → (t : Maybe (Trie n)) → (is : Vec Bool n) → (c : Clause) →
  nextIndex′ n t ≡ just is → ∀ a → eval′ n a (insert′ n t is c) ≡ eval′ n a t ∧ evalᶜ a c
append⇒∧′ zero    nothing             []ᵛ           _ _ _ = refl
append⇒∧′ (suc n) nothing             (i ∷ᵛ is)     c _ a = insertEmpty′ (suc n) a (i ∷ᵛ is) c
append⇒∧′ (suc n) (just (node tˡ tʳ)) (false ∷ᵛ is) c p a = begin
  eval′ n a (insert′ n tˡ is c) ∧ eval′ n a tʳ ≡⟨ cong (_∧ eval′ n a tʳ) $ append⇒∧′ n tˡ is c (nextIndexLeft′ n tˡ tʳ is p) a ⟩
  (eval′ n a tˡ ∧ evalᶜ a c) ∧ eval′ n a tʳ    ≡⟨ ∧-assoc (eval′ n a tˡ) (evalᶜ a c) (eval′ n a tʳ) ⟩
  eval′ n a tˡ ∧ evalᶜ a c ∧ eval′ n a tʳ      ≡⟨ cong (eval′ n a tˡ ∧_) $ ∧-comm (evalᶜ a c) (eval′ n a tʳ) ⟩
  eval′ n a tˡ ∧ eval′ n a tʳ ∧ evalᶜ a c      ≡⟨ sym $ ∧-assoc (eval′ n a tˡ) (eval′ n a tʳ) (evalᶜ a c) ⟩
  (eval′ n a tˡ ∧ eval′ n a tʳ) ∧ evalᶜ a c    ∎
append⇒∧′ (suc n) (just (node tˡ tʳ)) (true ∷ᵛ is)  c p a = begin
  eval′ n a tˡ ∧ eval′ n a (insert′ n tʳ is c) ≡⟨ cong (eval′ n a tˡ ∧_) $ append⇒∧′ n tʳ is c (nextIndexRight′ n tˡ tʳ is p) a ⟩
  eval′ n a tˡ ∧ eval′ n a tʳ ∧ evalᶜ a c      ≡⟨ sym $ ∧-assoc (eval′ n a tˡ) (eval′ n a tʳ) (evalᶜ a c) ⟩
  (eval′ n a tˡ ∧ eval′ n a tʳ) ∧ evalᶜ a c    ∎

append⇒∧ : (f : Formula) → (i : Index) → (c : Clause) →
  nextIndex f ≡ just i → ∀ a → eval a (insert f i c) ≡ eval a f ∧ evalᶜ a c
append⇒∧ = append⇒∧′ bitsᶜ

-- Not strictly a resolvent, as |l| isn't removed from |c₁|.
resolvent : Literal → Clause → Clause → Clause
resolvent l c₁ c₂ = c₁ ++ˡ removeLiteral c₂ (flip l)

resolventTrue : (a : Assignment) → (l : Literal) → (c₁ c₂ : Clause) → evalᶜ a c₁ ≡ false →
  evalᶜ a (resolvent l c₁ c₂) ≡ true → evalᶜ a (removeLiteral c₂ (flip l)) ≡ true
resolventTrue _ _ []ˡ         _  _  p₂ = p₂
resolventTrue a l (lᶜ ∷ˡ lsᶜ) c₂ p₁ p₂
  with q₁ , q₂ ← ∨-splitFalse (evalˡ a lᶜ) (evalᶜ a lsᶜ) p₁ = begin
  evalᶜ a (removeLiteral c₂ (flip l))                      ≡⟨ sym $ ++-falseˡ a lsᶜ (removeLiteral c₂ (flip l)) q₂ ⟩
  evalᶜ a (lsᶜ ++ˡ removeLiteral c₂ (flip l))              ≡⟨ sym $ ∨-extendFalse (evalˡ a lᶜ) (evalᶜ a (lsᶜ ++ˡ removeLiteral c₂ (flip l))) q₁ ⟩
  evalˡ a lᶜ ∨ evalᶜ a (lsᶜ ++ˡ removeLiteral c₂ (flip l)) ≡⟨ p₂ ⟩
  true                                                     ∎

adjust : Assignment → Variable → Bool → Assignment
adjust a vᵃ b v
  with v ≟ᵛ vᵃ
... | true  because ofʸ _ = b
... | false because ofⁿ _ = a v

adjustSame : (a : Assignment) → (vᵃ : Variable) → (b : Bool) → (adjust a vᵃ b) vᵃ ≡ b
adjustSame a vᵃ b
  with vᵃ ≟ᵛ vᵃ
... | true  because ofʸ _ = refl
... | false because ofⁿ q = contradiction refl q

adjustOther : (a : Assignment) → (vᵃ v : Variable) → (b : Bool) → vᵃ ≢ v → (adjust a vᵃ b) v ≡ a v
adjustOther a vᵃ v b p
  with v ≟ᵛ vᵃ
... | true  because ofʸ q = contradiction (sym q) p
... | false because ofⁿ _ = refl

forceTrue : Assignment → Literal → Assignment
forceTrue a (pos v) = adjust a v true
forceTrue a (neg v) = adjust a v false

{-
forceTrueForces : ∀ a l → evalˡ (forceTrue a l) l ≡ true
forceTrueForces a (pos v) = adjustSame a v true
forceTrueForces a (neg v) = cong not $ adjustSame a v false

forceTrueNoChange : ∀ l l′ a → flip l ≢ l′ → evalˡ a l′ ≡ true → evalˡ (forceTrue a l) l′ ≡ true
forceTrueNoChange (pos v) (pos v′) a p₁ p₂
  with v′ ≟ᵛ v
... | true  because ofʸ _ = refl
... | false because ofⁿ _ = p₂
forceTrueNoChange (pos v) (neg v′) a p₁ p₂ rewrite adjustOther a v v′ true  (p₁ ∘ cong neg) = p₂
forceTrueNoChange (neg v) (pos v′) a p₁ p₂ rewrite adjustOther a v v′ false (p₁ ∘ cong pos) = p₂
forceTrueNoChange (neg v) (neg v′) a p₁ p₂
  with v′ ≟ᵛ v
... | true  because ofʸ _ = refl
... | false because ofⁿ _ = p₂

forceTrue-∈ : ∀ l c a → l ∈ c → evalᶜ (forceTrue a l) c ≡ true
forceTrue-∈ (pos v) (pos v ∷ˡ ls′) a (here refl) rewrite adjustSame a v true = refl
forceTrue-∈ (neg v) (neg v ∷ˡ ls′) a (here refl) rewrite cong not $ adjustSame a v false = refl
forceTrue-∈ l       (l′ ∷ˡ ls′)    a (there p)
  rewrite forceTrue-∈ l ls′ a p = ∨-zeroʳ (evalˡ (forceTrue a l) l′)

forceTrue-∉ : ∀ l c a → flip l ∉ c → evalᶜ a c ≡ true → evalᶜ (forceTrue a l) c ≡ true
forceTrue-∉ l (l′ ∷ˡ ls′) a p₁ p₂
  with ∨-splitTrue (evalˡ a l′) (evalᶜ a ls′) p₂
... | inj₁ q rewrite forceTrueNoChange l l′ a (p₁ ∘ here) q = refl
... | inj₂ q rewrite forceTrue-∉ l ls′ a (p₁ ∘ there) q = ∨-zeroʳ (evalˡ (forceTrue a l) l′)

∉-tail : ∀ x y ys → x ∉ y ∷ˡ ys → x ∉ ys
∉-tail _ _ (_ ∷ˡ _) p (here n)  = p $ there (here n)
∉-tail _ _ (_ ∷ˡ _) p (there n) = p $ there (there n)

clauseTrue₁ : ∀ a c l → evalᶜ a c ≡ true → flip l ∉ c → evalᶜ (forceTrue a l) c ≡ true
clauseTrue₁ a (l′ ∷ˡ ls′) l p₁ p₂
  with evalˡ a l′ | inspect (evalˡ a) l′
... | false | _
  rewrite clauseTrue₁ a ls′ l p₁ (∉-tail (flip l) l′ ls′ p₂)
  = ∨-zeroʳ $ evalˡ (forceTrue a l) l′
... | true | [ eq ]
  with l ≟ˡ l′
... | true  because ofʸ refl = forceTrue-∈ l (l′ ∷ˡ ls′) a (here refl)
... | false because ofⁿ _    = forceTrue-∉ l (l′ ∷ˡ ls′) a p₂ (∨-trueExtend (evalᶜ a ls′) eq)

clauseTrue₂ : ∀ a l ls c l′ → evalᶜ a (l ∷ˡ ls) ≡ false → l′ ∈ ls → flip l′ ∈ c → l ≢ l′ →
  evalᶜ (forceTrue a l) c ≡ true
clauseTrue₂ a l (l″ ∷ˡ ls″) c l′ p₁ (here refl) p₃ p₄
  with (_ ∷ᵃ q ∷ᵃ _) ← allFlippedTrue a (l ∷ˡ l″ ∷ˡ ls″) p₁
  with r ← forceTrueNoChange l (flip l″) a (p₄ ∘ flipInjective) q
  = anyLiteralTrue (forceTrue a l) (flip l″) c r p₃
clauseTrue₂ a l (l″ ∷ˡ ls″) c l′ p₁ (there p₂)  p₃ p₄
  with q ← ∨-falseStrip (evalˡ a l) (evalˡ a l″) (evalᶜ a ls″) p₁
  = clauseTrue₂ a l ls″ c l′ q  p₂ p₃ p₄

clauseTrue₃ : ∀ a l ls c → evalᶜ a (l ∷ˡ ls) ≡ false → evalᶜ a (resolvent l (l ∷ˡ ls) c) ≡ true →
  evalᶜ (forceTrue a l) c ≡ true
clauseTrue₃ a l ls c p₁ p₂
  with q ← resolventTrue a l (l ∷ˡ ls) c p₁ p₂
  with r ← removeLiteral-∉ (flip l) c
  with s ← forceTrue-∉ l (removeLiteral c (flip l)) a r q
  = removeLiteralTrue (forceTrue a l) c (flip l) s

clauseCheck₁ : ∀ l c → Maybe (flip l ∉ c)
clauseCheck₁ l c
  with flip l ∈? c
... | false because ofⁿ p = just p
... | true  because ofʸ _ = nothing

clauseCheck₂ : ∀ ls c l → Maybe (∃ λ l′ → l′ ∈ ls × flip l′ ∈ c × l ≢ l′)
clauseCheck₂ []ˡ         _ _ = nothing
clauseCheck₂ (l″ ∷ˡ ls″) c l
  with l ≟ˡ l″
... | true  because ofʸ _ = mapᵐ ((map₂ (map₁ there))) (clauseCheck₂ ls″ c l)
... | false because ofⁿ p
  with flip l″ ∈? c
... | false because ofⁿ _ = mapᵐ ((map₂ (map₁ there))) (clauseCheck₂ ls″ c l)
... | true  because ofʸ q = just $ l″ , here refl , q , p

clauseCheck₃ : ∀ is a f l ls c → eval a f ≡ true → Maybe (evalᶜ a (resolvent l (l ∷ˡ ls) c) ≡ true)
clauseCheck₃ is a f l ls c p
  with q ← checkRUP is a f (resolvent l (l ∷ˡ ls) c)
  rewrite p
  = mapᵐ sym {!!}

satisfiable′ : ∀ n a f t l ls → eval a f ≡ true → eval′ n a t ≡ true →
  evalᶜ a (l ∷ˡ ls) ≡ false → Maybe (eval′ n (forceTrue a l) t ≡ true)
satisfiable′ zero    _ _ nothing             _ _  _  _  _  = just refl
satisfiable′ zero    a f (just (leaf c))     l ls p₁ p₂ p₃
  with clauseCheck₁ l c
... | just q = just $ clauseTrue₁ a c l p₂ q
... | nothing
  with clauseCheck₂ ls c l
... | just (l′ , r₁ , r₂ , r₃) = just $ clauseTrue₂ a l ls c l′ p₃ r₁ r₂ r₃
... | nothing
  with clauseCheck₃ {!!} a f l ls c p₁
... | just s = just $ clauseTrue₃ a l ls c p₃ s
... | nothing = nothing
satisfiable′ (suc n) _ _ nothing             _ _  _  _  _ = just refl
satisfiable′ (suc n) a f (just (node fˡ fʳ)) l ls p₁ p₂ p₃
  with q₁ , q₂ ← ∧-trueSplit (eval′ n a fˡ) (eval′ n a fʳ) p₂
  with satisfiable′ n a f fˡ l ls p₁ q₁ p₃
... | nothing = nothing
... | just r₁
  with satisfiable′ n a f fʳ l ls p₁ q₂ p₃
... | nothing = nothing
... | just r₂ = just $ ∧-trueJoin (eval′ n (forceTrue a l) fˡ) (eval′ n (forceTrue a l) fʳ) r₁ r₂

satisfiable : ∀ a l ls f → evalᶜ a (l ∷ˡ ls) ≡ false → eval a f ≡ true →
  Maybe (eval (forceTrue a l) f ∧ evalᶜ (forceTrue a l) (l ∷ˡ ls) ≡ true)
satisfiable a l ls f p₁ p₂
  with satisfiable′ bitsᶜ a f f l ls p₂ p₂ p₁
... | nothing = nothing
... | just q  rewrite q | forceTrueForces a l = just refl
-}

postulate
  checkRAT : (f : Formula) → (lᶜ : Literal) → (lsᶜ : Clause) → (is : List Index) →
    Maybe (∀ a → eval a f ≡ true → evalᶜ a (lᶜ ∷ˡ lsᶜ) ≡ false →
      let a′ = forceTrue a lᶜ in eval a′ f ∧ evalᶜ a′ (lᶜ ∷ˡ lsᶜ) ≡ true)

∀-∧-false : (f : Formula) → (∀ a → eval a f ≡ eval a f ∧ false) → ∀ a → eval a f ≡ false
∀-∧-false f p a = begin
  eval a f         ≡⟨ p a ⟩
  eval a f ∧ false ≡⟨ ∧-zeroʳ (eval a f) ⟩
  false            ∎

checkLRAT : (f : Formula) → Proof → Maybe (∀ a → eval a f ≡ false)

RUPStep : (f : Formula) → (c : Clause) → Proof →
  (∀ a → eval a f ≡ eval a f ∧ evalᶜ a c) → Maybe (∀ a → eval a f ≡ false)
RUPStep f []ˡ         _  p = just $ ∀-∧-false f p
RUPStep f (lᶜ ∷ˡ lsᶜ) ss p
  with nextIndex f | inspect nextIndex f
... | nothing | _      = nothing
... | just i  | [ eq ]
  with checkLRAT (insert f i (lᶜ ∷ˡ lsᶜ)) ss
... | nothing = nothing
... | just q  =
  let r = append⇒∧ f i (lᶜ ∷ˡ lsᶜ) eq in
  just $ λ a → trans (trans (p a) (sym (r a))) (q a)

RATStep′ : (f : Formula) → (c : Clause) → (lᶜ : Literal) → (lsᶜ : Clause) →
  (∀ a → eval a f ∧ evalᶜ a (lᶜ ∷ˡ lsᶜ) ≡ eval a f ∧ evalᶜ a c) →
  (∀ a → eval a f ≡ true → evalᶜ a (lᶜ ∷ˡ lsᶜ) ≡ false →
    let a′ = forceTrue a lᶜ in eval a′ f ∧ evalᶜ a′ (lᶜ ∷ˡ lsᶜ) ≡ true) →
  (∀ a → eval a f ∧ evalᶜ a c ≡ false) →
  ∀ a → eval a f ≡ false
RATStep′ f c lᶜ lsᶜ p q r a
  with evalᶜ a (lᶜ ∷ˡ lsᶜ) | inspect (evalᶜ a) (lᶜ ∷ˡ lsᶜ)
... | true  | [ eq₁ ] = begin
  eval a f                              ≡⟨ sym $ ∧-identityʳ (eval a f) ⟩
  eval a f ∧ true                       ≡⟨ cong (eval a f ∧_) $ sym eq₁ ⟩
  eval a f ∧ (evalˡ a lᶜ ∨ evalᶜ a lsᶜ) ≡⟨ p a ⟩
  eval a f ∧ evalᶜ a c                  ≡⟨ r a ⟩
  false                                 ∎
... | false | [ eq₁ ]
  with eval a f | inspect (eval a) f
... | false | _       = refl
... | true  | [ eq₂ ] =
  let s = q a eq₂ eq₁ in
  let a′ = forceTrue a lᶜ in
  trans (sym s) (subst (_≡ false) (sym $ p a′) (r a′))

RATStep : (f : Formula) → (c : Clause) → (lᶜ : Literal) → (lsᶜ : Clause) → Proof →
  (∀ a → eval a f ∧ evalᶜ a (lᶜ ∷ˡ lsᶜ) ≡ eval a f ∧ evalᶜ a c) →
  (∀ a → eval a f ≡ true → evalᶜ a (lᶜ ∷ˡ lsᶜ) ≡ false →
    let a′ = forceTrue a lᶜ in eval a′ f ∧ evalᶜ a′ (lᶜ ∷ˡ lsᶜ) ≡ true) →
  Maybe (∀ a → eval a f ≡ false)
RATStep f c lᶜ lsᶜ ss p q
  with nextIndex f | inspect nextIndex f
... | nothing | _       = nothing
... | just i  | [ eq ]
  with checkLRAT (insert f i c) ss
... | nothing = nothing
... | just r =
  let s = append⇒∧ f i c eq in
  let t = λ a → trans (sym $ s a) (r a) in
  just $ RATStep′ f c lᶜ lsᶜ p q t

checkLRAT _ []ˡ                  = nothing
checkLRAT f (del _ ∷ˡ ss)        = checkLRAT f ss -- skip delete steps for now
checkLRAT f (ext c is iss ∷ˡ ss)
  with checkRUP f c is
... | fail             = nothing
... | done p           = RUPStep f c ss p
... | more []ˡ         = nothing
... | more (lᶜ ∷ˡ lsᶜ)
  with checkRAT f lᶜ lsᶜ is
... | nothing = nothing
... | just p  = RATStep f c lᶜ lsᶜ ss {!!} p

module Test where
  v₀ : Variable
  v₀ = false ∷ᵛ []ᵛ
  v₁ : Variable
  v₁ = false ∷ᵛ []ᵛ

  c₀ : Clause
  c₀ = neg v₀ ∷ˡ pos v₁ ∷ˡ []ˡ
  c₁ : Clause
  c₁ = pos v₀ ∷ˡ neg v₁ ∷ˡ []ˡ

  i₀ : Index
  i₀ = false ∷ᵛ []ᵛ
  i₁ : Index
  i₁ = false ∷ᵛ []ᵛ

  f : Formula
  f = just $ node (just $ leaf c₀) (just $ leaf c₁)

{-
insertLemma : ∀ n a f i c → evalᶜ a c ≡ true → eval′ n a (insert′ n f i c) ≡ false →
  eval′ n a f ≡ false

insertLemma zero    _ _                 []ᵛ           _ p₁ p₂ = contradiction p₁ (not-¬ p₂)

insertLemma (suc n) a nothing           (false ∷ᵛ is) c p₁ p₂
  rewrite ∧-identityʳ (eval′ n a (insert′ n nothing is c))
  = contradiction (insertEmpty n a is c p₁) (not-¬ p₂)

insertLemma (suc n) a nothing           (true ∷ᵛ is)  c p₁ p₂ =
  contradiction (insertEmpty n a is c p₁) (not-¬ p₂)

insertLemma (suc n) a (just (node l r)) (false ∷ᵛ is) c p₁ p₂ with eval′ n a r
... | true rewrite ∧-identityʳ (eval′ n a l)
                 | ∧-identityʳ (eval′ n a (insert′ n l is c))
           = insertLemma n a l is c p₁ p₂

... | false = ∧-zeroʳ (eval′ n a l)

insertLemma (suc n) a (just (node l r)) (true ∷ᵛ is)  c p₁ p₂ with eval′ n a l
... | true = insertLemma n a r is c p₁ p₂
... | false = refl

removeLemma : ∀ n a f i → eval′ n a (remove′ n f i) ≡ false → eval′ n a f ≡ false
removeLemma zero    _ nothing           []ᵛ           p = p
removeLemma zero    _ (just (leaf c))   []ᵛ           p = case p of λ ()
removeLemma (suc n) _ nothing           (_ ∷ᵛ _)      p = p

removeLemma (suc n) a (just (node l r)) (false ∷ᵛ is) p with eval′ n a r
... | true rewrite ∧-identityʳ (eval′ n a l)
                 | ∧-identityʳ (eval′ n a (remove′ n l is))
           = removeLemma n a l is p

... | false = ∧-zeroʳ (eval′ n a l)

removeLemma (suc n) a (just (node l r)) (true ∷ᵛ is)  p with eval′ n a l
... | true = removeLemma n a r is p
... | false = refl
-}
