import Data.Nat

module LRAT (bitsᵛ : Data.Nat.ℕ) (bitsᶜ : Data.Nat.ℕ) where

open Data.Nat using (ℕ ; zero ; suc)

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not)
open import Data.Bool.Properties
  using (
      ∧-zeroʳ ; ∧-identityʳ ; ∨-identityʳ ; ∧-comm ; ∧-assoc ; ∧-idem ;
      ∧-distribʳ-∨ ; ∧-distribˡ-∨ ; ∧-inverseʳ ; ∨-∧-booleanAlgebra ; not-¬
    )
  renaming (_≟_ to _≟ᵇ_)
open import Data.List using (List) renaming ([] to []ˡ ; _∷_ to _∷ˡ_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec using (Vec) renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_)
open import Data.Vec.Properties using () renaming (≡-dec to ≡-decᵛ)
open import Function using (_$_ ; _∘_ ; case_of_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; inspect ; [_] ; cong ; subst)
open import Relation.Nullary using (Dec ; _because_ ; ofʸ ; ofⁿ)
open import Relation.Nullary.Negation using (contradiction)

open import Algebra.Properties.BooleanAlgebra ∨-∧-booleanAlgebra using (deMorgan₁ ; deMorgan₂)

data Variable : Set where
  var : Vec Bool bitsᵛ → Variable

Assignment = Variable → Bool

data Literal : Set where
  pos : Variable → Literal
  neg : Variable → Literal

Clause = List Literal

data Trie : ℕ → Set where
  leaf : Clause → Trie 0
  node : {n : ℕ} → Maybe (Trie n) → Maybe (Trie n) → Trie (suc n)

Formula = Maybe (Trie bitsᶜ)
Index = Vec Bool bitsᶜ

flip : Literal → Literal
flip (pos v) = neg v
flip (neg v) = pos v

evalˡ : Assignment → Literal → Bool
evalˡ a (pos v) = a v
evalˡ a (neg v) = not (a v)

evalᶜ : Assignment → Clause → Bool
evalᶜ a []ˡ       = false
evalᶜ a (l ∷ˡ ls) = evalˡ a l ∨ evalᶜ a ls

eval′ : (n : ℕ) → Assignment → Maybe (Trie n) → Bool
eval′ _       _ nothing           = true
eval′ zero    a (just (leaf c))   = evalᶜ a c
eval′ (suc n) a (just (node l r)) = eval′ n a l ∧ eval′ n a r

eval : Assignment → Formula → Bool
eval a f = eval′ bitsᶜ a f

evalOne′ : (n : ℕ) → Assignment → Maybe (Trie n) → Vec Bool n → Bool
evalOne′ _       _ nothing           _             = true
evalOne′ zero    a (just (leaf c))   []ᵛ           = evalᶜ a c
evalOne′ (suc n) a (just (node l _)) (false ∷ᵛ is) = evalOne′ n a l is
evalOne′ (suc n) a (just (node _ r)) (true ∷ᵛ is)  = evalOne′ n a r is

evalOne : Assignment → Formula → Index → Bool
evalOne a f i = evalOne′ bitsᶜ a f i

insert′ : (n : ℕ) → Maybe (Trie n) → Vec Bool n → Clause → Maybe (Trie n)
insert′ zero    _                 []ᵛ            c = just (leaf c)
insert′ (suc n) nothing           (false ∷ᵛ cs′) c = just (node (insert′ n nothing cs′ c) nothing)
insert′ (suc n) nothing           (true ∷ᵛ cs′)  c = just (node nothing (insert′ n nothing cs′ c))
insert′ (suc n) (just (node l r)) (false ∷ᵛ cs′) c = just (node (insert′ n l cs′ c) r)
insert′ (suc n) (just (node l r)) (true ∷ᵛ cs′)  c = just (node l (insert′ n r cs′ c))

insert : Formula → Index → Clause → Formula
insert f i c = insert′ bitsᶜ f i c

remove′ : (n : ℕ) → Maybe (Trie n) → Vec Bool n → Maybe (Trie n)
remove′ zero    _                 []ᵛ            = nothing
remove′ (suc n) nothing           (_ ∷ᵛ _)       = nothing
remove′ (suc n) (just (node l r)) (false ∷ᵛ cs′) = just (node (remove′ n l cs′) r)
remove′ (suc n) (just (node l r)) (true ∷ᵛ cs′)  = just (node l (remove′ n r cs′))

remove : Formula → Index → Formula
remove f i = remove′ bitsᶜ f i

duplicateL′ : ∀ n a f i → eval′ n a f ≡ eval′ n a f ∧ evalOne′ n a f i
duplicateL′ zero    _ nothing           []ᵛ           = refl
duplicateL′ zero    a (just (leaf c))   []ᵛ           = sym $ ∧-idem (evalᶜ a c)
duplicateL′ (suc n) _ nothing           (_ ∷ᵛ _)      = refl

duplicateL′ (suc n) a (just (node l r)) (false ∷ᵛ is)
  rewrite ∧-comm (eval′ n a l) (eval′ n a r)
        | ∧-assoc (eval′ n a r) (eval′ n a l) (evalOne′ n a l is)
        | sym $ duplicateL′ n a l is
  = refl

duplicateL′ (suc n) a (just (node l r)) (true ∷ᵛ is)
  rewrite ∧-assoc (eval′ n a l) (eval′ n a r) (evalOne′ n a r is)
        | sym $ duplicateL′ n a r is
  = refl

duplicateL : ∀ a f i → eval a f ≡ eval a f ∧ evalOne a f i
duplicateL a f i = duplicateL′ bitsᶜ a f i

infix 4 _≟ᵛ_ _≟ˡ_

_≟ᵛ_ : (v₁ v₂ : Vec Bool bitsᵛ) → Dec (v₁ ≡ v₂)
_≟ᵛ_ = ≡-decᵛ _≟ᵇ_

_≟ˡ_ : (l₁ l₂ : Literal) → Dec (l₁ ≡ l₂)
pos (var v₁) ≟ˡ pos (var v₂) with v₁ ≟ᵛ v₂
... | true  because ofʸ refl = true  because ofʸ refl

... | false because ofⁿ p = false because ofⁿ (p ∘ posVarInj v₁ v₂)
  where
  posVarInj : (v₁ v₂ : Vec Bool bitsᵛ) → pos (var v₁) ≡ pos (var v₂) → v₁ ≡ v₂
  posVarInj v₁ v₂ refl = refl

pos _ ≟ˡ neg _ = false because ofⁿ λ ()
neg _ ≟ˡ pos _ = false because ofⁿ λ ()

neg (var v₁) ≟ˡ neg (var v₂) with v₁ ≟ᵛ v₂
... | true  because ofʸ refl = true  because ofʸ refl

... | false because ofⁿ p = false because ofⁿ (p ∘ negVarInj v₁ v₂)
  where
  negVarInj : (v₁ v₂ : Vec Bool bitsᵛ) → neg (var v₁) ≡ neg (var v₂) → v₁ ≡ v₂
  negVarInj v₁ v₂ refl = refl

removeLiteral : (c : Clause) → (l : Literal) → Clause
removeLiteral []ˡ         _ = []ˡ
removeLiteral (l′ ∷ˡ ls′) l with l′ ≟ˡ l
... | true  because ofʸ _ = removeLiteral ls′ l
... | false because ofⁿ _ = l′ ∷ˡ removeLiteral ls′ l

removeLiteralL : ∀ a c l →
  evalᶜ a c ∧ not (evalˡ a l) ≡ evalᶜ a (removeLiteral c l) ∧ not (evalˡ a l)

removeLiteralL a []ˡ         _ = refl

removeLiteralL a (l′ ∷ˡ ls′) l with l′ ≟ˡ l
... | true because ofʸ refl
  rewrite ∧-distribʳ-∨ (not (evalˡ a l′)) (evalˡ a l′) (evalᶜ a ls′)
        | ∧-inverseʳ (evalˡ a l′) = removeLiteralL a ls′ l′

... | false because ofⁿ _
  rewrite ∧-distribʳ-∨ (not (evalˡ a l)) (evalˡ a l′) (evalᶜ a (removeLiteral ls′ l))
        | ∧-distribʳ-∨ (not (evalˡ a l)) (evalˡ a l′) (evalᶜ a ls′)
        | sym $ removeLiteralL a ls′ l
  = refl

andNot : (c₁ c₂ : Clause) → Clause
andNot c₁ []ˡ       = c₁
andNot c₁ (l ∷ˡ ls) = andNot (removeLiteral c₁ l) ls

andNotL : ∀ a c₁ c₂ → evalᶜ a c₁ ∧ not (evalᶜ a c₂) ≡ evalᶜ a (andNot c₁ c₂) ∧ not (evalᶜ a c₂)
andNotL a c₁ []ˡ = refl
andNotL a c₁ (l ∷ˡ ls)
  rewrite deMorgan₂ (evalˡ a l) (evalᶜ a ls)
        | sym $ ∧-assoc (evalᶜ a c₁) (not (evalˡ a l)) (not (evalᶜ a ls))
        | removeLiteralL a c₁ l
        | ∧-assoc (evalᶜ a (removeLiteral c₁ l)) (not (evalˡ a l)) (not (evalᶜ a ls))
        | ∧-comm (not (evalˡ a l)) (not (evalᶜ a ls))
        | sym $ ∧-assoc (evalᶜ a (removeLiteral c₁ l)) (not (evalᶜ a ls)) (not (evalˡ a l))
        | sym $ ∧-assoc (evalᶜ a (andNot (removeLiteral c₁ l) ls)) (not (evalᶜ a ls)) (not (evalˡ a l))
        | andNotL a (removeLiteral c₁ l) ls
  = refl

notNotL : ∀ b → not (not b) ≡ b
notNotL true  = refl
notNotL false = refl

flipL : ∀ a l → evalˡ a (flip l) ≡ not (evalˡ a l)
flipL a (pos v) = refl
flipL a (neg v) = sym $ notNotL (a v)

pushUnitL : ∀ a l c → evalᶜ a (l ∷ˡ []ˡ) ∧ not (evalᶜ a c) ≡ not (evalᶜ a (flip l ∷ˡ c))
pushUnitL a l []ˡ
  rewrite ∨-identityʳ (evalˡ a l)
        | ∨-identityʳ (evalˡ a (flip l))
        | ∧-identityʳ (evalˡ a l)
  with l
... | neg v = refl
... | pos v = sym $ notNotL (a v)

pushUnitL a l (l′ ∷ˡ ls′)
  rewrite deMorgan₂ (evalˡ a (flip l)) (evalˡ a l′ ∨ evalᶜ a ls′)
        | flipL a l
        | notNotL (evalˡ a l)
        | ∨-identityʳ (evalˡ a l)
  = refl

emptyFalseL : ∀ a f c → eval a f ∧ evalᶜ a []ˡ ∧ evalᶜ a c ≡ false
emptyFalseL a f c = ∧-zeroʳ (eval a f)

contradictL : ∀ a f c → eval a f ∧ not (evalᶜ a c) ≡ false → eval a f ≡ false ⊎ evalᶜ a c ≡ true
contradictL a f c p with eval a f
... | true  = inj₂ $ subst (_≡ true) (notNotL (evalᶜ a c)) (cong not p)
... | false = inj₁ p

rupL′ : ∀ a f c → eval a f ≡ false ⊎ evalᶜ a c ≡ true → eval a f ≡ eval a f ∧ evalᶜ a c
rupL′ a f c (inj₁ p) rewrite p = refl
rupL′ a f c (inj₂ p) rewrite p = sym $ ∧-identityʳ (eval a f)

nextIndex′ : (n : ℕ) → Maybe (Trie n) → Maybe (Vec Bool n)
nextIndex′ zero    nothing = just []ᵛ
nextIndex′ zero    (just _) = nothing

nextIndex′ (suc n) nothing with nextIndex′ n nothing
... | just i  = just $ false ∷ᵛ i
... | nothing = nothing

nextIndex′ (suc n) (just (node l r)) with nextIndex′ n l
... | just i  = just $ false ∷ᵛ i
... | nothing with nextIndex′ n r
... | just i  = just $ true ∷ᵛ i
... | nothing = nothing

nextIndex : Formula → Maybe Index
nextIndex f = nextIndex′ bitsᶜ f

nextIndexLeftL′ : (n : ℕ) → (l r : Maybe (Trie n)) → (i : Vec Bool n) →
  nextIndex′ (suc n) (just (node l r)) ≡ just (false ∷ᵛ i) → nextIndex′ n l ≡ just i

nextIndexLeftL′ n l r i p
  with nextIndex′ n l
... | just i′ = case p of λ { refl → refl }
... | nothing
  with nextIndex′ n r
... | just i′ = case p of λ ()
... | nothing = case p of λ ()

nextIndexRightL′ : (n : ℕ) → (l r : Maybe (Trie n)) → (i : Vec Bool n) →
  nextIndex′ (suc n) (just (node l r)) ≡ just (true ∷ᵛ i) → nextIndex′ n r ≡ just i

nextIndexRightL′ n l r i p
  with nextIndex′ n l
... | just i′ = case p of λ ()
... | nothing
  with nextIndex′ n r
... | just i′ = case p of λ { refl → refl }
... | nothing = case p of λ ()

insertEmptyL′ : ∀ n a i c → eval′ n a (insert′ n nothing i c) ≡ evalᶜ a c
insertEmptyL′ zero _ []ᵛ _ = refl

insertEmptyL′ (suc n) a (false ∷ᵛ is) c
  rewrite ∧-identityʳ (eval′ n a (insert′ n nothing is c))
  = insertEmptyL′ n a is c

insertEmptyL′ (suc n) a (true ∷ᵛ is) c = insertEmptyL′ n a is c

appendL′ : ∀ n mt i c a → nextIndex′ n mt ≡ just i →
  eval′ n a (insert′ n mt i c) ≡ eval′ n a mt ∧ evalᶜ a c

appendL′ zero    nothing []ᵛ       _ _ _ = refl
appendL′ (suc n) nothing (i ∷ᵛ is) c a p = insertEmptyL′ (suc n) a (i ∷ᵛ is) c

appendL′ (suc n) (just (node l r)) (false ∷ᵛ is) c a p
  rewrite appendL′ n l is c a (nextIndexLeftL′ n l r is p)
        | ∧-assoc (eval′ n a l) (evalᶜ a c) (eval′ n a r)
        | ∧-assoc (eval′ n a l) (eval′ n a r) (evalᶜ a c)
        | ∧-comm (eval′ n a r) (evalᶜ a c)
  = refl

appendL′ (suc n) (just (node l r)) (true ∷ᵛ is)  c a p
  rewrite appendL′ n r is c a (nextIndexRightL′ n l r is p)
  = sym $ ∧-assoc (eval′ n a l) (eval′ n a r) (evalᶜ a c)

appendL : ∀ f i c a → nextIndex f ≡ just i → eval a (insert f i c) ≡ eval a f ∧ evalᶜ a c
appendL f i c a p = appendL′ bitsᶜ f i c a p

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
