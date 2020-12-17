import Data.Nat

module LRAT (bitsᵛ : Data.Nat.ℕ) (bitsᶜ : Data.Nat.ℕ) where

open Data.Nat using (ℕ ; zero ; suc)

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; if_then_else_)
open import Data.Bool.Properties
  using (
      ∧-zeroʳ ; ∨-zeroʳ ; ∧-identityʳ ; ∨-identityʳ ; ∧-comm ; ∨-comm ; ∧-assoc ; ∨-assoc ;
      ∧-idem ; ∧-distribʳ-∨ ; ∧-distribˡ-∨ ; ∧-inverseʳ ; ∨-∧-booleanAlgebra ; not-¬
    )
  renaming (_≟_ to _≟ᵇ_)
open import Data.List using (List) renaming ([] to []ˡ ; _∷_ to _∷ˡ_ ; _++_ to _++ˡ_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ ; _∷_ to _∷ᵃ_)
open import Data.List.Relation.Unary.Any using (Any ; here ; there)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec using (Vec) renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_)
open import Data.Vec.Properties using () renaming (≡-dec to ≡-decᵛ)
open import Function using (_$_ ; _∘_ ; case_of_)
open import Level using (0ℓ)
open import Relation.Binary using (DecSetoid)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; ≢-sym ; inspect ; [_] ; cong ; subst ; decSetoid)
open import Relation.Nullary using (Dec ; _because_ ; ofʸ ; ofⁿ)
open import Relation.Nullary.Negation using (contradiction)

open import Algebra.Properties.BooleanAlgebra ∨-∧-booleanAlgebra using (deMorgan₁ ; deMorgan₂)

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

++ˡ⇒∨ : ∀ a c₁ c₂ → evalᶜ a (c₁ ++ˡ c₂) ≡ evalᶜ a c₁ ∨ evalᶜ a c₂
++ˡ⇒∨ _ []ˡ       _  = refl
++ˡ⇒∨ a (l ∷ˡ ls) c₂ rewrite ∨-assoc (evalˡ a l) (evalᶜ a ls) (evalᶜ a c₂) | ++ˡ⇒∨ a ls c₂ = refl

false-++ˡ : ∀ a c₁ c₂ → evalᶜ a c₁ ≡ false → evalᶜ a (c₁ ++ˡ c₂) ≡ evalᶜ a c₂
false-++ˡ a c₁ c₂ p rewrite ++ˡ⇒∨ a c₁ c₂ | p = refl

evalTrueStep′ : ∀ n a l r → eval′ (suc n) a (just (node l r)) ≡ true →
  eval′ n a l ≡ true × eval′ n a r ≡ true
evalTrueStep′ n a l r p
  with eval′ n a l
... | false = case p of λ ()
... | true
  with eval′ n a r
... | false = case p of λ ()
... | true  = refl , refl

flip : Literal → Literal
flip (pos v) = neg v
flip (neg v) = pos v

notNot : ∀ b → not (not b) ≡ b
notNot true  = refl
notNot false = refl

flipNot : ∀ a l → evalˡ a (flip l) ≡ not (evalˡ a l)
flipNot a (pos v) = refl
flipNot a (neg v) = sym $ notNot (a v)

flipInjective : ∀ {l l′} → flip l ≡ flip l′ → l ≡ l′
flipInjective {pos _} {pos _} refl = refl
flipInjective {neg _} {neg _} refl = refl

∨-falseSplit : ∀ x y → x ∨ y ≡ false → x ≡ false × y ≡ false
∨-falseSplit false false refl = refl , refl

∨-trueSplit : ∀ x y → x ∨ y ≡ true → x ≡ true ⊎ y ≡ true
∨-trueSplit false _ refl = inj₂ refl
∨-trueSplit true  _ refl = inj₁ refl

∨-trueExtend : ∀ {x} y → x ≡ true → x ∨ y ≡ true
∨-trueExtend _ refl = refl

∨-falseStrip : ∀ x y z → x ∨ y ∨ z ≡ false → x ∨ z ≡ false
∨-falseStrip x true  _ p rewrite ∨-zeroʳ x = case p of λ ()
∨-falseStrip _ false _ p = p

anyLiteralTrue : ∀ a l c → evalˡ a l ≡ true → l ∈ c → evalᶜ a c ≡ true
anyLiteralTrue a l (l′ ∷ˡ ls′) p₁ (here refl) rewrite p₁ = refl
anyLiteralTrue a l (l′ ∷ˡ ls′) p₁ (there p₂)
  rewrite anyLiteralTrue a l ls′ p₁ p₂ = ∨-zeroʳ (evalˡ a l′)

allLiteralsFalse : ∀ a c → evalᶜ a c ≡ false → All (λ l → evalˡ a l ≡ false) c
allLiteralsFalse _ []ˡ       _ = []ᵃ
allLiteralsFalse a (l ∷ˡ ls) p
  with q₁ , q₂ ← ∨-falseSplit (evalˡ a l) (evalᶜ a ls) p
  = q₁ ∷ᵃ allLiteralsFalse a ls q₂

allFlippedTrue : ∀ a c → evalᶜ a c ≡ false → All (λ l → evalˡ a (flip l) ≡ true) c
allFlippedTrue _ []ˡ       _ = []ᵃ
allFlippedTrue a (l ∷ˡ ls) p
  with q₁ , q₂ ← ∨-falseSplit (evalˡ a l) (evalᶜ a ls) p
  = subst (λ # → evalˡ a (flip l) ≡ #) (cong not q₁) (flipNot a l) ∷ᵃ allFlippedTrue a ls q₂

duplicate′ : ∀ n a f i → eval′ n a f ≡ eval′ n a f ∧ evalOne′ n a f i
duplicate′ zero    _ nothing           []ᵛ           = refl
duplicate′ zero    a (just (leaf c))   []ᵛ           = sym $ ∧-idem (evalᶜ a c)
duplicate′ (suc n) _ nothing           (_ ∷ᵛ _)      = refl
duplicate′ (suc n) a (just (node l r)) (false ∷ᵛ is)
  rewrite ∧-comm (eval′ n a l) (eval′ n a r)
        | ∧-assoc (eval′ n a r) (eval′ n a l) (evalOne′ n a l is)
        | sym $ duplicate′ n a l is
  = refl
duplicate′ (suc n) a (just (node l r)) (true ∷ᵛ is)
  rewrite ∧-assoc (eval′ n a l) (eval′ n a r) (evalOne′ n a r is)
        | sym $ duplicate′ n a r is
  = refl

duplicate : ∀ a f i → eval a f ≡ eval a f ∧ evalOne a f i
duplicate a f i = duplicate′ bitsᶜ a f i

removeLiteral : (c : Clause) → (l : Literal) → Clause
removeLiteral []ˡ         _ = []ˡ
removeLiteral (l′ ∷ˡ ls′) l with l′ ≟ˡ l
... | true  because ofʸ _ = removeLiteral ls′ l
... | false because ofⁿ _ = l′ ∷ˡ removeLiteral ls′ l

removeLiteralBool : ∀ a c l →
  evalᶜ a c ∧ not (evalˡ a l) ≡ evalᶜ a (removeLiteral c l) ∧ not (evalˡ a l)
removeLiteralBool a []ˡ         _ = refl
removeLiteralBool a (l′ ∷ˡ ls′) l with l′ ≟ˡ l
... | true  because ofʸ refl
  rewrite ∧-distribʳ-∨ (not (evalˡ a l′)) (evalˡ a l′) (evalᶜ a ls′)
        | ∧-inverseʳ (evalˡ a l′) = removeLiteralBool a ls′ l′
... | false because ofⁿ _
  rewrite ∧-distribʳ-∨ (not (evalˡ a l)) (evalˡ a l′) (evalᶜ a (removeLiteral ls′ l))
        | ∧-distribʳ-∨ (not (evalˡ a l)) (evalˡ a l′) (evalᶜ a ls′)
        | sym $ removeLiteralBool a ls′ l
  = refl

removeLiteralFalse : ∀ a c l → evalᶜ a c ≡ false → evalᶜ a (removeLiteral c l) ≡ false
removeLiteralFalse _ []ˡ         _ _ = refl
removeLiteralFalse a (l′ ∷ˡ ls′) l p
  with (q ∷ᵃ qs) ← allLiteralsFalse a (l′ ∷ˡ ls′) p
  with l′ ≟ˡ l
... | true  because ofʸ r rewrite q = removeLiteralFalse a ls′ l p
... | false because ofⁿ r rewrite q = removeLiteralFalse a ls′ l p

removeLiteralTrue : ∀ a c l → evalᶜ a (removeLiteral c l) ≡ true → evalᶜ a c ≡ true
removeLiteralTrue a (l′ ∷ˡ ls′) l p
  with l′ ≟ˡ l
... | true  because ofʸ _ rewrite removeLiteralTrue a ls′ l p = ∨-zeroʳ (evalˡ a l′)
... | false because ofⁿ q
  with ∨-trueSplit (evalˡ a l′) (evalᶜ a (removeLiteral ls′ l)) p
... | inj₁ r rewrite r = refl
... | inj₂ r rewrite removeLiteralTrue a ls′ l r = ∨-zeroʳ (evalˡ a l′)

removeLiteral-∉ : ∀ l c → l ∉ removeLiteral c l
removeLiteral-∉ l []ˡ         = λ ()
removeLiteral-∉ l (l′ ∷ˡ ls′)
  with l′ ≟ˡ l
... | true  because ofʸ _ = removeLiteral-∉ l ls′
... | false because ofⁿ p = λ where
  (here q)  → contradiction (sym q) p
  (there q) → contradiction q (removeLiteral-∉ l ls′)

resolvent : Literal → Clause → Clause → Clause
resolvent l c₁ c₂ = removeLiteral c₁ l ++ˡ removeLiteral c₂ (flip l)

resolventTrue : ∀ a l c₁ c₂ → evalᶜ a c₁ ≡ false → evalᶜ a (resolvent l c₁ c₂) ≡ true →
  evalᶜ a (removeLiteral c₂ (flip l)) ≡ true
resolventTrue _ _ []ˡ         _  _  p₂ = p₂
resolventTrue a l (l′ ∷ˡ ls′) c₂ p₁ p₂
  with q₁ , q₂ ← ∨-falseSplit (evalˡ a l′) (evalᶜ a ls′) p₁
  with r ← removeLiteralFalse a ls′ l q₂
  with s ← false-++ˡ a (removeLiteral ls′ l) (removeLiteral c₂ (flip l)) r
  with l′ ≟ˡ l
... | true  because ofʸ z rewrite s = p₂
... | false because ofⁿ z rewrite q₁ | s = p₂

andNot : (c₁ c₂ : Clause) → Clause
andNot c₁ []ˡ       = c₁
andNot c₁ (l ∷ˡ ls) = andNot (removeLiteral c₁ l) ls

andNotBool : ∀ a c₁ c₂ → evalᶜ a c₁ ∧ not (evalᶜ a c₂) ≡ evalᶜ a (andNot c₁ c₂) ∧ not (evalᶜ a c₂)
andNotBool a c₁ []ˡ       = refl
andNotBool a c₁ (l ∷ˡ ls)
  rewrite deMorgan₂ (evalˡ a l) (evalᶜ a ls)
        | sym $ ∧-assoc (evalᶜ a c₁) (not (evalˡ a l)) (not (evalᶜ a ls))
        | removeLiteralBool a c₁ l
        | ∧-assoc (evalᶜ a (removeLiteral c₁ l)) (not (evalˡ a l)) (not (evalᶜ a ls))
        | ∧-comm (not (evalˡ a l)) (not (evalᶜ a ls))
        | sym $ ∧-assoc (evalᶜ a (removeLiteral c₁ l)) (not (evalᶜ a ls)) (not (evalˡ a l))
        | sym $ ∧-assoc (evalᶜ a (andNot (removeLiteral c₁ l) ls)) (not (evalᶜ a ls)) (not (evalˡ a l))
        | andNotBool a (removeLiteral c₁ l) ls
  = refl

pushUnit : ∀ a l c → evalᶜ a (l ∷ˡ []ˡ) ∧ not (evalᶜ a c) ≡ not (evalᶜ a (flip l ∷ˡ c))
pushUnit a l []ˡ
  rewrite ∨-identityʳ (evalˡ a l)
        | ∨-identityʳ (evalˡ a (flip l))
        | ∧-identityʳ (evalˡ a l)
  with l
... | neg v = refl
... | pos v = sym $ notNot (a v)
pushUnit a l (l′ ∷ˡ ls′)
  rewrite deMorgan₂ (evalˡ a (flip l)) (evalˡ a l′ ∨ evalᶜ a ls′)
        | flipNot a l
        | notNot (evalˡ a l)
        | ∨-identityʳ (evalˡ a l)
  = refl

emptyFalse : ∀ a f c → eval a f ∧ evalᶜ a []ˡ ∧ evalᶜ a c ≡ false
emptyFalse a f c = ∧-zeroʳ (eval a f)

clauseImplied : ∀ a f c → eval a f ∧ not (evalᶜ a c) ≡ false → eval a f ≡ false ⊎ evalᶜ a c ≡ true
clauseImplied a f c p with eval a f
... | true  = inj₂ $ subst (_≡ true) (notNot (evalᶜ a c)) (cong not p)
... | false = inj₁ p

rupL′ : ∀ a f c → eval a f ≡ false ⊎ evalᶜ a c ≡ true → eval a f ≡ eval a f ∧ evalᶜ a c
rupL′ a f c (inj₁ p) rewrite p = refl
rupL′ a f c (inj₂ p) rewrite p = sym $ ∧-identityʳ (eval a f)

nextIndex′ : (n : ℕ) → Maybe (Trie n) → Maybe (Vec Bool n)
nextIndex′ zero    nothing           = just []ᵛ
nextIndex′ zero    (just _)          = nothing
nextIndex′ (suc n) nothing           with nextIndex′ n nothing
... | just i  = just $ false ∷ᵛ i
... | nothing = nothing
nextIndex′ (suc n) (just (node l r)) with nextIndex′ n l
... | just i  = just $ false ∷ᵛ i
... | nothing with nextIndex′ n r
... | just i  = just $ true ∷ᵛ i
... | nothing = nothing

nextIndex : Formula → Maybe Index
nextIndex f = nextIndex′ bitsᶜ f

nextIndexLeft′ : (n : ℕ) → (l r : Maybe (Trie n)) → (i : Vec Bool n) →
  nextIndex′ (suc n) (just (node l r)) ≡ just (false ∷ᵛ i) → nextIndex′ n l ≡ just i
nextIndexLeft′ n l r i p
  with nextIndex′ n l
... | just i′ = case p of λ { refl → refl }
... | nothing
  with nextIndex′ n r
... | just i′ = case p of λ ()
... | nothing = case p of λ ()

nextIndexRight′ : (n : ℕ) → (l r : Maybe (Trie n)) → (i : Vec Bool n) →
  nextIndex′ (suc n) (just (node l r)) ≡ just (true ∷ᵛ i) → nextIndex′ n r ≡ just i
nextIndexRight′ n l r i p
  with nextIndex′ n l
... | just i′ = case p of λ ()
... | nothing
  with nextIndex′ n r
... | just i′ = case p of λ { refl → refl }
... | nothing = case p of λ ()

insertEmpty′ : ∀ n a i c → eval′ n a (insert′ n nothing i c) ≡ evalᶜ a c
insertEmpty′ zero    _ []ᵛ           _ = refl
insertEmpty′ (suc n) a (false ∷ᵛ is) c
  rewrite ∧-identityʳ (eval′ n a (insert′ n nothing is c))
  = insertEmpty′ n a is c
insertEmpty′ (suc n) a (true ∷ᵛ is)  c = insertEmpty′ n a is c

append′ : ∀ n mt i c a → nextIndex′ n mt ≡ just i →
  eval′ n a (insert′ n mt i c) ≡ eval′ n a mt ∧ evalᶜ a c
append′ zero    nothing           []ᵛ            _ _ _ = refl
append′ (suc n) nothing           (i ∷ᵛ is)     c a p = insertEmpty′ (suc n) a (i ∷ᵛ is) c
append′ (suc n) (just (node l r)) (false ∷ᵛ is) c a p
  rewrite append′ n l is c a (nextIndexLeft′ n l r is p)
        | ∧-assoc (eval′ n a l) (evalᶜ a c) (eval′ n a r)
        | ∧-assoc (eval′ n a l) (eval′ n a r) (evalᶜ a c)
        | ∧-comm (eval′ n a r) (evalᶜ a c)
  = refl

append′ (suc n) (just (node l r)) (true ∷ᵛ is)  c a p
  rewrite append′ n r is c a (nextIndexRight′ n l r is p)
  = sym $ ∧-assoc (eval′ n a l) (eval′ n a r) (evalᶜ a c)

append : ∀ f i c a → nextIndex f ≡ just i → eval a (insert f i c) ≡ eval a f ∧ evalᶜ a c
append f i c a p = append′ bitsᶜ f i c a p

adjust : Assignment → Variable → Bool → Assignment
adjust a v b v′
  with v′ ≟ᵛ v
... | true  because ofʸ _ = b
... | false because ofⁿ _ = a v′

adjustSame : ∀ a v b → (adjust a v b) v ≡ b
adjustSame a v b
  with v ≟ᵛ v
... | true  because ofʸ _ = refl
... | false because ofⁿ q = contradiction refl q

adjustOther : ∀ a v v′ b → v ≢ v′ → (adjust a v b) v′ ≡ a v′
adjustOther a v v′ b p
  with v′ ≟ᵛ v
... | true  because ofʸ q = contradiction (sym q) p
... | false because ofⁿ _ = refl

forceTrue : Assignment → Literal → Assignment
forceTrue a (pos v) = adjust a v true
forceTrue a (neg v) = adjust a v false

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
  with ∨-trueSplit (evalˡ a l′) (evalᶜ a ls′) p₂
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
