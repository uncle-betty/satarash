import Data.Nat

module Verifier (bitsᶜ : Data.Nat.ℕ) where

open Data.Nat using (ℕ ; zero ; suc ; _+_ ; _*_)

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; if_then_else_)
open import Data.Bool.Properties
  using (
      ∧-zeroʳ ; ∨-zeroʳ ; ∧-identityʳ ; ∨-identityʳ ; ∧-comm ; ∨-comm ; ∧-assoc ; ∨-assoc ;
      ∧-idem ; ∧-distribʳ-∨ ; ∧-distribˡ-∨ ; ∨-distribˡ-∧ ; ∧-inverseʳ ; ∨-∧-booleanAlgebra ;
      not-¬ ; ¬-not
    )
open import Data.List using (List) renaming ([] to []ˡ ; _∷_ to _∷ˡ_ ; _++_ to _++ˡ_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ ; _∷_ to _∷ᵃ_)
open import Data.List.Relation.Unary.Any using (Any ; here ; there)
open import Data.Maybe using (Maybe ; just ; nothing) renaming (map to mapᵐ)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ⁿ_)
open import Data.Nat.Show using () renaming (show to showⁿ)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁ ; map₂ ; ∃)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec using (Vec) renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_ ; _++_ to _++ᵛ_)
open import Function using (_$_ ; _∘_ ; id ; case_of_)
open import Level using (0ℓ)
open import Relation.Binary using (DecSetoid)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; ≢-sym ; inspect ; [_] ; cong ; subst ; trans ; decSetoid ;
    module ≡-Reasoning)
open import Relation.Nullary using (Dec ; _because_ ; ofʸ ; ofⁿ ; yes ; no)
open import Relation.Nullary.Negation using (contradiction)

open import Algebra.Lattice.Properties.BooleanAlgebra ∨-∧-booleanAlgebra
  using (deMorgan₁ ; deMorgan₂)
open ≡-Reasoning

Variable : Set
Variable = ℕ

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

showBinary : {n : ℕ} → Vec Bool n → String
showBinary bs = showⁿ (to-ℕ bs 0)
  where
  to-ℕ : {n : ℕ} → Vec Bool n → ℕ → ℕ
  to-ℕ []ᵛ           a = a
  to-ℕ (true ∷ᵛ bs)  a = to-ℕ bs (2 * a + 1)
  to-ℕ (false ∷ᵛ bs) a = to-ℕ bs (2 * a)

showLiteral : Literal → String
showLiteral (pos v) = "pos " ++ˢ showⁿ v
showLiteral (neg v) = "neg " ++ˢ showⁿ v

showIndexList : List Index → String
showIndexList []ˡ        = ""
showIndexList (i ∷ˡ []ˡ) = showBinary i
showIndexList (i ∷ˡ is)  = showBinary i ++ˢ " : " ++ˢ showIndexList is

showIndexLists : List (List Index) → String
showIndexLists []ˡ         = ""
showIndexLists (is ∷ˡ iss) = showIndexList is ++ˢ "\n" ++ˢ showIndexLists iss

showClause : Clause → String
showClause []ˡ        = ""
showClause (l ∷ˡ []ˡ) = showLiteral l
showClause (l ∷ˡ ls)  = showLiteral l ++ˢ " : " ++ˢ showClause ls

showTrie : {n m : ℕ} → Maybe (Trie n) → Vec Bool m → String
showTrie nothing             is = ""
showTrie (just (leaf c))     is = showBinary is ++ˢ " | " ++ˢ showClause c ++ˢ "\n"
showTrie (just (node tˡ tʳ)) is =
  showTrie tˡ (is ++ᵛ false ∷ᵛ []ᵛ) ++ˢ showTrie tʳ (is ++ᵛ true ∷ᵛ []ᵛ)

posInjective : (v₁ v₂ : Variable) → pos v₁ ≡ pos v₂ → v₁ ≡ v₂
posInjective v₁ v₂ refl = refl

negInjective : (v₁ v₂ : Variable) → neg v₁ ≡ neg v₂ → v₁ ≡ v₂
negInjective v₁ v₂ refl = refl

infix 4 _≟ˡ_

_≟ˡ_ : (l₁ l₂ : Literal) → Dec (l₁ ≡ l₂)
pos v₁ ≟ˡ pos v₂ with v₁ ≟ⁿ v₂
... | true  because ofʸ refl = true because ofʸ refl
... | false because ofⁿ p = false because ofⁿ (p ∘ posInjective v₁ v₂)
pos _  ≟ˡ neg _  = false because ofⁿ λ ()
neg _  ≟ˡ pos _  = false because ofⁿ λ ()
neg v₁ ≟ˡ neg v₂ with v₁ ≟ⁿ v₂
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

insert′ : (n : ℕ) → Maybe (Trie n) → Clause → Maybe (Maybe (Trie n))
insert′ zero    nothing             c = just $ just (leaf c)
insert′ zero    (just (leaf _))     c = nothing
insert′ (suc n) nothing             c
  with insert′ n nothing c
... | just t  = just $ just (node t nothing)
... | nothing = nothing
insert′ (suc n) (just (node tˡ tʳ)) c
  with insert′ n tˡ c
... | just t  = just $ just (node t tʳ)
... | nothing
  with insert′ n tʳ c
... | just t  = just $ just (node tˡ t)
... | nothing = nothing

insert : Formula → Clause → Maybe Formula
insert = insert′ bitsᶜ

remove′ : (n : ℕ) → Maybe (Trie n) → Vec Bool n → Maybe (Trie n)
remove′ zero    _                   []ᵛ           = nothing
remove′ (suc n) nothing             (_ ∷ᵛ _)      = nothing
remove′ (suc n) (just (node tˡ tʳ)) (false ∷ᵛ is) = just (node (remove′ n tˡ is) tʳ)
remove′ (suc n) (just (node tˡ tʳ)) (true ∷ᵛ is)  = just (node tˡ (remove′ n tʳ is))

remove : Formula → Index → Formula
remove = remove′ bitsᶜ

removePreserves′ : (n : ℕ) → (t : Maybe (Trie n)) → (is : Vec Bool n) →
  ∀ a → eval′ n a (remove′ n t is) ≡ false → eval′ n a t ≡ false
removePreserves′ zero    nothing             []ᵛ           a p = case p of λ ()
removePreserves′ zero    (just cˡ)           []ᵛ           a p = case p of λ ()
removePreserves′ (suc n) nothing             (i ∷ᵛ is)     a p = case p of λ ()
removePreserves′ (suc n) (just (node tˡ tʳ)) (false ∷ᵛ is) a p
  with eval′ n a tʳ
... | false = ∧-zeroʳ (eval′ n a tˡ)
... | true  =
  let q = subst (_≡ false) (∧-identityʳ (eval′ n a (remove′ n tˡ is))) p in
  let r = removePreserves′ n tˡ is a q in
  subst (_≡ false) (sym $ ∧-identityʳ (eval′ n a tˡ)) r
removePreserves′ (suc n) (just (node tˡ tʳ)) (true ∷ᵛ is)  a p
  with eval′ n a tˡ
... | false = refl
... | true  = removePreserves′ n tʳ is a p

removePreserves : (f : Formula) → (i : Index) → ∀ a → eval a (remove f i) ≡ false → eval a f ≡ false
removePreserves = removePreserves′ bitsᶜ

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

notSwap : (b₁ b₂ : Bool) → not b₁ ≡ b₂ → b₁ ≡ not b₂
notSwap b₁ b₂ refl = sym $ notNot b₁

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
... | yes _ = removeLiteral lsᶜ l
... | no  _ = lᶜ ∷ˡ removeLiteral lsᶜ l

removeLiteral-∧-not : (a : Assignment) → (c : Clause) →  (l : Literal) →
  evalᶜ a c ∧ not (evalˡ a l) ≡ evalᶜ a (removeLiteral c l) ∧ not (evalˡ a l)
removeLiteral-∧-not a []ˡ         _ = refl
removeLiteral-∧-not a (lᶜ ∷ˡ lsᶜ) l with lᶜ ≟ˡ l
... | yes refl = begin
  (evalˡ a lᶜ ∨ evalᶜ a lsᶜ) ∧ not (evalˡ a lᶜ)                  ≡⟨ ∧-distribʳ-∨ (not (evalˡ a lᶜ)) (evalˡ a lᶜ) (evalᶜ a lsᶜ) ⟩
  evalˡ a lᶜ ∧ not (evalˡ a lᶜ) ∨ evalᶜ a lsᶜ ∧ not (evalˡ a lᶜ) ≡⟨ cong (_∨ evalᶜ a lsᶜ ∧ not (evalˡ a lᶜ)) $ ∧-inverseʳ (evalˡ a lᶜ) ⟩
  evalᶜ a lsᶜ ∧ not (evalˡ a lᶜ)                                 ≡⟨ removeLiteral-∧-not a lsᶜ l  ⟩
  evalᶜ a (removeLiteral lsᶜ lᶜ) ∧ not (evalˡ a lᶜ)              ∎
... | no  _    = begin
  (evalˡ a lᶜ ∨ evalᶜ a lsᶜ) ∧ not (evalˡ a l)                                   ≡⟨ ∧-distribʳ-∨ (not (evalˡ a l)) (evalˡ a lᶜ) (evalᶜ a lsᶜ) ⟩
  evalˡ a lᶜ ∧ not (evalˡ a l) ∨ evalᶜ a lsᶜ ∧ not (evalˡ a l)                   ≡⟨ cong (evalˡ a lᶜ ∧ not (evalˡ a l) ∨_) $ removeLiteral-∧-not a lsᶜ l ⟩
  evalˡ a lᶜ ∧ not (evalˡ a l) ∨ evalᶜ a (removeLiteral lsᶜ l) ∧ not (evalˡ a l) ≡⟨ sym $ ∧-distribʳ-∨ (not (evalˡ a l)) (evalˡ a lᶜ) (evalᶜ a (removeLiteral lsᶜ l)) ⟩
  (evalˡ a lᶜ ∨ evalᶜ a (removeLiteral lsᶜ l)) ∧ not (evalˡ a l)                 ∎

removeLiteralTrue : (a : Assignment) → (c : Clause) → (l : Literal) →
  evalᶜ a (removeLiteral c l) ≡ true → evalᶜ a c ≡ true
removeLiteralTrue a (lᶜ ∷ˡ lsᶜ) l p
  with lᶜ ≟ˡ l
... | yes _ = begin
  evalˡ a lᶜ ∨ evalᶜ a lsᶜ ≡⟨ cong (evalˡ a lᶜ ∨_) $ removeLiteralTrue a lsᶜ l p ⟩
  evalˡ a lᶜ ∨ true        ≡⟨ ∨-zeroʳ (evalˡ a lᶜ) ⟩
  true                     ∎
... | no  q
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
... | yes _ = removeLiteral-∉ l lsᶜ
... | no  p = λ where
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

andNotRUP : (a : Assignment) → (c₁ c₂ : Clause) → (l : Literal) → andNot c₁ c₂ ≡ l ∷ˡ []ˡ →
  evalˡ a l ≡ false → evalᶜ a c₁ ≡ evalᶜ a c₁ ∧ evalᶜ a c₂
andNotRUP a c₁ c₂ l p₁ p₂
  with q ← andNotIntro a c₁ c₂
  with evalᶜ a c₁
... | false = refl
... | true  = sym $ begin
  evalᶜ a c₂                                      ≡⟨ notSwap (evalᶜ a c₂) (evalᶜ a (andNot c₁ c₂) ∧ not (evalᶜ a c₂)) q ⟩
  not (evalᶜ a (andNot c₁ c₂) ∧ not (evalᶜ a c₂)) ≡⟨ cong (λ # → not (evalᶜ a # ∧ not (evalᶜ a c₂))) p₁ ⟩
  not ((evalˡ a l ∨ false) ∧ not (evalᶜ a c₂))    ≡⟨ cong (λ # → not (# ∧ not (evalᶜ a c₂))) (∨-identityʳ (evalˡ a l)) ⟩
  not (evalˡ a l ∧ not (evalᶜ a c₂))              ≡⟨ cong (λ # → not (# ∧ not (evalᶜ a c₂))) p₂ ⟩
  true                                            ∎

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
  Result (∀ a → eval a f ∧ not (evalᶜ a c) ≡ false)
    (∃ λ cʳ → ∀ a → eval a f ∧ evalᶜ a cʳ ≡ eval a f ∧ evalᶜ a c)
checkRUP′ f c []ˡ       = more (c , λ _ → refl)
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
  with checkRUP′ f (c ++ˡ flip l ∷ˡ []ˡ) is
... | done p = done $ λ a → begin
  eval a f ∧ not (evalᶜ a c)                            ≡⟨ cong (_∧ not (evalᶜ a c)) $ duplicate f i cᶠ eq₁ a ⟩
  (eval a f ∧ evalᶜ a cᶠ) ∧ not (evalᶜ a c)             ≡⟨ ∧-assoc (eval a f) (evalᶜ a cᶠ) (not (evalᶜ a c)) ⟩
  eval a f ∧ evalᶜ a cᶠ ∧ not (evalᶜ a c)               ≡⟨ cong (eval a f ∧_) $ andNotIntro a cᶠ c ⟩
  eval a f ∧ evalᶜ a (andNot cᶠ c) ∧ not (evalᶜ a c)    ≡⟨ cong (λ # → eval a f ∧ evalᶜ a # ∧ not (evalᶜ a c)) eq₂ ⟩
  eval a f ∧ (evalˡ a l ∨ false) ∧ not (evalᶜ a c)      ≡⟨ cong (eval a f ∧_) $ pushUnit a l c ⟩
  eval a f ∧ not (evalˡ a (flip l) ∨ evalᶜ a c)         ≡⟨ cong (λ # → eval a f ∧ not #) $ ∨-comm (evalˡ a (flip l)) (evalᶜ a c) ⟩
  eval a f ∧ not (evalᶜ a c ∨ evalˡ a (flip l))         ≡⟨ sym $ cong (λ # → eval a f ∧ not (evalᶜ a c ∨ #)) $ ∨-identityʳ (evalˡ a (flip l)) ⟩
  eval a f ∧ not (evalᶜ a c ∨ evalˡ a (flip l) ∨ false) ≡⟨ sym $ cong (λ # → eval a f ∧ not #) $ ++⇒∨ a c (flip l ∷ˡ []ˡ) ⟩
  eval a f ∧ not (evalᶜ a (c ++ˡ flip l ∷ˡ []ˡ))        ≡⟨ p a ⟩
  false                                                 ∎
... | more (cʳ , q) = more (cʳ , aux)
  where
  aux : ∀ a → eval a f ∧ evalᶜ a cʳ ≡ eval a f ∧ evalᶜ a c
  aux a
    with evalˡ a l | inspect (evalˡ a) l
  ... | true  | [ eq₃ ] = begin
    eval a f ∧ evalᶜ a cʳ                             ≡⟨ q a ⟩
    eval a f ∧ evalᶜ a (c ++ˡ flip l ∷ˡ []ˡ)          ≡⟨ cong (eval a f ∧_) $ ++⇒∨ a c (flip l ∷ˡ []ˡ) ⟩
    eval a f ∧ (evalᶜ a c ∨ evalˡ a (flip l) ∨ false) ≡⟨ cong (λ # → eval a f ∧ (evalᶜ a c ∨ # ∨ false)) $ flipNot a l ⟩
    eval a f ∧ (evalᶜ a c ∨ not (evalˡ a l) ∨ false)  ≡⟨ cong (λ # → eval a f ∧ (evalᶜ a c ∨ not # ∨ false)) $ eq₃ ⟩
    eval a f ∧ (evalᶜ a c ∨ false)                    ≡⟨ cong (eval a f ∧_) $ ∨-identityʳ (evalᶜ a c) ⟩
    eval a f ∧ evalᶜ a c                              ∎
  ... | false | [ eq₃ ] = begin
    eval a f ∧ evalᶜ a cʳ                             ≡⟨ q a ⟩
    eval a f ∧ evalᶜ a (c ++ˡ flip l ∷ˡ []ˡ)          ≡⟨ cong (eval a f ∧_) $ ++⇒∨ a c (flip l ∷ˡ []ˡ) ⟩
    eval a f ∧ (evalᶜ a c ∨ evalˡ a (flip l) ∨ false) ≡⟨ cong (λ # → eval a f ∧ (evalᶜ a c ∨ #)) $ ∨-identityʳ (evalˡ a (flip l)) ⟩
    eval a f ∧ (evalᶜ a c ∨ evalˡ a (flip l))         ≡⟨ cong (eval a f ∧_) $ ∨-comm (evalᶜ a c) (evalˡ a (flip l)) ⟩
    eval a f ∧ (evalˡ a (flip l) ∨ evalᶜ a c)         ≡⟨ cong (λ # → eval a f ∧ (# ∨ evalᶜ a c)) (flipNot a l) ⟩
    eval a f ∧ (not (evalˡ a l) ∨ evalᶜ a c)          ≡⟨ cong (λ # → eval a f ∧ ((not #) ∨ evalᶜ a c)) eq₃ ⟩
    eval a f ∧ true                                   ≡⟨ ∧-identityʳ (eval a f) ⟩
    eval a f                                          ≡⟨ duplicate f i cᶠ eq₁ a ⟩
    eval a f ∧ evalᶜ a cᶠ                             ≡⟨ cong (eval a f ∧_) $ andNotRUP a cᶠ c l eq₂ eq₃ ⟩
    eval a f ∧ evalᶜ a cᶠ ∧ evalᶜ a c                 ≡⟨ sym $ ∧-assoc (eval a f) (evalᶜ a cᶠ) (evalᶜ a c) ⟩
    (eval a f ∧ evalᶜ a cᶠ) ∧ evalᶜ a c               ≡⟨ cong (_∧ evalᶜ a c) $ sym $ duplicate f i cᶠ eq₁ a ⟩
    eval a f ∧ evalᶜ a c                              ∎
... | fail          = fail
checkRUP′ _ _ _ | _ | _ | _ | _ = fail

checkRUP : (f : Formula) → (c : Clause) → (is : List Index) →
  Result (∀ a → eval a f ≡ eval a f ∧ evalᶜ a c)
    (∃ λ cʳ → ∀ a → eval a f ∧ evalᶜ a cʳ ≡ eval a f ∧ evalᶜ a c)
checkRUP f c is
  with checkRUP′ f c is
... | fail          = fail
... | more (cʳ , p) = more (cʳ , p)
... | done p        = done $
  λ a → case ∧-splitFalse (eval a f) (not (evalᶜ a c)) (p a) of λ where
    (inj₁ q) → trans q $ sym $ ∧-extendFalse (eval a f) (evalᶜ a c) q
    (inj₂ q) → begin
      eval a f             ≡⟨ sym $ ∧-identityʳ (eval a f) ⟩
      eval a f ∧ true      ≡⟨ sym $ cong (eval a f ∧_) $ notFalse (evalᶜ a c) q ⟩
      eval a f ∧ evalᶜ a c ∎

insert⇒∧′ : (n : ℕ) → (t t′ : Maybe (Trie n)) → (c : Clause) → insert′ n t c ≡ just t′ →
  ∀ a → eval′ n a t′ ≡ eval′ n a t ∧ evalᶜ a c
insert⇒∧′ zero    nothing             (just (leaf _))     _ refl = λ _ → refl
insert⇒∧′ zero    (just (leaf _))     (just _)            _ ()
insert⇒∧′ zero    (just (leaf _))     nothing             _ ()
insert⇒∧′ (suc n) nothing             nothing             c p
  with insert′ n nothing c
... | nothing with () ← p
... | just _  with () ← p
insert⇒∧′ (suc n) nothing             (just (node tˡ tʳ)) c p
  with insert′ n nothing c | inspect (insert′ n nothing) c
... | nothing | _      with ()   ← p
... | just f  | [ eq ] with refl ← p = λ a → begin
  eval′ n a f ∧ true ≡⟨ ∧-identityʳ (eval′ n a f) ⟩
  eval′ n a f        ≡⟨ insert⇒∧′ n nothing f c eq a ⟩
  evalᶜ a c          ∎
insert⇒∧′ (suc n) (just (node tˡ tʳ)) nothing             c p
  with insert′ n tˡ c
... | nothing
  with insert′ n tʳ c
... | nothing with () ← p
... | just _  with () ← p
insert⇒∧′ (suc n) (just (node l₁ r₁)) (just (node l₂ r₂)) c p
  with insert′ n l₁ c | inspect (insert′ n l₁) c
... | just l₁′ | [ eq₁ ] with refl ← p = λ a → begin
  eval′ n a l₁′ ∧ eval′ n a r₁              ≡⟨ cong (_∧ eval′ n a r₁) $ insert⇒∧′ n l₁ l₁′ c eq₁ a ⟩
  (eval′ n a l₁ ∧ evalᶜ a c) ∧ eval′ n a r₁ ≡⟨ ∧-assoc (eval′ n a l₁) (evalᶜ a c) (eval′ n a r₁) ⟩
  eval′ n a l₁ ∧ evalᶜ a c ∧ eval′ n a r₁   ≡⟨ cong (eval′ n a l₁ ∧_) $ ∧-comm (evalᶜ a c) (eval′ n a r₁) ⟩
  eval′ n a l₁ ∧ eval′ n a r₁ ∧ evalᶜ a c   ≡⟨ sym $ ∧-assoc (eval′ n a l₁) (eval′ n a r₁) (evalᶜ a c) ⟩
  (eval′ n a l₁ ∧ eval′ n a r₁) ∧ evalᶜ a c ∎
... | nothing  | [ eq₁ ]
  with insert′ n r₁ c | inspect (insert′ n r₁) c
... | just r₁′ | [ eq₂ ] with refl ← p = λ a → begin
  eval′ n a l₁ ∧ eval′ n a r₁′              ≡⟨ cong (eval′ n a l₁ ∧_) $ insert⇒∧′ n r₁ r₁′ c eq₂ a ⟩
  eval′ n a l₁ ∧ eval′ n a r₁ ∧ evalᶜ a c   ≡⟨ sym $ ∧-assoc (eval′ n a l₁) (eval′ n a r₁) (evalᶜ a c) ⟩
  (eval′ n a l₁ ∧ eval′ n a r₁) ∧ evalᶜ a c ∎

insert⇒∧ : (f f′ : Formula) → (c : Clause) → insert f c ≡ just f′ →
  ∀ a → eval a f′ ≡ eval a f ∧ evalᶜ a c
insert⇒∧ = insert⇒∧′ bitsᶜ

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
  with v ≟ⁿ vᵃ
... | true  because ofʸ _ = b
... | false because ofⁿ _ = a v

adjustSame : (a : Assignment) → (vᵃ : Variable) → (b : Bool) → (adjust a vᵃ b) vᵃ ≡ b
adjustSame a vᵃ b
  with vᵃ ≟ⁿ vᵃ
... | true  because ofʸ _ = refl
... | false because ofⁿ q = contradiction refl q

adjustOther : (a : Assignment) → (vᵃ v : Variable) → (b : Bool) → vᵃ ≢ v → (adjust a vᵃ b) v ≡ a v
adjustOther a vᵃ v b p
  with v ≟ⁿ vᵃ
... | true  because ofʸ q = contradiction (sym q) p
... | false because ofⁿ _ = refl

forceTrue : Assignment → Literal → Assignment
forceTrue a (pos v) = adjust a v true
forceTrue a (neg v) = adjust a v false

forceTrueSame : (a : Assignment) → (l : Literal) → evalˡ (forceTrue a l) l ≡ true
forceTrueSame a (pos v) = adjustSame a v true
forceTrueSame a (neg v) = cong not $ adjustSame a v false

forceTrueOther : (l₁ l₂ : Literal) → (a : Assignment) → flip l₁ ≢ l₂ → evalˡ a l₂ ≡ true →
  evalˡ (forceTrue a l₁) l₂ ≡ true
forceTrueOther (pos v₁) (pos v₂) a p₁ p₂
  with v₂ ≟ⁿ v₁
... | true  because ofʸ _ = refl
... | false because ofⁿ _ = p₂
forceTrueOther (pos v₁) (neg v₂) a p₁ p₂ = begin
  not (adjust a v₁ true v₂) ≡⟨ cong not $ adjustOther a v₁ v₂ true (p₁ ∘ cong neg) ⟩
  not (a v₂)                ≡⟨ p₂ ⟩
  true                      ∎
forceTrueOther (neg v₁) (pos v₂) a p₁ p₂ = begin
  adjust a v₁ false v₂ ≡⟨ adjustOther a v₁ v₂ false (p₁ ∘ cong pos) ⟩
  a v₂                 ≡⟨ p₂ ⟩
  true                 ∎
forceTrueOther (neg v₁) (neg v₂) a p₁ p₂
  with v₂ ≟ⁿ v₁
... | true  because ofʸ _ = refl
... | false because ofⁿ _ = p₂

forceTrue-∈ : (l : Literal) → (c : Clause) → (a : Assignment) → l ∈ c →
  evalᶜ (forceTrue a l) c ≡ true
forceTrue-∈ (pos v) (pos v ∷ˡ lsᶜ) a (here refl) =
  cong (_∨ evalᶜ (adjust a v true) lsᶜ) $ adjustSame a v true
forceTrue-∈ (neg v) (neg v ∷ˡ lsᶜ) a (here refl) =
  cong (λ # → not # ∨ evalᶜ (adjust a v false) lsᶜ) $ adjustSame a v false
forceTrue-∈ l       (lᶜ ∷ˡ lsᶜ)    a (there p)   = begin
  evalˡ (forceTrue a l) lᶜ ∨ evalᶜ (forceTrue a l) lsᶜ ≡⟨ cong (evalˡ (forceTrue a l) lᶜ ∨_) $ forceTrue-∈ l lsᶜ a p ⟩
  evalˡ (forceTrue a l) lᶜ ∨ true                      ≡⟨ ∨-zeroʳ (evalˡ (forceTrue a l) lᶜ) ⟩
  true                                                 ∎

forceTrue-∉ : (l : Literal) → (c : Clause) → (a : Assignment) → flip l ∉ c → evalᶜ a c ≡ true →
  evalᶜ (forceTrue a l) c ≡ true
forceTrue-∉ l (lᶜ ∷ˡ lsᶜ) a p₁ p₂
  with ∨-splitTrue (evalˡ a lᶜ) (evalᶜ a lsᶜ) p₂
... | inj₁ q = cong (_∨ evalᶜ (forceTrue a l) lsᶜ) $ forceTrueOther l lᶜ a (p₁ ∘ here) q
... | inj₂ q = begin
  evalˡ (forceTrue a l) lᶜ ∨ evalᶜ (forceTrue a l) lsᶜ ≡⟨ cong (evalˡ (forceTrue a l) lᶜ ∨_) $ forceTrue-∉ l lsᶜ a (p₁ ∘ there) q ⟩
  evalˡ (forceTrue a l) lᶜ ∨ true                      ≡⟨ ∨-zeroʳ (evalˡ (forceTrue a l) lᶜ) ⟩
  true                                                 ∎

∉-tail : (l lᶜ : Literal) → (lsᶜ : Clause) → l ∉ lᶜ ∷ˡ lsᶜ → l ∉ lsᶜ
∉-tail _ _ (_ ∷ˡ _) p (here n)  = p $ there (here n)
∉-tail _ _ (_ ∷ˡ _) p (there n) = p $ there (there n)

clauseCheck₁ : (l : Literal) → (c : Clause) → Maybe (flip l ∉ c)
clauseCheck₁ l c
  with flip l ∈? c
... | false because ofⁿ p = just p
... | true  because ofʸ _ = nothing

clauseProof₁ : (c : Clause) → (l : Literal) → ∀ a → evalᶜ a c ≡ true → flip l ∉ c →
  evalᶜ (forceTrue a l) c ≡ true
clauseProof₁ c l a p q = forceTrue-∉ l c a q p

clauseCheck₂ : (c₁ c₂ : Clause) → (l : Literal) → Maybe (∃ λ lᶜ → lᶜ ∈ c₁ × flip lᶜ ∈ c₂ × l ≢ lᶜ)
clauseCheck₂ []ˡ         _  _ = nothing
clauseCheck₂ (l₁ ∷ˡ ls₁) c₂ l
  with l ≟ˡ l₁
... | true  because ofʸ _ = mapᵐ ((map₂ (map₁ there))) (clauseCheck₂ ls₁ c₂ l)
... | false because ofⁿ p
  with flip l₁ ∈? c₂
... | false because ofⁿ _ = mapᵐ ((map₂ (map₁ there))) (clauseCheck₂ ls₁ c₂ l)
... | true  because ofʸ q = just $ l₁ , here refl , q , p

clauseProof₂ : (l₁ : Literal) → (ls₁ c₂ : Clause) → (l : Literal) → l ∈ ls₁ → flip l ∈ c₂ → l₁ ≢ l →
  ∀ a → evalᶜ a (l₁ ∷ˡ ls₁) ≡ false → evalᶜ (forceTrue a l₁) c₂ ≡ true
clauseProof₂ l₁ (l₁′ ∷ˡ ls₁′) c₂ l (here refl) q r a s
  with (_ ∷ᵃ t ∷ᵃ _) ← allFlippedTrue a (l₁ ∷ˡ l₁′ ∷ˡ ls₁′) s =
  let u = forceTrueOther l₁ (flip l₁′) a (r ∘ flipInjective) t in
  anyLiteralTrue (forceTrue a l₁) (flip l₁′) c₂ u q
clauseProof₂ l₁ (l₁′ ∷ˡ ls₁′) c₂ l (there p) q r a s =
  let t = ∨-stripFalse (evalˡ a l₁) (evalˡ a l₁′) (evalᶜ a ls₁′) s in
  clauseProof₂ l₁ ls₁′ c₂ l p q r a t

clauseCheck₃ : (f : Formula) → (lᶜ : Literal) → (lsᶜ c : Clause) → List (List Index) →
  List (List Index) × Maybe (∀ a → eval a f ≡ true → evalᶜ a (resolvent lᶜ (lᶜ ∷ˡ lsᶜ) c) ≡ true)
clauseCheck₃ _ _ _  _ []ˡ           = []ˡ , nothing
clauseCheck₃ f lᶜ lsᶜ c (is ∷ˡ iss)
  with checkRUP f (resolvent lᶜ (lᶜ ∷ˡ lsᶜ) c) is
... | more _        = iss , nothing
... | fail          = iss , nothing
... | done p        = iss , just λ a q →
   sym $ subst (λ # → # ≡ # ∧ (evalˡ a lᶜ ∨ evalᶜ a (lsᶜ ++ˡ removeLiteral c (flip lᶜ)))) q (p a)

clauseProof₃ : (lᶜ : Literal) → (lsᶜ c : Clause) →
  ∀ a → evalᶜ a (lᶜ ∷ˡ lsᶜ) ≡ false → evalᶜ a (resolvent lᶜ (lᶜ ∷ˡ lsᶜ) c) ≡ true →
    evalᶜ (forceTrue a lᶜ) c ≡ true
clauseProof₃ lᶜ lsᶜ c = λ a p q →
  let r = resolventTrue a lᶜ (lᶜ ∷ˡ lsᶜ) c p q in
  let s = removeLiteral-∉ (flip lᶜ) c in
  let t = forceTrue-∉ lᶜ (removeLiteral c (flip lᶜ)) a s r  in
  removeLiteralTrue (forceTrue a lᶜ) c (flip lᶜ) t

checkRAT′ : (n : ℕ) → (f : Formula) → (t : Maybe (Trie n)) → (lᶜ : Literal) → (lsᶜ : Clause) →
  (iss : List (List Index)) →
  List (List Index) × Maybe (∀ a → eval a f ≡ true → eval′ n a t ≡ true →
    evalᶜ a (lᶜ ∷ˡ lsᶜ) ≡ false → eval′ n (forceTrue a lᶜ) t ≡ true)
checkRAT′ zero    f nothing             lᶜ lsᶜ iss  = iss , (just $ λ _ _ _ _ → refl)
checkRAT′ zero    f (just (leaf cˡ))    lᶜ lsᶜ iss
  with clauseCheck₁ lᶜ cˡ
... | just p = iss , (just $ λ a _ q _ → clauseProof₁ cˡ lᶜ a q p)
... | nothing
  with clauseCheck₂ lsᶜ cˡ lᶜ
... | just (lʳ , p , q , r) = iss , (just $ λ a _ _ s → clauseProof₂ lᶜ lsᶜ cˡ lʳ p q r a s)
... | nothing
  with clauseCheck₃ f lᶜ lsᶜ cˡ iss
... | (iss′ , just p)  = iss′ , (just $ λ a q _ r → clauseProof₃ lᶜ lsᶜ cˡ a r (p a q))
... | (iss′ , nothing) = iss′ , nothing
checkRAT′ (suc n) f nothing             lᶜ lsᶜ iss = iss , (just $ λ _ _ _ _ → refl)
checkRAT′ (suc n) f (just (node tˡ tʳ)) lᶜ lsᶜ iss
  with checkRAT′ n f tˡ lᶜ lsᶜ iss
... | (iss′ , nothing) = (iss′ , nothing)
... | (iss′ , just p)
  with checkRAT′ n f tʳ lᶜ lsᶜ iss′
... | (iss″ , nothing) = (iss″ , nothing)
... | (iss″ , just q)  = iss″ , (
    just $ λ a r s t →
      let u₁ , u₂ = ∧-splitTrue (eval′ n a tˡ) (eval′ n a tʳ) s in
      ∧-joinTrue (eval′ n (forceTrue a lᶜ) tˡ) (eval′ n (forceTrue a lᶜ) tʳ)
        (p a r u₁ t) (q a r u₂ t)
  )

checkRAT : (f : Formula) → (lᶜ : Literal) → (lsᶜ : Clause) → (iss : List (List Index)) →
  Maybe (∀ a → eval a f ≡ true → evalᶜ a (lᶜ ∷ˡ lsᶜ) ≡ false →
    let a′ = forceTrue a lᶜ in eval a′ f ∧ evalᶜ a′ (lᶜ ∷ˡ lsᶜ) ≡ true)
checkRAT f lᶜ lsᶜ iss = mapᵐ (λ p a q r → begin
    eval (forceTrue a lᶜ) f ∧ (evalˡ (forceTrue a lᶜ) lᶜ ∨ evalᶜ (forceTrue a lᶜ) lsᶜ) ≡⟨ cong (_∧ (evalˡ (forceTrue a lᶜ) lᶜ ∨ evalᶜ (forceTrue a lᶜ) lsᶜ)) $ p a q q r ⟩
    evalˡ (forceTrue a lᶜ) lᶜ ∨ evalᶜ (forceTrue a lᶜ) lsᶜ                             ≡⟨ cong (_∨ (evalᶜ (forceTrue a lᶜ) lsᶜ)) $ forceTrueSame a lᶜ ⟩
    true                                                                               ∎
  ) (proj₂ $ checkRAT′ bitsᶜ f f lᶜ lsᶜ iss)

∀-∧-false : (f : Formula) → (∀ a → eval a f ≡ eval a f ∧ false) → ∀ a → eval a f ≡ false
∀-∧-false f p a = begin
  eval a f         ≡⟨ p a ⟩
  eval a f ∧ false ≡⟨ ∧-zeroʳ (eval a f) ⟩
  false            ∎

checkLRAT : (f : Formula) → Proof → Maybe (∀ a → eval a f ≡ false)

deleteStep : (f : Formula) → List Index → Proof → Maybe (∀ a → eval a f ≡ false)
deleteStep f []ˡ       ss = checkLRAT f ss
deleteStep f (i ∷ˡ is) ss
  with deleteStep (remove f i) is ss
... | nothing = nothing
... | just p  = just $ λ a → removePreserves f i a (p a)

RUPStep : (f : Formula) → (c : Clause) → Proof →
  (∀ a → eval a f ≡ eval a f ∧ evalᶜ a c) → Maybe (∀ a → eval a f ≡ false)
RUPStep f []ˡ         _  p = just $ ∀-∧-false f p
RUPStep f (lᶜ ∷ˡ lsᶜ) ss p
  with insert f (lᶜ ∷ˡ lsᶜ) | inspect (insert f) (lᶜ ∷ˡ lsᶜ)
... | nothing | _      = nothing
... | just f′ | [ eq ]
  with checkLRAT f′ ss
... | nothing = nothing
... | just q  =
  let r = insert⇒∧ f f′ (lᶜ ∷ˡ lsᶜ) eq in
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
  with insert f c | inspect (insert f) c
... | nothing | _       = nothing
... | just f′  | [ eq ]
  with checkLRAT f′ ss
... | nothing = nothing
... | just r =
  let s = insert⇒∧ f f′ c eq in
  let t = λ a → trans (sym $ s a) (r a) in
  just $ RATStep′ f c lᶜ lsᶜ p q t

checkLRAT _ []ˡ                  = nothing
checkLRAT f (del is ∷ˡ ss)       = deleteStep f is ss
checkLRAT f (ext c is iss ∷ˡ ss)
  with checkRUP f c is
... | fail                 = nothing
... | done p               = RUPStep f c ss p
... | more ([]ˡ , _)       = nothing
... | more (lᶜ ∷ˡ lsᶜ , p)
  with checkRAT f lᶜ lsᶜ iss
... | nothing = nothing
... | just q  = RATStep f c lᶜ lsᶜ ss p q
