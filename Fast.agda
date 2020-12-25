import Data.Nat

module Fast (bitsᵛ : Data.Nat.ℕ) (bitsᶜ : Data.Nat.ℕ) where

open Data.Nat using (ℕ ; zero ; suc)

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; if_then_else_)
open import Data.List using (List) renaming ([] to []ˡ ; _∷_ to _∷ˡ_ ; _++_ to _++ˡ_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using (Vec) renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_)
open import Function using (_$_ ; _∘_ ; id ; case_of_)
open import Relation.Nullary using (_because_ ; ofʸ ; ofⁿ)

import Correct as C

open C bitsᵛ bitsᶜ using (
    Variable ; Literal ; pos ; neg ; Clause ; Formula ;
    Trie ; leaf ; node ; Index ;
    Step ; del ; ext ; Proof ;
    Result ; done ; more ; fail ;
    literalDS ;
    lookup ; insert ; remove ; nextIndex ;
    _≟ˡ_ ; flip ; andNot ; resolvent
  )

open import Data.List.Membership.DecSetoid literalDS using (_∈?_)

checkRUP′ : Formula → Clause → List Index → Result ⊤ Clause
checkRUP′ f c []ˡ       = more c
checkRUP′ f c (i ∷ˡ is)
  with lookup f i
... | nothing = fail
... | just cᶠ
  with andNot cᶠ c
checkRUP′ f c (i ∷ˡ is) | just cᶠ | []ˡ      = done tt
checkRUP′ f c (i ∷ˡ is) | just cᶠ | l ∷ˡ []ˡ = checkRUP′ f (flip l ∷ˡ c) is
checkRUP′ _ _ _         | _       | _        = fail

checkRUP : Formula → Clause → List Index → Result ⊤ Clause
checkRUP f c is
  with checkRUP′ f c is
... | fail    = fail
... | more cʳ = more cʳ
... | done p  = done p

clauseCheck₁ : Literal → Clause → Bool
clauseCheck₁ l c
  with flip l ∈? c
... | false because ofⁿ _ = true
... | true  because ofʸ _ = false

clauseCheck₂ : Clause → Clause → Literal → Bool
clauseCheck₂ []ˡ         _  _ = false
clauseCheck₂ (l₁ ∷ˡ ls₁) c₂ l
  with l ≟ˡ l₁
... | true  because ofʸ _ = clauseCheck₂ ls₁ c₂ l
... | false because ofⁿ _
  with flip l₁ ∈? c₂
... | false because ofⁿ _ = clauseCheck₂ ls₁ c₂ l
... | true  because ofʸ _ = true

clauseCheck₃ : Formula → Literal → Clause → Clause → List (List Index) → List (List Index) × Bool
clauseCheck₃ _ _ _  _ []ˡ           = []ˡ , false
clauseCheck₃ f lᶜ lsᶜ c (is ∷ˡ iss)
  with checkRUP f (resolvent lᶜ (lᶜ ∷ˡ lsᶜ) c) is
... | more _        = iss , false
... | fail          = iss , false
... | done _        = iss , true

checkRAT′ : (n : ℕ) → Formula → Maybe (Trie n) → Literal → Clause → List (List Index) →
  List (List Index) × Bool
checkRAT′ zero    f nothing             lᶜ lsᶜ iss  = iss , true
checkRAT′ zero    f (just (leaf cˡ))    lᶜ lsᶜ iss
  with clauseCheck₁ lᶜ cˡ
... | true  = iss , true
... | false
  with clauseCheck₂ lsᶜ cˡ lᶜ
... | true  = iss , true
... | false
  with clauseCheck₃ f lᶜ lsᶜ cˡ iss
... | iss′ , true  = iss′ , true
... | iss′ , false = iss′ , false
checkRAT′ (suc n) f nothing             lᶜ lsᶜ iss = iss , true
checkRAT′ (suc n) f (just (node tˡ tʳ)) lᶜ lsᶜ iss
  with checkRAT′ n f tˡ lᶜ lsᶜ iss
... | iss′ , false = iss′ , false
... | iss′ , true
  with checkRAT′ n f tʳ lᶜ lsᶜ iss′
... | iss″ , false = iss″ , false
... | iss″ , true  = iss″ , true

checkRAT : Formula → Literal → Clause → List (List Index) → Bool
checkRAT f lᶜ lsᶜ iss = proj₂ $ checkRAT′ bitsᶜ f f lᶜ lsᶜ iss

checkLRAT : Formula → Proof → Bool

deleteStep : Formula → List Index → Proof → Bool
deleteStep f []ˡ       ss = checkLRAT f ss
deleteStep f (i ∷ˡ is) ss = deleteStep (remove f i) is ss

RUPStep : Formula → Clause → Proof → Bool
RUPStep f []ˡ         _  = true
RUPStep f (lᶜ ∷ˡ lsᶜ) ss
  with nextIndex f
... | nothing = false
... | just i  = checkLRAT (insert f i (lᶜ ∷ˡ lsᶜ)) ss

RATStep : Formula → Clause → Literal → Clause → Proof → Bool
RATStep f c lᶜ lsᶜ ss
  with nextIndex f
... | nothing = false
... | just i  = checkLRAT (insert f i c) ss

checkLRAT _ []ˡ                  = false
checkLRAT f (del is ∷ˡ ss)       = deleteStep f is ss
checkLRAT f (ext c is iss ∷ˡ ss)
  with checkRUP f c is
... | fail             = false
... | done _           = RUPStep f c ss
... | more []ˡ         = false
... | more (lᶜ ∷ˡ lsᶜ)
  with checkRAT f lᶜ lsᶜ iss
... | false = false
... | true  = RATStep f c lᶜ lsᶜ ss