import Data.Nat

module Proof (bitsᵛ : Data.Nat.ℕ) (bitsᶜ : Data.Nat.ℕ) where

open Data.Nat using (ℕ ; zero ; suc)

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; if_then_else_)
open import Data.Bool.Properties using (not-¬)
open import Data.Empty using (⊥)
open import Data.List using (List) renaming ([] to []ˡ ; _∷_ to _∷ˡ_ ; _++_ to _++ˡ_)
open import Data.List.Relation.Unary.Any using (Any ; here ; there)
open import Data.Maybe using (Maybe ; just ; nothing) renaming (map to mapᵐ)
open import Data.Product using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂ ; ∃ ; map₁ ; map₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using (Vec) renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_)
open import Function using (_$_ ; _∘_ ; id ; case_of_ ; _∋_)
open import Relation.Binary.PropositionalEquality using (
    _≡_ ; _≢_ ; refl ; sym ; trans ; cong ; subst ; inspect ; [_] ;
    module ≡-Reasoning
  )
open import Relation.Nullary using (_because_ ; ofʸ ; ofⁿ ; yes ; no)

open ≡-Reasoning

import Correct as C
import Fast as F

open C bitsᵛ bitsᶜ using (
    Variable ; Literal ; pos ; neg ; Clause ; Formula ;
    Trie ; leaf ; node ; Index ;
    Step ; del ; ext ; Proof ;
    Result ; done ; more ; fail ;
    literalDS ;
    lookup ; insert ; remove ;
    _≟ˡ_ ; flip ; andNot ; removeLiteral ; resolvent ;
    eval ; evalᶜ ; evalˡ
  ) renaming (
    checkRUP′ to C-checkRUP′ ;
    checkRUP to C-checkRUP ;
    clauseCheck₁ to C-clauseCheck₁ ;
    clauseCheck₂ to C-clauseCheck₂ ;
    clauseCheck₃ to C-clauseCheck₃ ;
    checkRAT′ to C-checkRAT′ ;
    checkRAT to C-checkRAT ;
    deleteStep to C-deleteStep ;
    RUPStep to C-RUPStep ;
    RATStep to C-RATStep ;
    checkLRAT to C-checkLRAT
  )

open F bitsᵛ bitsᶜ using (
  ) renaming (
    checkRUP′ to F-checkRUP′ ;
    checkRUP to F-checkRUP ;
    clauseCheck₁ to F-clauseCheck₁ ;
    clauseCheck₂ to F-clauseCheck₂ ;
    clauseCheck₃ to F-clauseCheck₃ ;
    checkRAT′ to F-checkRAT′ ;
    checkRAT to F-checkRAT ;
    deleteStep to F-deleteStep ;
    RUPStep to F-RUPStep ;
    RATStep to F-RATStep ;
    checkLRAT to F-checkLRAT
  )

open import Data.List.Membership.DecSetoid literalDS using (_∈?_)

,-injective : {X Y : Set} → {x₁ x₂ : X} → {y₁ y₂ : Y} → (x₁ , y₁) ≡ (x₂ , y₂) → x₁ ≡ x₂
,-injective refl = refl

more-injective : {S T : Set} → {t₁ t₂ : T} → (Result S T ∋ more t₁) ≡ more t₂ → t₁ ≡ t₂
more-injective refl = refl

faster : {S : Set} → {T : Clause → Set} → Result S (∃ λ (c : Clause) → T c) → Result ⊤ Clause
faster (done _)       = done tt
faster (more (c , _)) = more c
faster fail           = fail

map-nothing′ : {X Y : Set} → {f : X → Y} → {x : Maybe X} → mapᵐ f x ≡ nothing → x ≡ nothing
map-nothing′ {x = nothing} refl = refl

checkRUP′ : ∀ f c is x → C-checkRUP′ f c is ≡ x → F-checkRUP′ f c is ≡ faster x
checkRUP′ _ _ []ˡ       (more (_ , _)) refl = refl
checkRUP′ f c (i ∷ˡ is) x              q
  with lookup f i | inspect (lookup f) i
... | nothing | _ with refl ← q = refl
... | just cᶠ | _
  with andNot cᶠ c | inspect (andNot cᶠ) c
... | []ˡ          | _ with refl ← q = refl
... | _ ∷ˡ _ ∷ˡ ls | _ with refl ← q = refl
... | l ∷ˡ []ˡ     | _
  with C-checkRUP′ f (c ++ˡ flip l ∷ˡ []ˡ) is | inspect (C-checkRUP′ f (c ++ˡ flip l ∷ˡ []ˡ)) is
... | done r | [ eq ] with refl ← q = checkRUP′ f (c ++ˡ flip l ∷ˡ []ˡ) is (done r) eq
... | more r | [ eq ] with refl ← q = checkRUP′ f (c ++ˡ flip l ∷ˡ []ˡ) is (more r) eq
... | fail   | [ eq ] with refl ← q = checkRUP′ f (c ++ˡ flip l ∷ˡ []ˡ) is fail     eq

checkRUP : ∀ f c is x → C-checkRUP f c is ≡ x → F-checkRUP f c is ≡ faster x
checkRUP f c is x p
  with C-checkRUP′ f c is | inspect (C-checkRUP′ f c) is
... | fail   | [ eq ] with refl ← p rewrite checkRUP′ f c is fail     eq = refl
... | more q | [ eq ] with refl ← p rewrite checkRUP′ f c is (more q) eq = refl
... | done q | [ eq ] with refl ← p rewrite checkRUP′ f c is (done q) eq = refl

clauseCheck₁ : ∀ l c → C-clauseCheck₁ l c ≡ nothing → F-clauseCheck₁ l c ≡ false
clauseCheck₁ l c p
  with flip l ∈? c
... | no  _ with () ← p
... | yes _ = refl

¬-clauseCheck₁ : ∀ l c p → C-clauseCheck₁ l c ≡ just p → F-clauseCheck₁ l c ≡ true
¬-clauseCheck₁ l c _ q
  with flip l ∈? c
... | no  _ = refl
... | yes _ with () ← q

clauseCheck₂ : ∀ c₁ c₂ l → C-clauseCheck₂ c₁ c₂ l ≡ nothing → F-clauseCheck₂ c₁ c₂ l ≡ false
clauseCheck₂ []ˡ         _  _ _ = refl
clauseCheck₂ (l₁ ∷ˡ ls₁) c₂ l p
  with l ≟ˡ l₁
... | yes refl = clauseCheck₂ ls₁ c₂ l $ map-nothing′ p
... | no  q
  with flip l₁ ∈? c₂
... | no  r = clauseCheck₂ ls₁ c₂ l $ map-nothing′ p
... | yes _ with () ← p

¬-clauseCheck₂ : ∀ c₁ c₂ l p → C-clauseCheck₂ c₁ c₂ l ≡ just p → F-clauseCheck₂ c₁ c₂ l ≡ true
¬-clauseCheck₂ []ˡ         _  _ _ ()
¬-clauseCheck₂ (l₁ ∷ˡ _)   _  l p q
  with l ≟ˡ l₁
¬-clauseCheck₂ (_ ∷ˡ ls₁)  c₂ l _ _ | yes _
  with C-clauseCheck₂ ls₁ c₂ l | inspect (C-clauseCheck₂ ls₁ c₂) l
... | just r | [ eq ] = ¬-clauseCheck₂ ls₁ c₂ l r eq
¬-clauseCheck₂ (l₁ ∷ˡ _)   c₂ _ _ _ | no  _
  with flip l₁ ∈? c₂
¬-clauseCheck₂ (_ ∷ˡ ls₁)  c₂ l _ _ | no  _ | no  _
  with C-clauseCheck₂ ls₁ c₂ l | inspect (C-clauseCheck₂ ls₁ c₂) l
... | just r | [ eq ] = ¬-clauseCheck₂ ls₁ c₂ l r eq
¬-clauseCheck₂ (_ ∷ˡ _)    _  _ _ _ | no  _ | yes _ = refl

clauseCheck₃ : ∀ f lᶜ lsᶜ c iss iss′ → C-clauseCheck₃ f lᶜ lsᶜ c iss ≡ (iss′ , nothing) →
  F-clauseCheck₃ f lᶜ lsᶜ c iss ≡ (iss′ , false)
clauseCheck₃ _ _  _   _ []ˡ         _    refl = refl
clauseCheck₃ f lᶜ lsᶜ c (is ∷ˡ iss) iss′ p
  with C-checkRUP f (resolvent lᶜ (lᶜ ∷ˡ lsᶜ) c) is
     | inspect (C-checkRUP f (resolvent lᶜ (lᶜ ∷ˡ lsᶜ) c)) is
... | more q | [ eq ]
  with refl ← p
  rewrite checkRUP f (lᶜ ∷ˡ lsᶜ ++ˡ removeLiteral c (flip lᶜ)) is (more q) eq
  = refl
... | fail   | [ eq ]
  with refl ← p
  rewrite checkRUP f (lᶜ ∷ˡ lsᶜ ++ˡ removeLiteral c (flip lᶜ)) is fail     eq
  = refl

¬-clauseCheck₃ : ∀ f lᶜ lsᶜ c iss iss′ p → C-clauseCheck₃ f lᶜ lsᶜ c iss ≡ (iss′ , just p) →
  F-clauseCheck₃ f lᶜ lsᶜ c iss ≡ (iss′ , true)
¬-clauseCheck₃ _ _  _   _ []ˡ         _    _ ()
¬-clauseCheck₃ f lᶜ lsᶜ c (is ∷ˡ iss) iss′ p q
  with C-checkRUP f (resolvent lᶜ (lᶜ ∷ˡ lsᶜ) c) is
     | inspect (C-checkRUP f (resolvent lᶜ (lᶜ ∷ˡ lsᶜ) c)) is
... | done r | [ eq ]
  with refl ← q
  rewrite checkRUP f (lᶜ ∷ˡ lsᶜ ++ˡ removeLiteral c (flip lᶜ)) is (done r) eq
  = refl

checkRAT′ : ∀ n f t lᶜ lsᶜ iss iss′ → C-checkRAT′ n f t lᶜ lsᶜ iss ≡ (iss′ , nothing) →
  F-checkRAT′ n f t lᶜ lsᶜ iss ≡ (iss′ , false)

¬-checkRAT′ : ∀ n f t lᶜ lsᶜ iss iss′ p → C-checkRAT′ n f t lᶜ lsᶜ iss ≡ (iss′ , just p) →
  F-checkRAT′ n f t lᶜ lsᶜ iss ≡ (iss′ , true)

checkRAT′ zero f (just (leaf cˡ)) lᶜ lsᶜ iss iss′ p
  with C-clauseCheck₁ lᶜ cˡ | inspect (C-clauseCheck₁ lᶜ) cˡ
... | just _  | _       with () ← p
... | nothing | [ eq₁ ]
  rewrite clauseCheck₁ lᶜ cˡ eq₁
  with C-clauseCheck₂ lsᶜ cˡ lᶜ | inspect (C-clauseCheck₂ lsᶜ cˡ) lᶜ
... | just _  | _       with () ← p
... | nothing | [ eq₂ ]
  rewrite clauseCheck₂ lsᶜ cˡ lᶜ eq₂
  with C-clauseCheck₃ f lᶜ lsᶜ cˡ iss | inspect (C-clauseCheck₃ f lᶜ lsᶜ cˡ) iss
... | (iss″ , just _)  | _       with ()   ← p
... | (iss″ , nothing) | [ eq₃ ] with refl ← p
  rewrite clauseCheck₃ f lᶜ lsᶜ cˡ iss iss′ eq₃
  = refl
checkRAT′ (suc n) f (just (node tˡ tʳ)) lᶜ lsᶜ iss iss′ p
  with C-checkRAT′ n f tˡ lᶜ lsᶜ iss | inspect (C-checkRAT′ n f tˡ lᶜ lsᶜ) iss
... | iss″ , nothing | [ eq₁ ]
  with refl ← p
  rewrite checkRAT′ n f tˡ lᶜ lsᶜ iss iss″ eq₁
  = refl
... | iss″ , just q  | [ eq₁ ]
  rewrite ¬-checkRAT′ n f tˡ lᶜ lsᶜ iss iss″ q eq₁
  with C-checkRAT′ n f tʳ lᶜ lsᶜ iss″ | inspect (C-checkRAT′ n f tʳ lᶜ lsᶜ) iss″
... | iss‴ , nothing | [ eq₂ ]
  with refl ← p
  rewrite checkRAT′ n f tʳ lᶜ lsᶜ iss″ iss‴ eq₂
  = refl

¬-checkRAT′ zero f nothing          lᶜ lsᶜ iss iss′ p q
  with refl ← q = refl
¬-checkRAT′ zero f (just (leaf cˡ)) lᶜ lsᶜ iss iss′ p q
  with C-clauseCheck₁ lᶜ cˡ | inspect (C-clauseCheck₁ lᶜ) cˡ
... | just r  | [ eq₁ ]
  with refl ← q
  rewrite ¬-clauseCheck₁ lᶜ cˡ r eq₁
  = refl
... | nothing | [ eq₁ ]
  rewrite clauseCheck₁ lᶜ cˡ eq₁
  with C-clauseCheck₂ lsᶜ cˡ lᶜ | inspect (C-clauseCheck₂ lsᶜ cˡ) lᶜ
... | just s  | [ eq₂ ]
  with refl ← q
  rewrite ¬-clauseCheck₂ lsᶜ cˡ lᶜ s eq₂
  = refl
... | nothing | [ eq₂ ]
  rewrite clauseCheck₂ lsᶜ cˡ lᶜ eq₂
  with C-clauseCheck₃ f lᶜ lsᶜ cˡ iss | inspect (C-clauseCheck₃ f lᶜ lsᶜ cˡ) iss
... | (iss″ , just t)  | [ eq₃ ]
  with refl ← q
  rewrite ¬-clauseCheck₃ f lᶜ lsᶜ cˡ iss iss″ t eq₃
  = refl
¬-checkRAT′ (suc n) f nothing             lᶜ lsᶜ iss iss′ p q
  with refl ← q = refl
¬-checkRAT′ (suc n) f (just (node tˡ tʳ)) lᶜ lsᶜ iss iss′ p q
  with C-checkRAT′ n f tˡ lᶜ lsᶜ iss | inspect (C-checkRAT′ n f tˡ lᶜ lsᶜ) iss
... | iss″ , just r | [ eq₁ ]
  rewrite ¬-checkRAT′ n f tˡ lᶜ lsᶜ iss iss″ r eq₁
  with C-checkRAT′ n f tʳ lᶜ lsᶜ iss″ | inspect (C-checkRAT′ n f tʳ lᶜ lsᶜ) iss″
... | iss‴ , just s | [ eq₂ ]
  rewrite ¬-checkRAT′ n f tʳ lᶜ lsᶜ iss″ iss‴ s eq₂
  with refl ← q
  = refl

checkRAT : ∀ f lᶜ lsᶜ iss → C-checkRAT f lᶜ lsᶜ iss ≡ nothing → F-checkRAT f lᶜ lsᶜ iss ≡ false
checkRAT f lᶜ lsᶜ iss p
  with C-checkRAT′ bitsᶜ f f lᶜ lsᶜ iss | inspect (C-checkRAT′ bitsᶜ f f lᶜ lsᶜ) iss
... | iss′ , nothing | [ eq ]
  rewrite checkRAT′ bitsᶜ f f lᶜ lsᶜ iss iss′ eq
  = refl

¬-checkRAT : ∀ f lᶜ lsᶜ iss p → C-checkRAT f lᶜ lsᶜ iss ≡ just p → F-checkRAT f lᶜ lsᶜ iss ≡ true
¬-checkRAT f lᶜ lsᶜ iss p q
  with C-checkRAT′ bitsᶜ f f lᶜ lsᶜ iss | inspect (C-checkRAT′ bitsᶜ f f lᶜ lsᶜ) iss
... | iss′ , just r | [ eq ]
  rewrite ¬-checkRAT′ bitsᶜ f f lᶜ lsᶜ iss iss′ r eq
  = refl

checkLRAT : ∀ f ss → C-checkLRAT f ss ≡ nothing → F-checkLRAT f ss ≡ false

deleteStep : ∀ f is ss → C-deleteStep f is ss ≡ nothing → F-deleteStep f is ss ≡ false
deleteStep f []ˡ       ss p = checkLRAT f ss p
deleteStep f (i ∷ˡ is) ss p
  with C-deleteStep (remove f i) is ss | inspect (C-deleteStep (remove f i) is) ss
... | nothing | [ eq ] = deleteStep (remove f i) is ss eq
... | just _  | _      with () ← p

RUPStep : ∀ f c ss p → C-RUPStep f c ss p ≡ nothing → F-RUPStep f c ss ≡ false
RUPStep f (lᶜ ∷ˡ lsᶜ) ss p q
  with insert f (lᶜ ∷ˡ lsᶜ) | inspect (insert f) (lᶜ ∷ˡ lsᶜ)
... | nothing | _ = refl
... | just f′ | _
  with C-checkLRAT f′ ss | inspect (C-checkLRAT f′) ss
... | nothing | [ eq ] = checkLRAT f′ ss eq

RATStep : ∀ f c lᶜ lsᶜ ss p q → C-RATStep f c lᶜ lsᶜ ss p q ≡ nothing →
  F-RATStep f c lᶜ lsᶜ ss ≡ false
RATStep f c lᶜ lsᶜ ss p q r
  with insert f c | inspect (insert f) c
... | nothing | _ = refl
... | just f′ | _
  with C-checkLRAT f′ ss | inspect (C-checkLRAT f′) ss
... | nothing | [ eq ] = checkLRAT f′ ss eq

checkLRAT _ []ˡ                  _ = refl
checkLRAT f (del is ∷ˡ ss)       p = deleteStep f is ss p
checkLRAT f (ext c is iss ∷ˡ ss) p
  with C-checkRUP f c is | inspect (C-checkRUP f c) is
... | fail                 | [ eq₁ ] rewrite checkRUP f c is fail                   eq₁ = refl
... | done q               | [ eq₁ ] rewrite checkRUP f c is (done q)               eq₁ = RUPStep f c ss q p
... | more ([]ˡ , q)       | [ eq₁ ] rewrite checkRUP f c is (more ([]ˡ , q))       eq₁ = refl
... | more (lᶜ ∷ˡ lsᶜ , q) | [ eq₁ ] rewrite checkRUP f c is (more (lᶜ ∷ˡ lsᶜ , q)) eq₁
  with C-checkRAT f lᶜ lsᶜ iss | inspect (C-checkRAT f lᶜ lsᶜ) iss
... | nothing | [ eq₂ ] rewrite checkRAT f lᶜ lsᶜ iss eq₂ = refl
... | just r  | [ eq₂ ] rewrite ¬-checkRAT f lᶜ lsᶜ iss r eq₂ = RATStep f c lᶜ lsᶜ ss q r p

fast⇒correct′ : ∀ f ss → F-checkLRAT f ss ≡ true → ∃ λ x → C-checkLRAT f ss ≡ just x
fast⇒correct′ f ss p
  with C-checkLRAT f ss | inspect (C-checkLRAT f) ss
... | nothing | [ eq ] = case trans (sym $ checkLRAT f ss eq) p of λ ()
... | just q  | _      = q , refl

fast⇒correct : ∀ f ss → F-checkLRAT f ss ≡ true → ∀ a → eval a f ≡ false
fast⇒correct f ss p with (x , _) ← fast⇒correct′ f ss p = x
