open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (
    IsMagma ; IsSemigroup ; IsMonoid ; IsGroup ; IsAbelianGroup ; IsRing ; IsCommutativeRing
  )
open import Data.Bool using (
    Bool ; true ; false ; _∧_ ; _∨_ ; not ; _xor_ ; if_then_else_
  ) renaming (
    _≟_ to _≟ᵇ_
  )
open import Data.Bool.Properties using (∧-zeroʳ ; ∧-identityʳ ; not-injective)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Nat using (
    ℕ ; zero ; suc ; pred ; _+_ ; _*_ ; _∸_ ; _^_ ; _≤_ ; _≰_ ; z≤n ; s≤s ; _<_ ; _≮_ ; _>_ ; _≯_ ;
    _≥_ ; _≱_ ; NonZero ; ≢-nonZero⁻¹
  ) renaming (
    _≟_ to _≟ⁿ_
  )
open import Data.Nat.DivMod using (
    _/_ ; _%_ ; m≡m%n+[m/n]*n ; n%n≡0 ; m*n%n≡0 ; m*n/n≡m ; m%n<n ; m%n%n≡m%n ; m<n⇒m/n≡0 ;
    m≤n⇒m%n≡m ; [m+kn]%n≡m%n ; +-distrib-/
  )
open import Data.Nat.Properties using (
    ≤-refl ; <-irrefl ; <⇒≢ ; <⇒≤ ; <⇒≱ ; ≤⇒≯ ; ≮⇒≥ ; +-identityʳ ; +-comm ; +-assoc ; +-monoˡ-≤ ;
    +-monoʳ-≤ ; +-monoˡ-< ; +-monoʳ-< ; n<1+n ; m+n∸n≡m ; m∸n+n≡m ; m∸n≤m ; *-suc ; *-zeroʳ ;
    *-identityˡ ; *-identityʳ ; *-comm ; *-assoc ; *-monoˡ-≤ ; *-monoʳ-≤ ; *-distribˡ-+ ;
    module ≤-Reasoning
  )
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; [] ; _∷_ ; replicate ; _++_ ; splitAt ; take ; drop)
open import Data.Vec.Properties using (≡-dec ; ∷-injectiveʳ)
open import Function using (_$_ ; case_of_ ; _∘_)
open import Function.Reasoning
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (
    _≡_ ; _≢_ ; refl ; sym ; ≢-sym ; cong ; trans ; subst ; module ≡-Reasoning
  )
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Algebra using (isMagma)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Negation using (contradiction)

open import Kong.Tactic using (kong)

module Satarash.Word where

--- words ------------------------------------------------------------------------------------------

Word : ℕ → Set
Word = Vec Bool

infix 4 _≟ʷ_

_≟ʷ_ : {i : ℕ} → DecidableEquality (Word i)
_≟ʷ_ {i} = ≡-dec _≟ᵇ_

--- useful helpers ---------------------------------------------------------------------------------

mn≢0 : ∀ m n → .⦃ NonZero m ⦄ → .⦃ NonZero n ⦄ → NonZero (m * n)
mn≢0 (suc m) (suc n) = _

x<m⇒x%m≡x : ∀ {x m} → x < m → .⦃ _ : NonZero m ⦄ → x % m ≡ x
x<m⇒x%m≡x {x} {suc m} (s≤s x≤m-1) = m≤n⇒m%n≡m x≤m-1

%-%-+ˡ : ∀ x y m → .⦃ _ : NonZero m ⦄ → (x % m + y) % m ≡ (x + y) % m
%-%-+ˡ x y m ⦃ m≢0 ⦄ =
  (x % m + y)             % m ≡˘⟨ [m+kn]%n≡m%n (x % m + y) (x / m) m ⟩
  (x % m + y + x / m * m) % m ≡⟨ kong (reorg (x % m) y (x / m * m))  ⟩
  (x % m + x / m * m + y) % m ≡˘⟨ kong (m≡m%n+[m/n]*n x m ⦃ m≢0 ⦄) ⟩
  (x + y)                 % m ∎
  where
  open ≡-Reasoning

  reorg : ∀ x%m y x/m*m → x%m + y + x/m*m ≡ x%m + x/m*m + y
  reorg = solve-∀

%-%-+ʳ : ∀ x y m → .⦃ _ : NonZero m ⦄ → (x + y % m) % m ≡ (x + y) % m
%-%-+ʳ x y m ⦃ m≢0 ⦄ =
  (x + y % m) % m ≡⟨ kong (+-comm x (y % m)) ⟩
  (y % m + x) % m ≡⟨ %-%-+ˡ y x m ⟩
  (y + x)     % m ≡⟨ kong (+-comm y x) ⟩
  (x + y)     % m ∎
  where open ≡-Reasoning

%-%-*ˡ : ∀ x y m → .⦃ _ : NonZero m ⦄ → (x % m * y) % m ≡ (x * y) % m
%-%-*ˡ x y m ⦃ m≢0 ⦄ =
  begin
    (x % m * y)                   % m ≡˘⟨ [m+kn]%n≡m%n (x % m * y) (x / m * y) m ⟩
    (x % m * y + (x / m) * y * m) % m ≡⟨ kong (reorg (x % m) y (x / m) m) ⟩
    ((x % m + x / m * m) * y)     % m ≡˘⟨ kong (m≡m%n+[m/n]*n x m ⦃ m≢0 ⦄) ⟩
    (x * y)                       % m ∎
  where
  open ≡-Reasoning

  reorg : ∀ x%m y x/m m → x%m * y + x/m * y * m ≡ (x%m + x/m * m) * y
  reorg = solve-∀

%-%-*ʳ : ∀ x y m → .⦃ _ : NonZero m ⦄ → (x * (y % m)) % m ≡ (x * y) % m
%-%-*ʳ x y m ⦃ m≢0 ⦄ =
  (x * (y % m)) % m ≡⟨ kong (*-comm x (y % m)) ⟩
  (y % m * x)   % m ≡⟨ %-%-*ˡ y x m ⟩
  (y * x)     % m ≡⟨ kong (*-comm y x) ⟩
  (x * y)     % m ∎
  where open ≡-Reasoning

--- evaluation -------------------------------------------------------------------------------------

bit : Bool → ℕ
bit false = 0
bit true  = 1

bit≤1 : ∀ x → bit x ≤ 1
bit≤1 false = z≤n
bit≤1 true  = s≤s z≤n

bits′ : {i : ℕ} → Word i → ℕ → ℕ
bits′ {zero}  []       a = a
bits′ {suc n} (x ∷ xs) a = bits′ xs (2 * a + bit x)

bits : {i : ℕ} → Word i → ℕ
bits xs = bits′ xs 0

bits′≡0 : ∀ i a → bits′ (replicate {n = i} false) a ≡ a * 2 ^ i
bits′≡0 zero    a = sym (*-identityʳ a)
bits′≡0 (suc i) a =
  begin
    bits′ (replicate {n = i} false) (2 * a + 0) ≡⟨ bits′≡0 i (2 * a + 0) ⟩
    (2 * a + 0) * 2 ^ i                         ≡⟨ reorg a (2 ^ i) ⟩
    a * (2 * 2 ^ i)                             ≡⟨⟩
    a * 2 ^ (suc i)                             ∎
  where
  open ≡-Reasoning

  reorg : ∀ a 2^i → (2 * a + 0) * 2^i ≡ a * (2 * 2^i)
  reorg = solve-∀

bits≡0 : ∀ i → bits (replicate {n = i} false) ≡ 0
bits≡0 i = bits′≡0 i 0

bits′≡2^i : ∀ i a → bits′ (true ∷ replicate {n = i} false) a ≡ a * 2 ^ suc i + 2 ^ i
bits′≡2^i i a =
  begin
    bits′ (replicate {n = i} false) (2 * a + 1) ≡⟨ bits′≡0 i (2 * a + 1) ⟩
    (2 * a + 1) * 2 ^ i                         ≡⟨ reorg a (2 ^ i) ⟩
    a * (2 * 2 ^ i) + 2 ^ i                     ≡⟨⟩
    a * 2 ^ suc i + 2 ^ i                       ∎
  where
  open ≡-Reasoning

  reorg : ∀ a 2^i → (2 * a + 1) * 2^i ≡ a * (2 * 2^i) + 2^i
  reorg = solve-∀

bits≡2^i : ∀ i → bits (true ∷ replicate {n = i} false) ≡ 2 ^ i
bits≡2^i i = bits′≡2^i i 0

bits′<2^i : ∀ {i} xs a → bits′ {i} xs a < a * 2 ^ i + 2 ^ i
bits′<2^i {zero} [] a =
  begin-strict
    a         ≡˘⟨ *-identityʳ a ⟩
    a * 1     <⟨ n<1+n (a * 1) ⟩
    1 + a * 1 ≡⟨ +-comm 1 (a * 1) ⟩
    a * 1 + 1 ∎
  where open ≤-Reasoning

bits′<2^i {suc i} (x ∷ xs) a =
  begin-strict
    bits′ (x ∷ xs) a                ≡⟨⟩
    bits′ xs (2 * a + bit x)        <⟨ bits′<2^i xs (2 * a + bit x) ⟩
    (2 * a + bit x) * 2 ^ i + 2 ^ i ≤⟨ +-monoˡ-≤ (2 ^ i) lemma₂ ⟩
    (2 * a + 1) * 2 ^ i + 2 ^ i     ≡⟨ reorg a (2 ^ i) ⟩
    a * (2 * 2 ^ i) + 2 * 2 ^ i     ≡⟨⟩
    a * 2 ^ suc i + 2 ^ suc i       ∎
  where
  open ≤-Reasoning

  lemma₁ : 2 * a + bit x ≤ 2 * a + 1
  lemma₁ = +-monoʳ-≤ (2 * a) (bit≤1 x)

  lemma₂ : (2 * a + bit x) * 2 ^ i ≤ (2 * a + 1) * 2 ^ i
  lemma₂ = *-monoˡ-≤ (2 ^ i) lemma₁

  reorg : ∀ a 2^i → (2 * a + 1) * 2^i + 2^i ≡ a * (2 * 2^i) + 2 * 2^i
  reorg = solve-∀

bits<2^i : ∀ {i} xs → bits {i} xs < 2 ^ i
bits<2^i {i} xs = bits′<2^i xs 0

bits′SplitAcc : ∀ {i} xs a b → bits′ {i} xs (a + b) ≡ bits′ xs a + 2 ^ i * b
bits′SplitAcc {zero}  []       a b = kong (sym (+-identityʳ b))
bits′SplitAcc {suc i} (x ∷ xs) a b =
  begin
    bits′ xs (2 * (a + b) + bit x)             ≡⟨ kong (reorg₁ a b (bit x)) ⟩
    bits′ xs (2 * a + bit x + 2 * b)           ≡⟨ bits′SplitAcc xs (2 * a + bit x) (2 * b) ⟩
    bits′ xs (2 * a + bit x) + 2 ^ i * (2 * b) ≡⟨ kong (reorg₂ (2 ^ i) b) ⟩
    bits′ xs (2 * a + bit x) + 2 * 2 ^ i * b   ∎
  where
  open ≡-Reasoning

  reorg₁ : ∀ a b bit-x → 2 * (a + b) + bit-x ≡ 2 * a + bit-x + 2 * b
  reorg₁ = solve-∀

  reorg₂ : ∀ 2^i b → 2^i * (2 * b) ≡ 2 * 2^i * b
  reorg₂ = solve-∀

bits′SplitWord : ∀ {i k} xs ys a → bits′ (xs ++ ys) a ≡ bits′ {k} ys (bits′ {i} xs a)
bits′SplitWord {zero}  {k} []       ys a = refl
bits′SplitWord {suc i} {k} (x ∷ xs) ys a = bits′SplitWord xs ys (2 * a + bit x)

module _ where
  private
    lemma₁ : ∀ {i} xs ys {ax ay} → ax < ay → bits′ {i} xs ax < bits′ {i} ys ay
    lemma₁ {i} xs ys {ax} {ay} ax<ay =
      begin-strict
        bits′ xs ax                 ≡⟨ bits′SplitAcc xs 0 ax ⟩
        bits′ xs 0 + 2 ^ i * ax     <⟨ +-monoˡ-< (2 ^ i * ax) (bits′<2^i xs 0) ⟩
        (2 ^ i)    + 2 ^ i * ax     ≡˘⟨ *-suc (2 ^ i) ax ⟩
                     2 ^ i * suc ax ≤⟨ *-monoʳ-≤ (2 ^ i) ax<ay ⟩
                     2 ^ i * ay     ≡⟨⟩
        0          + 2 ^ i * ay     ≤⟨ +-monoˡ-≤ (2 ^ i * ay) z≤n ⟩
        bits′ ys 0 + 2 ^ i * ay     ≡˘⟨ bits′SplitAcc ys 0 ay ⟩
        bits′ ys ay                 ∎
      where open ≤-Reasoning

    lemma₂ : ∀ a → a + 0 < a + 1
    lemma₂ a = +-monoʳ-< a ≤-refl

    lemma₃ : ∀ {i} xs ys a → bits′ {i} xs (a + 0) < bits′ {i} ys (a + 1)
    lemma₃ xs ys a = lemma₁ xs ys (lemma₂ a)

  bits′Injective : ∀ {i xs ys a} → bits′ {i} xs a ≡ bits′ {i} ys a → xs ≡ ys
  bits′Injective {zero}  {[]}         {[]}         {a} p = refl
  bits′Injective {suc i} {false ∷ xs} {false ∷ ys} {a} p = cong (false ∷_) (bits′Injective p)
  bits′Injective {suc i} {true ∷ xs}  {true ∷ ys}  {a} p = cong (true ∷_) (bits′Injective p)
  bits′Injective {suc i} {false ∷ xs} {true ∷ ys}  {a} p = contradiction p ¬p
    where ¬p = <⇒≢ (lemma₃ xs ys (2 * a))
  bits′Injective {suc i} {true ∷ xs}  {false ∷ ys} {a} p = contradiction p ¬p
    where ¬p = ≢-sym (<⇒≢ (lemma₃ ys xs (2 * a)))

bitsInjective : ∀ {n} {x y : Word n} → bits x ≡ bits y → x ≡ y
bitsInjective = bits′Injective

--- adder ------------------------------------------------------------------------------------------

_+ᵇ_+_ : (x y c : Bool) → Word 2
_+ᵇ_+_ x y c = (x ∧ y ∨ x ∧ c ∨ y ∧ c) ∷ (x xor y xor c) ∷ []

+ᵇ+-✓ : ∀ x y c → bits (x +ᵇ y + c) ≡ bit x + bit y + bit c
+ᵇ+-✓ false false false = refl
+ᵇ+-✓ false false true  = refl
+ᵇ+-✓ false true  false = refl
+ᵇ+-✓ false true  true  = refl
+ᵇ+-✓ true  false false = refl
+ᵇ+-✓ true  false true  = refl
+ᵇ+-✓ true  true  false = refl
+ᵇ+-✓ true  true  true  = refl

--- logical operations -----------------------------------------------------------------------------

~ : {i : ℕ} → (xs : Word i) → Word i
~ []       = []
~ (x ∷ xs) = not x ∷ ~ xs

infixl 6 _∧ʷ_

_∧ʷ_ : {i : ℕ} → (xs ys : Word i) → Word i
_∧ʷ_ []       []       = []
_∧ʷ_ (x ∷ xs) (y ∷ ys) = x ∧ y ∷ xs ∧ʷ ys

∧ʷ-zeroʳ : ∀ {i} xs → xs ∧ʷ (replicate {n = i} false) ≡ replicate false
∧ʷ-zeroʳ {zero}  []       = refl
∧ʷ-zeroʳ {suc i} (x ∷ xs) =
  x ∧ false ∷ (xs ∧ʷ replicate false) ≡⟨ kong (∧-zeroʳ x) ⟩
  false ∷ (xs ∧ʷ replicate false)     ≡⟨ kong (∧ʷ-zeroʳ xs) ⟩
  replicate false                     ∎
  where open ≡-Reasoning

∧ʷ-identityʳ : ∀ {i} xs → xs ∧ʷ (replicate {n = i} true) ≡ xs
∧ʷ-identityʳ {zero}  []       = refl
∧ʷ-identityʳ {suc i} (x ∷ xs) =
  x ∧ true ∷ xs ∧ʷ (replicate true) ≡⟨ kong (∧-identityʳ x) ⟩
  x ∷ xs ∧ʷ (replicate true)        ≡⟨ kong (∧ʷ-identityʳ xs) ⟩
  x ∷ xs                            ∎
  where open ≡-Reasoning

infixl 5 _∨ʷ_

_∨ʷ_ : {i : ℕ} → (xs ys : Word i) → Word i
_∨ʷ_ []       []       = []
_∨ʷ_ (x ∷ xs) (y ∷ ys) = (x ∨ y) ∷ (xs ∨ʷ ys)

infixl 5 _xorʷ_

_xorʷ_ : {i : ℕ} → (xs ys : Word i) → Word i
_xorʷ_ []       []       = []
_xorʷ_ (x ∷ xs) (y ∷ ys) = (x xor y) ∷ (xs xorʷ ys)

--- truncation -------------------------------------------------------------------------------------

instance
  2^i≢0 : ∀ {i} → NonZero (2 ^ i)
  2^i≢0 {zero}  = _
  2^i≢0 {suc i} = mn≢0 2 (2 ^ i) ⦃ _ ⦄ ⦃ 2^i≢0 {i} ⦄

bits-/ : ∀ {i k} xs ys → .⦃ _ : NonZero (2 ^ k) ⦄ → bits {i + k} (xs ++ ys) / 2 ^ k ≡ bits {i} xs
bits-/ {i} {k} xs ys ⦃ d≢0 ⦄ =
  begin-equality
    bits (xs ++ ys) / d           ≡⟨ kong (bits′SplitWord xs ys 0) ⟩
    bits′ ys (bits xs) / d        ≡⟨ kong (bits′SplitAcc ys 0 (bits xs)) ⟩
    (bits ys + d * bits xs) / d   ≡⟨ +-distrib-/ (bits ys) (d * bits xs) lemma ⟩
    bits ys / d + d * bits xs / d ≡⟨ kong (m<n⇒m/n≡0 (bits<2^i ys)) ⟩
    d * bits xs / d               ≡⟨ kong (*-comm d (bits xs)) ⟩
    bits xs * d / d               ≡⟨ m*n/n≡m (bits xs) d ⟩
    bits xs                       ∎
  where
  open ≤-Reasoning

  d = 2 ^ k

  lemma : bits ys % d + d * bits xs % d < d
  lemma =
    begin-strict
      bits ys % d + d * bits xs % d ≡⟨ kong (*-comm d (bits xs)) ⟩
      bits ys % d + bits xs * d % d ≡⟨ kong (m*n%n≡0 (bits xs) d ⦃ d≢0 ⦄) ⟩
      bits ys % d + 0               ≡⟨ +-identityʳ (bits ys % d) ⟩
      bits ys % d                   <⟨ m%n<n (bits ys) d ⟩
      d                             ∎

/ʷ2^′ : {i : ℕ} → (k : ℕ) → (xs : Word (i + k)) → Word i
/ʷ2^′ {i} k xs = take i xs

infixl 7 /ʷ2^′
syntax /ʷ2^′ k xs = xs /ʷ2^ k

/ʷ2^-✓ : ∀ {i} k xs → .⦃ _ : NonZero (2 ^ k) ⦄ → bits (xs /ʷ2^ k) ≡ bits xs / 2 ^ k
/ʷ2^-✓ {i} k xs
  with hs , ls , refl ← splitAt i xs
  = sym (bits-/ hs ls)

bits-% : ∀ {i k} xs ys → .⦃ _ : NonZero (2 ^ k) ⦄ → bits {i + k} (xs ++ ys) % 2 ^ k ≡ bits {k} ys
bits-% {i} {k} xs ys =
  begin
    bits (xs ++ ys) % d          ≡⟨ kong (bits′SplitWord xs ys 0) ⟩
    bits′ ys (bits xs) % d       ≡⟨ kong (bits′SplitAcc ys 0 (bits xs)) ⟩
    (bits ys + d * bits xs) % d  ≡⟨ kong (*-comm d (bits xs)) ⟩
    (bits ys + bits xs * d) % d  ≡⟨ [m+kn]%n≡m%n (bits ys) (bits xs) d ⟩
    bits ys % d                  ≡⟨ x<m⇒x%m≡x (bits<2^i ys) ⟩
    bits ys                      ∎
  where
  d = 2 ^ k

  open ≡-Reasoning

%ʷ2^′ : {i : ℕ} → (k : ℕ) → (xs : Word (i + k)) → Word k
%ʷ2^′ {i} k xs = drop i xs

infixl 7 %ʷ2^′
syntax %ʷ2^′ k xs = xs %ʷ2^ k

%ʷ2^-✓ : ∀ {i} k xs → .⦃ _ : NonZero (2 ^ k) ⦄ → bits (xs %ʷ2^ k) ≡ bits xs % 2 ^ k
%ʷ2^-✓ {i} k xs
  with hs , ls , refl ← splitAt i xs
  = sym (bits-% hs ls)

modDiv : ∀ {i k} xs ys → .⦃ _ : NonZero (2 ^ k) ⦄ →
  bits (xs ++ ys) ≡ bits {k} ys + bits {i} xs * 2 ^ k
modDiv {i} {k} xs ys ⦃ d≢0 ⦄ =
  begin
    bits (xs ++ ys)                               ≡⟨ m≡m%n+[m/n]*n (bits (xs ++ ys)) d ⟩
    bits (xs ++ ys) % d + bits (xs ++ ys) / d * d ≡⟨ kong (bits-% xs ys ⦃ d≢0 ⦄) ⟩
    bits ys + bits (xs ++ ys) / d * d             ≡⟨ kong (bits-/ xs ys ⦃ d≢0 ⦄) ⟩
    bits ys + bits xs * d                         ∎
  where
  d = 2 ^ k

  open ≡-Reasoning

--- padding ----------------------------------------------------------------------------------------

infixl 7 _*ʷ2^_

_*ʷ2^_ : {i : ℕ} → (xs : Word i) → (k : ℕ) → Word (i + k)
_*ʷ2^_ xs k = xs ++ replicate false

*ʷ2^-✓ : ∀ {i} xs k → bits (xs *ʷ2^ k) ≡ bits {i} xs * 2 ^ k
*ʷ2^-✓ {i} xs k =
  begin
    bits (xs *ʷ2^ k)                              ≡⟨ modDiv xs (replicate false) ⦃ 2^i≢0 {k} ⦄ ⟩
    bits (replicate {n = k} false) + bits xs * d  ≡⟨ kong (bits≡0 k) ⟩
    bits xs * d                                   ∎
  where
  d = 2 ^ k

  open ≡-Reasoning

_0⋯_ : (i : ℕ) → {k : ℕ} → (xs : Word k) → Word (i + k)
_0⋯_ i {k} xs = replicate false ++ xs

0⋯-✓ : ∀ i {k} xs → bits (i 0⋯ xs) ≡ bits {k} xs
0⋯-✓ i {k} xs =
  begin
    bits (i 0⋯ xs)                                   ≡⟨ modDiv (replicate {n = i} false) xs ⦃ 2^i≢0 {k} ⦄ ⟩
    bits xs + bits (replicate {n = i} false) * 2 ^ k ≡⟨ kong (bits≡0 i) ⟩
    bits xs + 0                                      ≡⟨ +-identityʳ (bits xs) ⟩
    bits xs                                          ∎
  where open ≡-Reasoning

--- addition ---------------------------------------------------------------------------------------

_+ʷ_+_ : {i : ℕ} → (xs ys : Word i) → (c : Bool) → Word (suc i)
_+ʷ_+_ {zero}  []       []       c = c ∷ []
_+ʷ_+_ {suc i} (x ∷ xs) (y ∷ ys) c =
  case xs +ʷ ys + c of λ where
    (z ∷ zs) → x +ᵇ y + z ++ zs

+ʷ+-✓ : ∀ {i} xs ys c → bits (xs +ʷ ys + c) ≡ bits {i} xs + bits ys + bit c
+ʷ+-✓ {zero}  []       []       c = refl
+ʷ+-✓ {suc i} (x ∷ xs) (y ∷ ys) c with xs +ʷ ys + c | +ʷ+-✓ xs ys c
+ʷ+-✓ {suc i} (x ∷ xs) (y ∷ ys) c    | z ∷ zs       | rec           =
  begin
    bits (x +ᵇ y + z ++ zs)                                           ≡⟨⟩
    bits′ zs (bits (x +ᵇ y + z))                                      ≡⟨ kong (+ᵇ+-✓ x y z) ⟩
    bits′ zs (bit x + bit y + bit z)                                  ≡⟨ kong (+-comm (bit x + bit y) (bit z)) ⟩
    bits′ zs (bit z + (bit x + bit y))                                ≡⟨ bits′SplitAcc zs (bit z) (bit x + bit y) ⟩
    bits′ zs (bit z) + 2 ^ i * (bit x + bit y)                        ≡⟨ kong rec ⟩
    bits′ xs 0 + bits′ ys 0 + bit c + 2 ^ i * (bit x + bit y)         ≡⟨ reorg (bits′ xs 0) (bits′ ys 0) (bit c) (2 ^ i) (bit x) (bit y) ⟩
    bits′ xs 0 + 2 ^ i * bit x + (bits′ ys 0 + 2 ^ i * bit y) + bit c ≡˘⟨ kong (bits′SplitAcc xs 0 (bit x)) ⟩
    bits′ xs (bit x) + (bits′ ys 0 + 2 ^ i * bit y) + bit c           ≡˘⟨ kong (bits′SplitAcc ys 0 (bit y)) ⟩
    bits′ xs (bit x) + bits′ ys (bit y) + bit c                       ≡⟨⟩
    bits (x ∷ xs) + bits (y ∷ ys) + bit c                             ∎
  where
  open ≡-Reasoning

  reorg : ∀ xs ys c 2^i x y → xs + ys + c + 2^i * (x + y) ≡ xs + 2^i * x + (ys + 2^i * y) + c
  reorg = solve-∀

infixl 6 _⊞_

_⊞_ : {i : ℕ} → (xs ys : Word i) → Word i
_⊞_ {i} xs ys = (xs +ʷ ys + false) %ʷ2^ i

⊞-✓ : ∀ {i} xs ys → .⦃ _ : NonZero (2 ^ i) ⦄ → bits {i} (xs ⊞ ys) ≡ (bits xs + bits ys) % 2 ^ i
⊞-✓ {i} xs ys =
  begin
    bits (xs ⊞ ys)              ≡⟨ %ʷ2^-✓ i (xs +ʷ ys + false) ⟩
    bits (xs +ʷ ys + false) % d ≡⟨ cong (_% d) (+ʷ+-✓ xs ys false) ⟩
    (bits xs + bits ys + 0) % d ≡⟨ cong (_% d) (+-identityʳ (bits xs + bits ys)) ⟩
    (bits xs + bits ys) % d     ∎
  where
  open ≡-Reasoning

  d = 2 ^ i

--- negation ---------------------------------------------------------------------------------------

↕′_ : {i : ℕ} → (xs : Word i) → Word (suc i)
↕′_ {zero}  []       = true ∷ []
↕′_ {suc i} (x ∷ xs) =
  case ↕′ xs of λ where
    (z ∷ zs) → false +ᵇ not x + z ++ zs

↕′-✓ : ∀ {i} xs → bits (↕′ xs) ≡ 2 ^ i ∸ bits {i} xs
↕′-✓ {i} xs =
  begin
    bits (↕′ xs)                          ≡⟨ lemma₂ xs ⟩
    bits (~ xs) + 1                       ≡˘⟨ m+n∸n≡m (bits (~ xs) + 1) (bits xs) ⟩
    bits (~ xs) + 1 + bits xs ∸ bits xs   ≡⟨ kong (+-comm (bits (~ xs) + 1) (bits xs)) ⟩
    bits xs + (bits (~ xs) + 1) ∸ bits xs ≡⟨ kong (lemma₄ xs) ⟩
    d ∸ bits xs                           ∎
  where
  open ≡-Reasoning

  d = 2 ^ i

  lemma₁ : ∀ {i} xs → ↕′ xs ≡ replicate {n = i} false +ʷ ~ xs + true
  lemma₁ {zero}  []       = refl
  lemma₁ {suc i} (x ∷ xs) with ↕′ xs  | replicate false +ʷ ~ xs + true | lemma₁ xs
  lemma₁ {suc i} (x ∷ xs)    | z ∷ zs | z ∷ zs                         | refl      = refl

  lemma₂ : ∀ {i} xs → bits (↕′ xs) ≡ bits {i} (~ xs) + 1
  lemma₂ {i} xs =
    begin
      bits (↕′ xs)                                     ≡⟨ kong (lemma₁ xs) ⟩
      bits (replicate false +ʷ (~ xs) + true)          ≡⟨ +ʷ+-✓ (replicate false) (~ xs) true ⟩
      bits (replicate {n = i} false) + bits (~ xs) + 1 ≡⟨ kong (bits≡0 i) ⟩
      bits (~ xs) + 1                                  ∎

  lemma₃ : ∀ {i} xs → xs +ʷ ~ xs + true ≡ true ∷ replicate {n = i} false
  lemma₃ {zero}  []           = refl
  lemma₃ {suc i} (x ∷ xs)     with xs +ʷ ~ xs + true | lemma₃ xs
  lemma₃ {suc i} (true ∷ xs)     | z ∷ zs            | refl      = refl
  lemma₃ {suc i} (false ∷ xs)    | z ∷ zs            | refl      = refl

  lemma₄ : ∀ {i} xs → bits {i} xs + (bits (~ xs) + 1) ≡ 2 ^ i
  lemma₄ {i} xs =
    begin
      bits {i} xs + (bits (~ xs) + 1)       ≡˘⟨ +-assoc (bits xs) (bits (~ xs)) 1 ⟩
      bits {i} xs + bits (~ xs) + 1         ≡˘⟨ +ʷ+-✓ xs (~ xs) true ⟩
      bits (xs +ʷ (~ xs) + true)            ≡⟨ cong bits (lemma₃ xs) ⟩
      bits (true ∷ replicate {n = i} false) ≡⟨ bits≡2^i i ⟩
      2 ^ i                                 ∎

infix 8 ↕_

↕_ : {i : ℕ} → (xs : Word i) → Word i
↕_ {i} xs = ↕′ xs %ʷ2^ i

↕-✓ : ∀ {i} xs → .⦃ _ : NonZero (2 ^ i) ⦄ → bits {i} (↕ xs) ≡ (2 ^ i ∸ bits xs) % 2 ^ i
↕-✓  {i} xs =
  begin
    bits (↕ xs)       ≡⟨ %ʷ2^-✓ i (↕′ xs) ⟩
    bits (↕′ xs) % d  ≡⟨ cong (_% d) (↕′-✓ xs) ⟩
    (d ∸ bits xs) % d ∎
  where
  open ≡-Reasoning

  d = 2 ^ i

--- subtraction ------------------------------------------------------------------------------------

infixl 6 _⊟_

_⊟_ : {i : ℕ} → (xs ys : Word i) → Word i
_⊟_ {i} xs ys = xs ⊞ (↕ ys)

⊟-✓ : ∀ {i} xs ys → .⦃ _ : NonZero (2 ^ i) ⦄ →
  bits {i} (xs ⊟ ys) ≡ (bits xs + (2 ^ i ∸ bits ys)) % 2 ^ i
⊟-✓ {i} xs ys ⦃ 2^i≢0 ⦄ =
  begin
    bits (xs ⊟ ys)                    ≡⟨ %ʷ2^-✓ i (xs ⊞ (↕ ys)) ⟩
    bits (xs ⊞ (↕ ys)) % d            ≡⟨ kong (⊞-✓ xs (↕ ys) ⦃ 2^i≢0 ⦄) ⟩
    (bits xs + bits (↕ ys)) % d % d   ≡⟨ m%n%n≡m%n (bits xs + bits (↕ ys)) d ⟩
    (bits xs + bits (↕ ys)) % d       ≡⟨ kong (↕-✓ ys ⦃ 2^i≢0 ⦄) ⟩
    (bits xs + (d ∸ bits ys) % d) % d ≡⟨ %-%-+ʳ (bits xs) (d ∸ bits ys) d ⟩
    (bits xs + (d ∸ bits ys)) % d     ∎
  where
  open ≡-Reasoning

  d = 2 ^ i

--- multiplication ---------------------------------------------------------------------------------

++-swap : (i k : ℕ) → (xs : Word (i + k)) → Word (k + i)
++-swap i k = subst (Word) (+-comm i k)

++-swap-✓ : ∀ i k xs → bits (++-swap i k xs) ≡ bits xs
++-swap-✓ i k xs rewrite +-comm i k = refl

infixl 7 _*ʷ_

_*ʷ_ : {i k : ℕ} → (xs : Word i) → (ys : Word k) → Word (k + i)
_*ʷ_ {i} {zero}  xs []       = replicate false
_*ʷ_ {i} {suc k} xs (y ∷ ys) = (xs *ʷ ys) +ʷ (xs′ ∧ʷ replicate y) + false
  where xs′ = ++-swap i k (xs *ʷ2^ k)

*ʷ-✓ : ∀ {i k} xs ys → bits (xs *ʷ ys) ≡ bits {i} xs * bits {k} ys
*ʷ-✓ {i} {zero}  xs []       =
  begin
    bits {i} (replicate false) ≡⟨ bits≡0 i ⟩
    0                          ≡˘⟨ *-zeroʳ (bits xs) ⟩
    bits xs * 0                ∎
  where open ≡-Reasoning

*ʷ-✓ {i} {suc k} xs (false ∷ ys) =
  begin
    bits ((xs *ʷ ys) +ʷ (xs′ ∧ʷ replicate false) + false) ≡⟨ kong (∧ʷ-zeroʳ xs′) ⟩
    bits ((xs *ʷ ys) +ʷ replicate false + false)          ≡⟨ +ʷ+-✓ (xs *ʷ ys) (replicate false) false ⟩
    bits (xs *ʷ ys) + bits {k + i} (replicate false) + 0  ≡⟨ kong (bits≡0 (k + i)) ⟩
    bits (xs *ʷ ys) + 0 + 0                               ≡⟨ kong (*ʷ-✓ xs ys) ⟩
    bits xs * bits ys + 0 + 0                             ≡⟨ reorg (bits xs * bits ys) ⟩
    bits xs * bits ys                                     ≡⟨⟩
    bits xs * bits (false ∷ ys)                           ∎
  where
  open ≡-Reasoning

  reorg : ∀ x → x + 0 + 0 ≡ x
  reorg = solve-∀

  xs′ = ++-swap i k (xs *ʷ2^ k)

*ʷ-✓ {i} {suc k} xs (true ∷ ys) =
  begin
    bits ((xs *ʷ ys) +ʷ (xs′ ∧ʷ replicate true) + false) ≡⟨ kong (∧ʷ-identityʳ xs′) ⟩
    bits ((xs *ʷ ys) +ʷ xs′ + false)                     ≡⟨ +ʷ+-✓ (xs *ʷ ys) xs′ false ⟩
    bits (xs *ʷ ys) + bits xs′ + 0                       ≡⟨ kong (++-swap-✓ i k (xs *ʷ2^ k)) ⟩
    bits (xs *ʷ ys) + bits (xs *ʷ2^ k) + 0               ≡⟨ kong (*ʷ-✓ xs ys) ⟩
    bits xs * bits ys + bits (xs *ʷ2^ k) + 0             ≡⟨ kong (*ʷ2^-✓ xs k) ⟩
    bits xs * bits ys + bits xs * 2 ^ k + 0              ≡⟨ reorg (bits xs) (bits ys) (2 ^ k) ⟩
    bits xs * (bits ys + 2 ^ k * 1)                      ≡˘⟨ kong (bits′SplitAcc ys 0 1) ⟩
    bits xs * bits′ ys 1                                 ≡⟨⟩
    bits xs * bits (true ∷ ys)                           ∎
  where
  open ≡-Reasoning

  xs′ = ++-swap i k (xs *ʷ2^ k)

  reorg : ∀ bxs bys 2^k → bxs * bys + bxs * 2^k + 0 ≡ bxs * (bys + 2^k * 1)
  reorg = solve-∀

infixl 7 _⊠_

_⊠_ : {i k : ℕ} → (xs : Word i) → (ys : Word k) → Word i
_⊠_ {i} {k} xs ys = xs *ʷ ys %ʷ2^ i

⊠-✓ : ∀ {i k} xs ys → .⦃ _ : NonZero (2 ^ i) ⦄ →
  bits (xs ⊠ ys) ≡ (bits {i} xs * bits {k} ys) % 2 ^ i
⊠-✓ {i} {k} xs ys =
  begin
    bits (xs ⊠ ys)         ≡⟨⟩
    bits (xs *ʷ ys %ʷ2^ i) ≡⟨ %ʷ2^-✓ i (xs *ʷ ys) ⟩
    bits (xs *ʷ ys) % d    ≡⟨ kong (*ʷ-✓ xs ys) ⟩
    bits xs * bits ys % d  ∎
  where
  open ≡-Reasoning

  d = 2 ^ i

--- equal ------------------------------------------------------------------------------------------

infix 4 _≡ʷ_

_≡ʷ_ : {i : ℕ} → Word i → Word i → Bool
[]     ≡ʷ []     = true
x ∷ xs ≡ʷ y ∷ ys = not (x xor y) ∧ (xs ≡ʷ ys)

≡ʷ-✓₁ : ∀ {i} {x y : Word i} → (x ≡ʷ y) ≡ true → x ≡ y
≡ʷ-✓₁ {zero}  {[]}         {[]}         refl = refl
≡ʷ-✓₁ {suc i} {false ∷ xs} {false ∷ ys} p    = cong (false ∷_) (≡ʷ-✓₁ p)
≡ʷ-✓₁ {suc i} {false ∷ xs} {true ∷ ys}  ()
≡ʷ-✓₁ {suc i} {true ∷ xs}  {false ∷ ys} ()
≡ʷ-✓₁ {suc i} {true ∷ xs}  {true ∷ ys}  p    = cong (true ∷_) (≡ʷ-✓₁ p)

≡ʷ-✓₂ : ∀ {i} {x y : Word i} → (x ≡ʷ y) ≡ false → x ≢ y
≡ʷ-✓₂ {zero}  {[]}         {[]}         ()
≡ʷ-✓₂ {suc i} {false ∷ xs} {false ∷ ys} p    = ≡ʷ-✓₂ p ∘ ∷-injectiveʳ
≡ʷ-✓₂ {suc i} {false ∷ xs} {true ∷ ys}  refl = λ ()
≡ʷ-✓₂ {suc i} {true ∷ xs}  {false ∷ ys} refl = λ ()
≡ʷ-✓₂ {suc i} {true ∷ xs}  {true ∷ ys}  p    = ≡ʷ-✓₂ p ∘ ∷-injectiveʳ

--- not equal --------------------------------------------------------------------------------------

infix 4 _≢ʷ_

_≢ʷ_ : {i : ℕ} → Word i → Word i → Bool
x ≢ʷ y = not (x ≡ʷ y)

≢ʷ-✓₁ : ∀ {i} {x y : Word i} → (x ≢ʷ y) ≡ true → x ≢ y
≢ʷ-✓₁ p = ≡ʷ-✓₂ (not-injective p)

≢ʷ-✓₂ : ∀ {i} {x y : Word i} → (x ≢ʷ y) ≡ false → x ≡ y
≢ʷ-✓₂ p = ≡ʷ-✓₁ (not-injective p)

--- less than --------------------------------------------------------------------------------------

infix 4 _<ʷ_

_<ʷ_ : {i : ℕ} → Word i → Word i → Bool
x <ʷ y =
  case (false ∷ x) ⊞ ↕′ y of λ where
    (c ∷ _) → not c

module _ where
  private
    lem₁ : ∀ {i} x y → bits {i} x + (2 ^ i ∸ bits {i} y) < 2 ^ suc i
    lem₁ {i} x y =
      begin-strict
        bits x + (2 ^ i ∸ bits y) <⟨ +-monoˡ-< (2 ^ i ∸ bits y) (bits<2^i x) ⟩
        2 ^ i  + (2 ^ i ∸ bits y) ≤⟨ +-monoʳ-≤ (2 ^ i) (m∸n≤m (2 ^ i) (bits y)) ⟩
        2 ^ i  + 2 ^ i            ≡⟨ reorg (2 ^ i) ⟩
        2 ^ suc i                 ∎
      where
      open ≤-Reasoning

      reorg : ∀ 2^i → 2^i + 2^i ≡ 2^i + (2^i + 0)
      reorg = solve-∀

    lem₂ : ∀ {i} x y → .⦃ _ : NonZero (2 ^ suc i) ⦄ →
      bits {suc i} ((false ∷ x) ⊞ ↕′ y) ≡ bits x + (2 ^ i ∸ bits y)
    lem₂ {i} x y =
      begin
        bits ((false ∷ x) ⊞ ↕′ y)                    ≡⟨ ⊞-✓ (false ∷ x) (↕′ y) ⟩
        (bits (false ∷ x) + bits (↕′ y)) % 2 ^ suc i ≡⟨⟩
        (bits x + bits (↕′ y)) % 2 ^ suc i           ≡⟨ kong (↕′-✓ y) ⟩
        (bits x + (2 ^ i ∸ bits y)) % 2 ^ suc i      ≡⟨ x<m⇒x%m≡x (lem₁ x y) ⟩
        bits x + (2 ^ i ∸ bits y)                    ∎
      where open ≡-Reasoning

    lem₃ : ∀ i {n x} → n ≡ bits {i} x → n < 2 ^ i
    lem₃ i {n} {x} refl = bits<2^i x

    lem₄ : ∀ i {n x} → n ≡ bits {suc i} (true ∷ x) → 2 ^ i ≤ n
    lem₄ i {n} {x} refl =
      begin
        2 ^ i              ≡⟨⟩
        0 + 2 ^ i          ≤⟨ +-monoˡ-≤ (2 ^ i) z≤n ⟩
        bits x + 2 ^ i     ≡˘⟨ kong (*-identityʳ (2 ^ i)) ⟩
        bits x + 2 ^ i * 1 ≡˘⟨ bits′SplitAcc x 0 1 ⟩
        bits′ x 1          ≡⟨⟩
        bits (true ∷ x)    ∎
      where open ≤-Reasoning

    lem₅ : ∀ {m n o} → o < m → m ≤ n + (m ∸ o) → o ≤ n
    lem₅ {m}     {n}     {zero}  p₁       p₂       = z≤n
    lem₅ {suc m} {zero}  {suc o} p₁       p₂       = contradiction p₂ (≤⇒≯ (m∸n≤m m o))
    lem₅ {suc m} {suc n} {suc o} (s≤s p₁) (s≤s p₂) = s≤s (lem₅ p₁ p₂)

    lem₆ : ∀ {m n o} → n + (m ∸ o) < m → n < o
    lem₆ {suc m} {n}     {zero}  (s≤s p) = contradiction p (<⇒≱ loc)
      where
      loc : m < n + suc m
      loc =
        begin-strict
          m         <⟨ n<1+n m ⟩
          suc m     ≤⟨ +-monoˡ-≤ (suc m) z≤n ⟩
          n + suc m ∎
        where open ≤-Reasoning
    lem₆ {suc m} {zero}  {suc o} p       = s≤s z≤n
    lem₆ {suc m} {suc n} {suc o} (s≤s p) = s≤s (lem₆ p)

  <ʷ-✓₁ : ∀ {i x y} → (x <ʷ y) ≡ true → bits {i} x < bits y
  <ʷ-✓₁ {i} {x} {y} p    with (false ∷ x) ⊞ ↕′ y in eq
  <ʷ-✓₁ {i} {x} {y} ()      | (true ∷ _)
  <ʷ-✓₁ {i} {x} {y} refl    | (false ∷ r) = loc₃
    where
    loc₁ : bits x + (2 ^ i ∸ bits y) ≡ bits r
    loc₁ = trans (sym (lem₂ x y ⦃ 2^i≢0 {suc i} ⦄)) (cong bits eq)

    loc₂ : bits x + (2 ^ i ∸ bits y) < 2 ^ i
    loc₂ = lem₃ i loc₁

    loc₃ : bits x < bits y
    loc₃ = lem₆ loc₂

  <ʷ-✓₂ : ∀ {i} {x} {y} → (x <ʷ y) ≡ false → bits {i} x ≮ bits y
  <ʷ-✓₂ {i} {x} {y} p    with (false ∷ x) ⊞ ↕′ y in eq
  <ʷ-✓₂ {i} {x} {y} ()      | (false ∷ _)
  <ʷ-✓₂ {i} {x} {y} refl    | (true ∷ r)  = ≤⇒≯ loc₃
    where
    loc₁ : bits x + (2 ^ i ∸ bits y) ≡ bits (true ∷ r)
    loc₁ = trans (sym (lem₂ x y ⦃ 2^i≢0 {suc i} ⦄)) (cong bits eq)

    loc₂ : 2 ^ i ≤ bits x + (2 ^ i ∸ bits y)
    loc₂ = lem₄ i loc₁

    loc₃ : bits y ≤ bits x
    loc₃ = lem₅ (bits<2^i y) loc₂

--- less than or equal to --------------------------------------------------------------------------

infix 4 _≤ʷ_

_≤ʷ_ : {i : ℕ} → Word i → Word i → Bool
x ≤ʷ y = not (y <ʷ x)

≤ʷ-✓₁ : ∀ {i} {x} {y} → (x ≤ʷ y) ≡ true → bits {i} x ≤ bits y
≤ʷ-✓₁ {i} {x} {y} p = ≮⇒≥ (<ʷ-✓₂ {i} (not-injective p))

≤ʷ-✓₂ : ∀ {i} {x} {y} → (x ≤ʷ y) ≡ false → bits {i} x ≰ bits y
≤ʷ-✓₂ {i} {x} {y} p = <⇒≱ (<ʷ-✓₁ {i} (not-injective p))

--- greater than -----------------------------------------------------------------------------------

infix 4 _>ʷ_

_>ʷ_ : {i : ℕ} → Word i → Word i → Bool
x >ʷ y = y <ʷ x

>ʷ-✓₁ : ∀ {i} {x} {y} → (x >ʷ y) ≡ true → bits {i} x > bits y
>ʷ-✓₁ {i} {x} {y} p = <ʷ-✓₁ {i} p

>ʷ-✓₂ : ∀ {i} {x} {y} → (x >ʷ y) ≡ false → bits {i} x ≯ bits y
>ʷ-✓₂ {i} {x} {y} p = <ʷ-✓₂ {i} p

--- greater than or equal to -----------------------------------------------------------------------

infix 4 _≥ʷ_

_≥ʷ_ : {i : ℕ} → Word i → Word i → Bool
x ≥ʷ y = y ≤ʷ x

≥ʷ-✓₁ : ∀ {i} {x} {y} → (x ≥ʷ y) ≡ true → bits {i} x ≥ bits y
≥ʷ-✓₁ {i} {x} {y} p = ≤ʷ-✓₁ {i} p

≥ʷ-✓₂ : ∀ {i} {x} {y} → (x ≥ʷ y) ≡ false → bits {i} x ≱ bits y
≥ʷ-✓₂ {i} {x} {y} p = ≤ʷ-✓₂ {i} p

--- ring solver ------------------------------------------------------------------------------------

module Solver (i : ℕ) .⦃ d≢0 : NonZero (2 ^ i) ⦄ where
  open ≡-Reasoning

  d = 2 ^ i

  0%d≡0 : 0 % d ≡ 0
  0%d≡0 with d
  0%d≡0    | zero    = contradiction refl (≢-nonZero⁻¹ 0)
  0%d≡0    | suc d-1 = refl

  elem₀ : Word i
  elem₀ = replicate false

  elem₀≡0 : bits elem₀ ≡ 0
  elem₀≡0 = bits≡0 i

  elem₁ : (i : ℕ) → Word i
  elem₁ zero          = []
  elem₁ (suc zero)    = true ∷ elem₁ zero
  elem₁ (suc (suc i)) = false ∷ elem₁ (suc i)

  elem₁≡1 : ∀ i → .⦃ NonZero i ⦄ → bits (elem₁ i) ≡ 1
  elem₁≡1 (suc zero)    = refl
  elem₁≡1 (suc (suc i)) = elem₁≡1 (suc i)

  ⊞-comm : (xs ys : Word i) → xs ⊞ ys ≡ ys ⊞ xs
  ⊞-comm xs ys = bitsInjective $
    bits (xs ⊞ ys)          ≡⟨ ⊞-✓ xs ys ⟩
    (bits xs + bits ys) % d ≡⟨ kong (+-comm (bits xs) (bits ys)) ⟩
    (bits ys + bits xs) % d ≡˘⟨ ⊞-✓ ys xs ⟩
    bits (ys ⊞ xs)          ∎

  ⊠-comm : (xs ys : Word i) → xs ⊠ ys ≡ ys ⊠ xs
  ⊠-comm xs ys = bitsInjective $
    bits (xs ⊠ ys)          ≡⟨ ⊠-✓ xs ys ⟩
    (bits xs * bits ys) % d ≡⟨ kong (*-comm (bits xs) (bits ys)) ⟩
    (bits ys * bits xs) % d ≡˘⟨ ⊠-✓ ys xs ⟩
    bits (ys ⊠ xs)          ∎

  ⊞-assoc : (xs ys zs : Word i) → (xs ⊞ ys) ⊞ zs ≡ xs ⊞ (ys ⊞ zs)
  ⊞-assoc xs ys zs = bitsInjective $
    bits ((xs ⊞ ys) ⊞ zs)                     ≡⟨ ⊞-✓ (xs ⊞ ys) zs ⟩
    (bits (xs ⊞ ys) + bits zs) % d            ≡⟨ kong (⊞-✓ xs ys ⦃ d≢0 ⦄) ⟩
    ((bits xs + bits ys) % d + bits zs) % d   ≡⟨ %-%-+ˡ (bits xs + bits ys) (bits zs) d ⟩
    (bits xs + bits ys + bits zs) % d         ≡⟨ kong (+-assoc (bits xs) (bits ys) (bits zs)) ⟩
    (bits xs + (bits ys + bits zs)) % d       ≡˘⟨ %-%-+ʳ (bits xs) (bits ys + bits zs) d ⟩
    (bits xs + (bits ys + bits zs) % d) % d   ≡˘⟨ kong (⊞-✓ ys zs ⦃ d≢0 ⦄) ⟩
    (bits xs + bits (ys ⊞ zs)) % d            ≡˘⟨ ⊞-✓ xs (ys ⊞ zs) ⟩
    bits (xs ⊞ (ys ⊞ zs))                     ∎

  ⊞-identityˡ : (xs : Word i) → elem₀ ⊞ xs ≡ xs
  ⊞-identityˡ xs = bitsInjective $
    bits (elem₀ ⊞ xs)          ≡⟨ ⊞-✓ elem₀ xs ⟩
    (bits elem₀ + bits xs) % d ≡⟨ kong (bits≡0 i) ⟩
    (0 + bits xs) % d          ≡⟨⟩
    bits xs % d                ≡⟨ x<m⇒x%m≡x (bits<2^i xs) ⟩
    bits xs                    ∎

  ⊞-identityʳ : (xs : Word i) → xs ⊞ elem₀ ≡ xs
  ⊞-identityʳ xs = trans (⊞-comm xs elem₀) (⊞-identityˡ xs)

  ⊞-inverseˡ : (xs : Word i) → ↕ xs ⊞ xs ≡ elem₀
  ⊞-inverseˡ xs = bitsInjective $
    bits (↕ xs ⊞ xs)                      ≡⟨ ⊞-✓ (↕ xs) xs ⟩
    (bits (↕ xs) + bits xs) % d           ≡⟨ kong (↕-✓ xs ⦃ d≢0 ⦄) ⟩
    ((2 ^ i ∸ bits xs) % d + bits xs) % d ≡⟨ kong (%-%-+ˡ (2 ^ i ∸ bits xs) (bits xs) d ⦃ d≢0 ⦄) ⟩
    (2 ^ i ∸ bits xs + bits xs) % d       ≡⟨ kong (m∸n+n≡m (<⇒≤ (bits<2^i xs))) ⟩
    2 ^ i % d                             ≡⟨ n%n≡0 d ⟩
    0                                     ≡˘⟨ elem₀≡0 ⟩
    bits elem₀                            ∎

  ⊞-inverseʳ : (xs : Word i) → xs ⊞ ↕ xs ≡ elem₀
  ⊞-inverseʳ xs = trans (⊞-comm xs (↕ xs)) (⊞-inverseˡ xs)

  ⊠-assoc : (xs ys zs : Word i) → (xs ⊠ ys) ⊠ zs ≡ xs ⊠ (ys ⊠ zs)
  ⊠-assoc xs ys zs = bitsInjective $
    bits ((xs ⊠ ys) ⊠ zs)                     ≡⟨ ⊠-✓ (xs ⊠ ys) zs ⟩
    (bits (xs ⊠ ys) * bits zs) % d            ≡⟨ kong (⊠-✓ xs ys ⦃ d≢0 ⦄) ⟩
    ((bits xs * bits ys) % d * bits zs) % d   ≡⟨ %-%-*ˡ (bits xs * bits ys) (bits zs) d ⟩
    (bits xs * bits ys * bits zs) % d         ≡⟨ kong (*-assoc (bits xs) (bits ys) (bits zs)) ⟩
    (bits xs * (bits ys * bits zs)) % d       ≡˘⟨ %-%-*ʳ (bits xs) (bits ys * bits zs) d ⟩
    (bits xs * (bits ys * bits zs % d)) % d   ≡˘⟨ kong (⊠-✓ ys zs ⦃ d≢0 ⦄) ⟩
    (bits xs * bits (ys ⊠ zs)) % d            ≡˘⟨ ⊠-✓ xs (ys ⊠ zs) ⟩
    bits (xs ⊠ (ys ⊠ zs))                     ∎

  ⊠-identityˡ : (xs : Word i) → elem₁ i ⊠ xs ≡ xs
  ⊠-identityˡ []       = refl
  ⊠-identityˡ (x ∷ xs) = bitsInjective $
    bits (elem₁ i ⊠ (x ∷ xs))          ≡⟨ ⊠-✓ (elem₁ i) (x ∷ xs) ⟩
    bits (elem₁ i) * bits (x ∷ xs) % d ≡⟨ kong (elem₁≡1 i ⦃ _ ⦄) ⟩
    1 * bits (x ∷ xs) % d              ≡⟨ kong (*-identityˡ (bits (x ∷ xs)))  ⟩
    bits (x ∷ xs) % d                  ≡⟨ x<m⇒x%m≡x (bits<2^i (x ∷ xs)) ⟩
    bits (x ∷ xs)                      ∎

  ⊠-identityʳ : (xs : Word i) → xs ⊠ (elem₁ i) ≡ xs
  ⊠-identityʳ xs = trans (⊠-comm xs (elem₁ i)) (⊠-identityˡ xs)

  ⊠-zeroˡ : (xs : Word i) → elem₀ ⊠ xs ≡ elem₀
  ⊠-zeroˡ xs = bitsInjective $
    bits (elem₀ ⊠ xs)          ≡⟨ ⊠-✓ elem₀ xs ⟩
    (bits elem₀ * bits xs) % d ≡⟨ kong elem₀≡0 ⟩
    0 % d                      ≡⟨ 0%d≡0 ⟩
    0                          ≡˘⟨ elem₀≡0 ⟩
    bits elem₀                 ∎

  ⊠-zeroʳ : (xs : Word i) → xs ⊠ elem₀ ≡ elem₀
  ⊠-zeroʳ xs = trans (⊠-comm xs elem₀) (⊠-zeroˡ xs)

  ⊠-distribˡ-⊞ : (xs ys zs : Word i) → xs ⊠ (ys ⊞ zs) ≡ xs ⊠ ys ⊞ xs ⊠ zs
  ⊠-distribˡ-⊞ xs ys zs = bitsInjective $
    bits (xs ⊠ (ys ⊞ zs))                           ≡⟨ ⊠-✓ xs (ys ⊞ zs) ⟩
    (bits xs * bits (ys ⊞ zs)) % d                  ≡⟨ kong (⊞-✓ ys zs ⦃ d≢0 ⦄) ⟩
    (bits xs * ((bits ys + bits zs) % d)) % d       ≡⟨ %-%-*ʳ (bits xs) (bits ys + bits zs) d ⟩
    (bits xs * (bits ys + bits zs)) % d             ≡⟨ kong (*-distribˡ-+ (bits xs) (bits ys) (bits zs)) ⟩
    (bits xs * bits ys + bits xs * bits zs) % d     ≡˘⟨ %-%-+ˡ (bits xs * bits ys) (bits xs * bits zs) d ⟩
    (bits xs * bits ys % d + bits xs * bits zs) % d ≡˘⟨ kong (⊠-✓ xs ys ⦃ d≢0 ⦄) ⟩
    (bits (xs ⊠ ys) + bits xs * bits zs) % d        ≡˘⟨ %-%-+ʳ (bits (xs ⊠ ys)) (bits xs * bits zs) d ⟩
    (bits (xs ⊠ ys) + bits xs * bits zs % d) % d    ≡˘⟨ kong (⊠-✓ xs zs ⦃ d≢0 ⦄) ⟩
    (bits (xs ⊠ ys) + bits (xs ⊠ zs)) % d           ≡˘⟨ ⊞-✓ (xs ⊠ ys) (xs ⊠ zs) ⦃ d≢0 ⦄ ⟩
    bits (xs ⊠ ys ⊞ xs ⊠ zs) ∎

  ⊠-distribʳ-⊞ : (xs ys zs : Word i) → (ys ⊞ zs) ⊠ xs ≡ ys ⊠ xs ⊞ zs ⊠ xs
  ⊠-distribʳ-⊞ xs ys zs =
    (ys ⊞ zs) ⊠ xs    ≡⟨ ⊠-comm (ys ⊞ zs) xs ⟩
    xs ⊠ (ys ⊞ zs)    ≡⟨ ⊠-distribˡ-⊞ xs ys zs ⟩
    xs ⊠ ys ⊞ xs ⊠ zs ≡⟨ kong (⊠-comm xs ys) ⟩
    ys ⊠ xs ⊞ xs ⊠ zs ≡⟨ kong (⊠-comm xs zs) ⟩
    ys ⊠ xs ⊞ zs ⊠ xs ∎

  isSemigroup : IsSemigroup _≡_ _⊞_
  isSemigroup = record {
      isMagma = isMagma _⊞_ ;
      assoc   = ⊞-assoc
    }

  isMonoid : IsMonoid _≡_ _⊞_ elem₀
  isMonoid = record {
      isSemigroup = isSemigroup ;
      identity    = ⊞-identityˡ , ⊞-identityʳ
    }

  isGroup : IsGroup _≡_ _⊞_ elem₀ ↕_
  isGroup = record {
      isMonoid = isMonoid ;
      inverse  = ⊞-inverseˡ , ⊞-inverseʳ ;
      ⁻¹-cong  = λ { refl → refl }
    }

  isAbelianGroup : IsAbelianGroup _≡_ _⊞_ elem₀ ↕_
  isAbelianGroup = record {
      isGroup = isGroup ;
      comm    = ⊞-comm
    }

  isRing : IsRing _≡_ _⊞_ _⊠_ ↕_ elem₀ (elem₁ i)
  isRing = record {
      +-isAbelianGroup = isAbelianGroup ;
      *-cong           = λ { refl refl → refl } ;
      *-assoc          = ⊠-assoc ;
      *-identity       = ⊠-identityˡ , ⊠-identityʳ ;
      distrib          = ⊠-distribˡ-⊞ , ⊠-distribʳ-⊞ ;
      zero             = ⊠-zeroˡ , ⊠-zeroʳ
    }

  isCommutativeRing : IsCommutativeRing _≡_ _⊞_ _⊠_ ↕_ elem₀ (elem₁ i)
  isCommutativeRing = record {
      isRing = isRing ;
      *-comm = ⊠-comm
    }

  commutativeRing : CommutativeRing 0ℓ 0ℓ
  commutativeRing = record {
      Carrier           = Word i ;
      _≈_               = _≡_ ;
      _+_               = _⊞_ ;
      _*_               = _⊠_ ;
      -_                = ↕_ ;
      0#                = elem₀ ;
      1#                = elem₁ i ;
      isCommutativeRing = isCommutativeRing
    }

  import Tactic.RingSolver.NonReflective as NR
  import Tactic.RingSolver.Core.AlmostCommutativeRing as ACR

  almostCommutativeRing : ACR.AlmostCommutativeRing 0ℓ 0ℓ
  almostCommutativeRing = ACR.fromCommutativeRing commutativeRing isZero
    where
    isZero : (x : Word i) → Maybe (elem₀ ≡ x)
    isZero x =
      case elem₀ ≟ʷ x of λ where
        (yes x≡0) → just x≡0
        (no  x≢0) → nothing

  open NR almostCommutativeRing public

--- SAT solver -------------------------------------------------------------------------------------

data Formulaᵇ (i : ℕ) : Set
data Formulaʷ (i : ℕ) : Set

data Formulaᵇ i where
  eqᵇ : Formulaʷ i → Formulaʷ i → Formulaᵇ i
  neᵇ : Formulaʷ i → Formulaʷ i → Formulaᵇ i
  ltᵇ : Formulaʷ i → Formulaʷ i → Formulaᵇ i
  leᵇ : Formulaʷ i → Formulaʷ i → Formulaᵇ i
  gtᵇ : Formulaʷ i → Formulaʷ i → Formulaᵇ i
  geᵇ : Formulaʷ i → Formulaʷ i → Formulaᵇ i

data Formulaʷ i where
  conʷ : Word i → Formulaʷ i
  varʷ : ℕ → Formulaʷ i
  notʷ : Formulaʷ i → Formulaʷ i
  andʷ : Formulaʷ i → Formulaʷ i → Formulaʷ i
  orʷ  : Formulaʷ i → Formulaʷ i → Formulaʷ i
  xorʷ : Formulaʷ i → Formulaʷ i → Formulaʷ i
  negʷ : Formulaʷ i → Formulaʷ i
  addʷ : Formulaʷ i → Formulaʷ i → Formulaʷ i
  subʷ : Formulaʷ i → Formulaʷ i → Formulaʷ i
  mulʷ : Formulaʷ i → Formulaʷ i → Formulaʷ i
  iteʷ : Formulaᵇ i → Formulaʷ i → Formulaʷ i → Formulaʷ i
