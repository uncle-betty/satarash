module Satarash.Word where

open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (
    IsMagma ; IsSemigroup ; IsMonoid ; IsGroup ; IsAbelianGroup ; IsRing ; IsCommutativeRing
  )
open import Data.Bool using (
    Bool ; true ; false ; _∧_ ; _∨_ ; not ; _xor_ ; if_then_else_
  ) renaming (
    _≟_ to _≟ᵇ_
  )
open import Data.Bool.Properties using (∧-zeroʳ ; ∧-identityʳ ; ∨-identityʳ ; not-injective)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Nat using (
    ℕ ; zero ; suc ; pred ; _+_ ; _*_ ; _∸_ ; _^_ ; _≤_ ; _≰_ ; z≤n ; s≤s ; z<s ; _<_ ; _≮_ ; _>_ ;
    _≯_ ; _≥_ ; _≱_ ; NonZero ; ≢-nonZero⁻¹
  ) renaming (
    _≟_ to _≟ⁿ_
  )
open import Data.Nat.DivMod using (
    _/_ ; _%_ ; m≡m%n+[m/n]*n ; n%n≡0 ; m*n%n≡0 ; m*n/n≡m ; m%n<n ; m%n%n≡m%n ; m<n⇒m/n≡0 ;
    m≤n⇒m%n≡m ; [m+kn]%n≡m%n ; +-distrib-/
  )
open import Data.Nat.Properties using (
    ≤-refl ; <-irrefl ; <⇒≢ ; <⇒≤ ; <⇒≱ ; ≤⇒≯ ; ≮⇒≥ ;
    +-identityʳ ; +-comm ; +-assoc ; +-suc ; +-monoˡ-≤ ; +-monoʳ-≤ ; +-monoˡ-< ; +-monoʳ-< ;
    n<1+n ; m+n∸n≡m ; m∸n+n≡m ; m∸n≤m ; m+[n∸m]≡n ;
    *-suc ; *-zeroʳ ; *-identityˡ ; *-identityʳ ; *-comm ; *-assoc ; *-monoˡ-≤ ; *-monoʳ-≤ ;
    *-monoˡ-< ; *-distribˡ-+ ; *-distribʳ-+ ; ^-distribˡ-+-* ;
    module ≤-Reasoning
  )
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; uncurry) renaming (map to mapᵖ)
open import Data.Vec using (
    Vec ; [] ; _∷_ ; [_] ; replicate ; _++_ ; splitAt ; take ; drop ; head ; map ; zip ; foldr
  )
open import Data.Vec.Properties using (
    ≡-dec ; ∷-injectiveʳ ; ∷-injective ; map-id ; map-++ ; map-∘ ; map-zip ; map-cong ;
    drop-distr-map
  )
open import Function using (_$_ ; case_of_ ; _∘_ ; _∘₂_ ; id ; const)
open import Function.Reasoning
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (
    _≡_ ; _≢_ ; refl ; sym ; ≢-sym ; cong ; cong₂ ; trans ; subst ; _≗_ ; module ≡-Reasoning
  )
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Algebra using (isMagma)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import Tactic.Cong using (cong!)

open import Kong.Tactic using (kong)

open import Satarash.Tseytin as T using (Formula₀ ; con₀ ; var₀ ; and₀ ; or₀ ; not₀ ; xor₀ ; eval₀)

--- words ------------------------------------------------------------------------------------------

Word : ℕ → Set
Word = Vec Bool

infix 4 _≟ʷ_

_≟ʷ_ : {i : ℕ} → DecidableEquality (Word i)
_≟ʷ_ {i} = ≡-dec _≟ᵇ_

substʷ : {i k : ℕ} → i ≡ k → Word i → Word k
substʷ = subst Word

Boolⁿ : (n : ℕ) → (S : Word n → Set) → Word 0 → Set
Boolⁿ zero    S = S
Boolⁿ (suc n) S = Boolⁿ n (λ w → (b : Bool) → S (b ∷ w))

curryʷ : {n : ℕ} → {S : Word n → Set} → (∀ w → S w) → Boolⁿ n S []
curryʷ {zero}  p = p []
curryʷ {suc n} p = curryʷ (λ w b → p (b ∷ w))

uncurryʷ : {n : ℕ} → {S : Word n → Set} → Boolⁿ n S [] → ∀ w → S w
uncurryʷ {zero}  p []      = p
uncurryʷ {suc n} p (b ∷ w) = uncurryʷ p w b

--- useful helpers ---------------------------------------------------------------------------------

lookup′ : {i : ℕ} → Word i → ℕ → Bool
lookup′ []       n       = false
lookup′ (b ∷ bs) zero    = b
lookup′ (b ∷ bs) (suc n) = lookup′ bs n

mn≢0 : ∀ m n → .⦃ NonZero m ⦄ → .⦃ NonZero n ⦄ → NonZero (m * n)
mn≢0 (suc m) (suc n) = _

2^i≢0 : ∀ i → NonZero (2 ^ i)
2^i≢0 zero    = _
2^i≢0 (suc i) = mn≢0 2 (2 ^ i) ⦃ _ ⦄ ⦃ 2^i≢0 i ⦄

%-congʳ : ∀ x {y z} .⦃ _ : NonZero y ⦄ .⦃ _ : NonZero z ⦄ → y ≡ z → x % y ≡ x % z
%-congʳ x {y} {z} refl = refl

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

%-* : ∀ x m n .⦃ _ : NonZero m ⦄ .⦃ _ : NonZero n ⦄ .⦃ _ : NonZero (m * n) ⦄ →
  x % m * n ≡ x * n % (m * n)
%-* x m n ⦃ m≢0 ⦄ ⦃ m*n≢0 ⦄ =
  begin
    x % m * n                               ≡˘⟨ x<m⇒x%m≡x <-lem ⟩
    x % m * n                     % (m * n) ≡˘⟨ [m+kn]%n≡m%n (x % m * n) (x / m) (m * n) ⟩
    (x % m * n + x / m * (m * n)) % (m * n) ≡˘⟨ kong (*-assoc (x / m) m n) ⟩
    (x % m * n + x / m * m * n)   % (m * n) ≡˘⟨ kong (*-distribʳ-+ n (x % m) (x / m * m)) ⟩
    (x % m + x / m * m) * n       % (m * n) ≡˘⟨ kong (m≡m%n+[m/n]*n x m ⦃ m≢0 ⦄) ⟩
    x * n                         % (m * n) ∎
  where
  open ≡-Reasoning

  <-lem : x % m * n < m * n
  <-lem = *-monoˡ-< n (m%n<n x m)

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

bitsSubstʷ : ∀ {i k} (p : i ≡ k) xs → bits (substʷ p xs) ≡ bits xs
bitsSubstʷ {i} {k} refl xs = refl

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

+ᵇ+-core : (x y c : Bool) → Word 2
+ᵇ+-core x y c = (x ∧ y ∨ x ∧ c ∨ y ∧ c) ∷ (x xor y xor c) ∷ []

+ᵇ+-core′ : (x y c : Formula₀) → Vec Formula₀ 2
+ᵇ+-core′ x y c = or₀ (and₀ x y) (or₀ (and₀ x c) (and₀ y c)) ∷ xor₀ x (xor₀ y c) ∷ []

_+ᵇ_+_ : (x y c : Bool) → Word 2
_+ᵇ_+_ x y c = +ᵇ+-core x y c

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
~ xs = map not xs

infixl 6 _∧ʷ_

_∧ʷ_ : {i : ℕ} → (xs ys : Word i) → Word i
xs ∧ʷ ys = map (uncurry _∧_) (zip xs ys)

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
xs ∨ʷ ys = map (uncurry _∨_) (zip xs ys)

infixl 5 _xorʷ_

_xorʷ_ : {i : ℕ} → (xs ys : Word i) → Word i
xs xorʷ ys = map (uncurry _xor_) (zip xs ys)

--- truncation -------------------------------------------------------------------------------------

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

modDiv : ∀ {i k} xs ys → bits (xs ++ ys) ≡ bits {k} ys + bits {i} xs * 2 ^ k
modDiv {i} {k} xs ys =
  begin
    bits (xs ++ ys)                               ≡⟨ m≡m%n+[m/n]*n (bits (xs ++ ys)) d ⟩
    bits (xs ++ ys) % d + bits (xs ++ ys) / d * d ≡⟨ kong (bits-% xs ys ⦃ d≢0 ⦄) ⟩
    bits ys + bits (xs ++ ys) / d * d             ≡⟨ kong (bits-/ xs ys ⦃ d≢0 ⦄) ⟩
    bits ys + bits xs * d                         ∎
  where
  d = 2 ^ k

  instance
    d≢0 = 2^i≢0 k

  open ≡-Reasoning

--- padding ----------------------------------------------------------------------------------------

infixl 7 _*ʷ2^_

_*ʷ2^_ : {i : ℕ} → (xs : Word i) → (k : ℕ) → Word (i + k)
_*ʷ2^_ xs k = xs ++ replicate false

*ʷ2^-✓ : ∀ {i} xs k → bits (xs *ʷ2^ k) ≡ bits {i} xs * 2 ^ k
*ʷ2^-✓ {i} xs k =
  begin
    bits (xs *ʷ2^ k)                              ≡⟨ modDiv xs (replicate false) ⟩
    bits (replicate {n = k} false) + bits xs * d  ≡⟨ kong (bits≡0 k) ⟩
    bits xs * d                                   ∎
  where
  open ≡-Reasoning

  d = 2 ^ k

_0⋯_ : (i : ℕ) → {k : ℕ} → (xs : Word k) → Word (i + k)
_0⋯_ i {k} xs = replicate false ++ xs

0⋯-✓ : ∀ i {k} xs → bits (i 0⋯ xs) ≡ bits {k} xs
0⋯-✓ i {k} xs =
  begin
    bits (i 0⋯ xs)                                   ≡⟨ modDiv (replicate {n = i} false) xs ⟩
    bits xs + bits (replicate {n = i} false) * 2 ^ k ≡⟨ kong (bits≡0 i) ⟩
    bits xs + 0                                      ≡⟨ +-identityʳ (bits xs) ⟩
    bits xs                                          ∎
  where
  open ≡-Reasoning

--- shift operations -------------------------------------------------------------------------------

module _ {i n : ℕ} (xs : Word i) (n≤i : n ≤ i) where
  open ≡-Reasoning

  i≡[i∸n]+n : i ≡ (i ∸ n) + n
  i≡[i∸n]+n =
    begin
      i           ≡˘⟨ m+[n∸m]≡n n≤i ⟩
      n + (i ∸ n) ≡⟨ +-comm n (i ∸ n) ⟩
      (i ∸ n) + n ∎

  [i∸n]+n≡i : (i ∸ n) + n ≡ i
  [i∸n]+n≡i = sym i≡[i∸n]+n

  n+[i∸n]≡i : n + (i ∸ n) ≡ i
  n+[i∸n]≡i =
    begin
      n + (i ∸ n) ≡⟨ +-comm n (i ∸ n) ⟩
      (i ∸ n) + n ≡⟨ m∸n+n≡m n≤i ⟩
      i           ∎

  i≡n+[i∸n] : i ≡ n + (i ∸ n)
  i≡n+[i∸n] = sym n+[i∸n]≡i

  instance
    _ = 2^i≢0 i
    _ = 2^i≢0 n
    _ = 2^i≢0 (i ∸ n)
    _ = 2^i≢0 (i ∸ n + n)
    _ = mn≢0 (2 ^ (i ∸ n)) (2 ^ n)

  infix 7 _⟫_

  _⟫_ : Word i
  _⟫_ = substʷ n+[i∸n]≡i (n 0⋯ (substʷ i≡[i∸n]+n xs /ʷ2^ n))

  ⟫-✓ : bits _⟫_ ≡ bits xs / 2 ^ n
  ⟫-✓ =
    begin
      bits _⟫_                            ≡⟨⟩
      bits (sub₁ (n 0⋯ (sub₂ xs /ʷ2^ n))) ≡⟨ bitsSubstʷ n+[i∸n]≡i (n 0⋯ (sub₂ xs /ʷ2^ n)) ⟩
      bits (n 0⋯ (sub₂ xs /ʷ2^ n))        ≡⟨ 0⋯-✓ n (sub₂ xs /ʷ2^ n) ⟩
      bits (sub₂ xs /ʷ2^ n)               ≡⟨ /ʷ2^-✓ n (sub₂ xs) ⟩
      bits (sub₂ xs) / 2 ^ n              ≡⟨ cong (_/ 2 ^ n) (bitsSubstʷ i≡[i∸n]+n xs) ⟩
      bits xs / 2 ^ n                     ∎
    where
    sub₁ = substʷ n+[i∸n]≡i
    sub₂ = substʷ i≡[i∸n]+n

  infix 7 _⟪_

  _⟪_ : Word i
  _⟪_ = substʷ [i∸n]+n≡i (substʷ i≡n+[i∸n] xs %ʷ2^ (i ∸ n) *ʷ2^ n)

  ⟪-✓ : bits _⟪_ ≡ bits xs * 2 ^ n % 2 ^ i
  ⟪-✓ =
    begin
      bits _⟪_                                  ≡⟨⟩
      bits (sub₁ (sub₂ xs %ʷ2^ (i ∸ n) *ʷ2^ n)) ≡⟨ bitsSubstʷ [i∸n]+n≡i (sub₂ xs %ʷ2^ (i ∸ n) *ʷ2^ n) ⟩
      bits (sub₂ xs %ʷ2^ (i ∸ n) *ʷ2^ n)        ≡⟨ *ʷ2^-✓ (sub₂ xs %ʷ2^ (i ∸ n)) n ⟩
      bits (sub₂ xs %ʷ2^ (i ∸ n)) * 2 ^ n       ≡⟨ cong (_* 2 ^ n) (%ʷ2^-✓ (i ∸ n) (sub₂ xs)) ⟩
      bits (sub₂ xs) % 2 ^ (i ∸ n) * 2 ^ n      ≡⟨ cong (λ # → # % 2 ^ (i ∸ n) * 2 ^ n) (bitsSubstʷ i≡n+[i∸n] xs) ⟩
      bits xs % 2 ^ (i ∸ n) * 2 ^ n             ≡⟨ %-* (bits xs) (2 ^ (i ∸ n)) (2 ^ n) ⟩
      bits xs * 2 ^ n % (2 ^ (i ∸ n) * 2 ^ n)   ≡⟨ %-congʳ (bits xs * 2 ^ n) expLem ⟩
      bits xs * 2 ^ n % 2 ^ i                   ∎
    where
    sub₁ = substʷ [i∸n]+n≡i
    sub₂ = substʷ i≡n+[i∸n]

    expLem : 2 ^ (i ∸ n) * 2 ^ n ≡ 2 ^ i
    expLem =
      begin
        2 ^ (i ∸ n) * 2 ^ n ≡˘⟨ ^-distribˡ-+-* 2 (i ∸ n) n ⟩
        2 ^ (i ∸ n + n)     ≡⟨ kong (m∸n+n≡m n≤i) ⟩
        2 ^ i               ∎

--- addition ---------------------------------------------------------------------------------------

+ʷ+-core : {i : ℕ} → Bool × Bool → Word (suc i) → Word (suc (suc i))
+ʷ+-core {i} (x , y) (z ∷ zs) = x +ᵇ y + z ++ zs

+ʷ+-core′ : {i : ℕ} → Formula₀ × Formula₀ → Vec Formula₀ (suc i) → Vec Formula₀ (suc (suc i))
+ʷ+-core′ {i} (x , y) (z ∷ zs) = +ᵇ+-core′ x y z ++ zs

_+ʷ_+_ : {i : ℕ} → (xs ys : Word i) → (c : Bool) → Word (suc i)
xs +ʷ ys + c = foldr (Word ∘ suc) +ʷ+-core [ c ] (zip xs ys)

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

↕′-core : {i : ℕ} → Bool → Word (suc i) → Word (suc (suc i))
↕′-core {i} x (z ∷ zs) = false +ᵇ not x + z ++ zs

↕′-core′ : {i : ℕ} → Formula₀ → Vec Formula₀ (suc i) → Vec Formula₀ (suc (suc i))
↕′-core′ {i} x (z ∷ zs) = +ᵇ+-core′ (con₀ false) (not₀ x) z ++ zs

↕′ : {i : ℕ} → (xs : Word i) → Word (suc i)
↕′ xs = foldr (Word ∘ suc) ↕′-core [ true ] xs

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

↕ : {i : ℕ} → (xs : Word i) → Word i
↕ {i} xs = ↕′ xs %ʷ2^ i

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
⊟-✓ {i} xs ys =
  begin
    bits (xs ⊟ ys)                    ≡⟨ %ʷ2^-✓ i (xs ⊞ (↕ ys)) ⟩
    bits (xs ⊞ (↕ ys)) % d            ≡⟨ kong (⊞-✓ xs (↕ ys) ⦃ 2^i≢0 i ⦄) ⟩
    (bits xs + bits (↕ ys)) % d % d   ≡⟨ m%n%n≡m%n (bits xs + bits (↕ ys)) d ⟩
    (bits xs + bits (↕ ys)) % d       ≡⟨ kong (↕-✓ ys ⦃ 2^i≢0 i ⦄) ⟩
    (bits xs + (d ∸ bits ys) % d) % d ≡⟨ %-%-+ʳ (bits xs) (d ∸ bits ys) d ⟩
    (bits xs + (d ∸ bits ys)) % d     ∎
  where
  open ≡-Reasoning

  d = 2 ^ i

--- multiplication ---------------------------------------------------------------------------------

++-swap : (i k : ℕ) → (xs : Word (i + k)) → Word (k + i)
++-swap i k = subst Word (+-comm i k)

++-swap′ : (i k : ℕ) → (xs : Vec Formula₀ (i + k)) → Vec Formula₀ (k + i)
++-swap′ i k = subst (Vec Formula₀) (+-comm i k)

++-swap-✓ : ∀ i k xs → bits (++-swap i k xs) ≡ bits xs
++-swap-✓ i k xs = bitsSubstʷ (+-comm i k) xs

*ʷ-core : {i k : ℕ} → (xs : Word i) → (y : Bool) → (zs : Word (k + i)) → Word (suc (k + i))
*ʷ-core {i} {k} xs y zs = zs +ʷ (xs′ ∧ʷ replicate y) + false
  where xs′ = ++-swap i k (xs *ʷ2^ k)

*ʷ-core′ : {i k : ℕ} → (xs : Vec Formula₀ i) → (y : Formula₀) → (zs : Vec Formula₀ (k + i)) →
  Vec Formula₀ (suc (k + i))
*ʷ-core′ {i} {k} xs y zs = foldr (Vec Formula₀ ∘ suc) +ʷ+-core′ [ con₀ false ] (zip zs xs″)
  where
  xs′ = ++-swap′ i k (xs ++ replicate (con₀ false))
  xs″ = map (uncurry and₀) (zip xs′ (replicate y))

infixl 7 _*ʷ_

_*ʷ_ : {i k : ℕ} → (xs : Word i) → (ys : Word k) → Word (k + i)
_*ʷ_ {i} {k} xs ys = foldr (Word ∘ (_+ i)) (*ʷ-core xs) (replicate false) ys

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

≡ʷ-core : (Bool × Bool) → Bool → Bool
≡ʷ-core (x , y) a = not (x xor y) ∧ a

≡ʷ-core′ : (Formula₀ × Formula₀) → Formula₀ → Formula₀
≡ʷ-core′ (x , y) a = and₀ (not₀ (xor₀ x y)) a

_≡ʷ_ : {i : ℕ} → Word i → Word i → Bool
xs ≡ʷ ys = foldr _ ≡ʷ-core true (zip xs ys)

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
x <ʷ y = not (head ((false ∷ x) ⊞ ↕′ y))

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

    lem₂ : ∀ {i} x y → bits {suc i} ((false ∷ x) ⊞ ↕′ y) ≡ bits x + (2 ^ i ∸ bits y)
    lem₂ {i} x y =
      begin
        bits ((false ∷ x) ⊞ ↕′ y)                    ≡⟨ ⊞-✓ (false ∷ x) (↕′ y) ⟩
        (bits (false ∷ x) + bits (↕′ y)) % 2 ^ suc i ≡⟨⟩
        (bits x + bits (↕′ y)) % 2 ^ suc i           ≡⟨ kong (↕′-✓ y) ⟩
        (bits x + (2 ^ i ∸ bits y)) % 2 ^ suc i      ≡⟨ x<m⇒x%m≡x (lem₁ x y) ⟩
        bits x + (2 ^ i ∸ bits y)                    ∎
      where
      open ≡-Reasoning

      instance
        _ = 2^i≢0 (suc i)

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
    loc₁ = trans (sym (lem₂ x y)) (cong bits eq)

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
    loc₁ = trans (sym (lem₂ x y)) (cong bits eq)

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

  isGroup : IsGroup _≡_ _⊞_ elem₀ ↕
  isGroup = record {
      isMonoid = isMonoid ;
      inverse  = ⊞-inverseˡ , ⊞-inverseʳ ;
      ⁻¹-cong  = λ { refl → refl }
    }

  isAbelianGroup : IsAbelianGroup _≡_ _⊞_ elem₀ ↕
  isAbelianGroup = record {
      isGroup = isGroup ;
      comm    = ⊞-comm
    }

  isRing : IsRing _≡_ _⊞_ _⊠_ ↕ elem₀ (elem₁ i)
  isRing = record {
      +-isAbelianGroup = isAbelianGroup ;
      *-cong           = λ { refl refl → refl } ;
      *-assoc          = ⊠-assoc ;
      *-identity       = ⊠-identityˡ , ⊠-identityʳ ;
      distrib          = ⊠-distribˡ-⊞ , ⊠-distribʳ-⊞ ;
      zero             = ⊠-zeroˡ , ⊠-zeroʳ
    }

  isCommutativeRing : IsCommutativeRing _≡_ _⊞_ _⊠_ ↕ elem₀ (elem₁ i)
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
      -_                = ↕ ;
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
  eorʷ : Formulaʷ i → Formulaʷ i → Formulaʷ i
  negʷ : Formulaʷ i → Formulaʷ i
  addʷ : Formulaʷ i → Formulaʷ i → Formulaʷ i
  subʷ : Formulaʷ i → Formulaʷ i → Formulaʷ i
  mulʷ : Formulaʷ i → Formulaʷ i → Formulaʷ i
  iteʷ : Formulaᵇ i → Formulaʷ i → Formulaʷ i → Formulaʷ i

W∘ : (ℕ → ℕ) → ℕ → Set
W∘ f = Word ∘ f

F∘ : (ℕ → ℕ) → ℕ → Set
F∘ f = Vec Formula₀ ∘ f

evalᵇ : {i : ℕ} → (ℕ → Word i) → Formulaᵇ i → Bool
evalʷ : {i : ℕ} → (ℕ → Word i) → Formulaʷ i → Word i

evalᵇ v (eqᵇ x y) = evalʷ v x ≡ʷ evalʷ v y
evalᵇ v (neᵇ x y) = evalʷ v x ≢ʷ evalʷ v y
evalᵇ v (ltᵇ x y) = evalʷ v x <ʷ evalʷ v y
evalᵇ v (leᵇ x y) = evalʷ v x ≤ʷ evalʷ v y
evalᵇ v (gtᵇ x y) = evalʷ v x >ʷ evalʷ v y
evalᵇ v (geᵇ x y) = evalʷ v x ≥ʷ evalʷ v y

evalʷ v (conʷ x)     = x
evalʷ v (varʷ x)     = v x
evalʷ v (notʷ x)     = ~ (evalʷ v x)
evalʷ v (andʷ x y)   = evalʷ v x ∧ʷ evalʷ v y
evalʷ v (orʷ x y)    = evalʷ v x ∨ʷ evalʷ v y
evalʷ v (eorʷ x y)   = evalʷ v x xorʷ evalʷ v y
evalʷ v (negʷ x)     = ↕ (evalʷ v x)
evalʷ v (addʷ x y)   = evalʷ v x ⊞ evalʷ v y
evalʷ v (subʷ x y)   = evalʷ v x ⊟ evalʷ v y
evalʷ v (mulʷ x y)   = evalʷ v x ⊠ evalʷ v y
evalʷ v (iteʷ x y z) = if evalᵇ v x then evalʷ v y else evalʷ v z

makeSeq : (k↑ k↓ : ℕ) → Vec ℕ k↓
makeSeq k↑ zero     = []
makeSeq k↑ (suc k↓) = k↑ ∷ makeSeq (suc k↑) k↓

headMap : ∀ {S T : Set} {i} (f : S → T) (xs : Vec S (suc i)) → head (map f xs) ≡ f (head xs)
headMap f (x ∷ xs) = refl

mapEvalRepl : ∀ {i} v x → map (eval₀ v) (replicate {n = i} x) ≡ replicate (eval₀ v x)
mapEvalRepl {zero}  v x = refl
mapEvalRepl {suc i} v x = cong (eval₀ v x ∷_) (mapEvalRepl v x)

mapEvalSubst : ∀ {i k} v (p : i ≡ k) (x : Vec Formula₀ i) →
  map (eval₀ v) (subst (Vec Formula₀) p x) ≡ subst Word p (map (eval₀ v) x)
mapEvalSubst v refl x = refl

transformᵇ : {i : ℕ} → Formulaᵇ i → Formula₀
transformʷ : {i : ℕ} → Formulaʷ i → Vec Formula₀ i

~-build : {i : ℕ} → (x : Vec Formula₀ i) → Vec Formula₀ i
~-build {i} x = map not₀ x

~-eval : ∀ {i} v (x : Vec Formula₀ i) → map (eval₀ v) (~-build x) ≡ ~ (map (eval₀ v) x)
~-eval {zero}  v []       = refl
~-eval {suc i} v (x ∷ xs) = kong (~-eval v xs)

∧-build : {i : ℕ} → (x y : Vec Formula₀ i) → Vec Formula₀ i
∧-build x y = map (uncurry and₀) (zip x y)

∧-eval : ∀ {i} v (x y : Vec Formula₀ i) →
  map (eval₀ v) (∧-build x y) ≡ map (eval₀ v) x ∧ʷ map (eval₀ v) y
∧-eval {zero}  v []       []       = refl
∧-eval {suc i} v (x ∷ xs) (y ∷ ys) = kong (∧-eval v xs ys)

∨-build : {i : ℕ} → (x y : Vec Formula₀ i) → Vec Formula₀ i
∨-build x y = map (uncurry or₀) (zip x y)

∨-eval : ∀ {i} v (x y : Vec Formula₀ i) →
  map (eval₀ v) (∨-build x y) ≡ map (eval₀ v) x ∨ʷ map (eval₀ v) y
∨-eval {zero}  v []       []       = refl
∨-eval {suc i} v (x ∷ xs) (y ∷ ys) = kong (∨-eval v xs ys)

eorBuild : {i : ℕ} → (x y : Vec Formula₀ i) → Vec Formula₀ i
eorBuild x y = map (uncurry xor₀) (zip x y)

eorEval : ∀ {i} v (x y : Vec Formula₀ i) →
  map (eval₀ v) (eorBuild x y) ≡ map (eval₀ v) x xorʷ map (eval₀ v) y
eorEval {zero}  v []       []       = refl
eorEval {suc i} v (x ∷ xs) (y ∷ ys) = kong (eorEval v xs ys)

↕′-build : {i : ℕ} → (x : Vec Formula₀ i) → Vec Formula₀ (suc i)
↕′-build x = foldr (F∘ suc) ↕′-core′ [ con₀ true ] x

↕-build : {i : ℕ} → (x : Vec Formula₀ i) → Vec Formula₀ i
↕-build = drop 1 ∘ ↕′-build

↕′-eval₁ : ∀ {i} v (x : Formula₀) (z : Vec Formula₀ (suc i)) →
  map (eval₀ v) (↕′-core′ x z) ≡ ↕′-core (eval₀ v x) (map (eval₀ v) z)
↕′-eval₁ {i} v x (z ∷ zs) = refl

↕′-eval₂ : ∀ {i} v (x : Vec Formula₀ i) → map (eval₀ v) (↕′-build x) ≡ ↕′ (map (eval₀ v) x)
↕′-eval₂ {zero}  v []       = refl
↕′-eval₂ {suc i} v (x ∷ xs)
  rewrite ↕′-eval₁ v x (↕′-build xs)
  -- XXX - why does kong fail here?
  = cong (↕′-core (eval₀ v x)) (↕′-eval₂ v xs)

↕-eval : ∀ {i} v (x : Vec Formula₀ i) → map (eval₀ v) (↕-build x) ≡ ↕ (map (eval₀ v) x)
↕-eval v x =
  begin
    map (eval₀ v) (↕-build x)           ≡⟨⟩
    map (eval₀ v) (drop 1 (↕′-build x)) ≡˘⟨ drop-distr-map (eval₀ v) 1 (↕′-build x) ⟩
    drop 1 (map (eval₀ v) (↕′-build x)) ≡⟨ kong (↕′-eval₂ v x ) ⟩
    drop 1 (↕′ (map (eval₀ v) x))       ≡⟨⟩
    ↕ (map (eval₀ v) x)                 ∎
  where open ≡-Reasoning

+′-build : {i : ℕ} → (x y : Vec Formula₀ i) → Vec Formula₀ (suc i)
+′-build x y = foldr (F∘ suc) +ʷ+-core′ [ con₀ false ] (zip x y)

+-build : {i : ℕ} → (x y : Vec Formula₀ i) → Vec Formula₀ i
+-build = drop 1 ∘₂ +′-build

+′-eval₁ : ∀ {i} v (x y : Formula₀) (z : Vec Formula₀ (suc i)) →
  map (eval₀ v) (+ʷ+-core′ (x , y) z) ≡ +ʷ+-core (eval₀ v x , eval₀ v y) (map (eval₀ v) z)
+′-eval₁ {i} v x y (z ∷ zs) = refl

+′-eval₂ : ∀ {i} v (x y : Vec Formula₀ i) →
    map (eval₀ v) (+′-build x y) ≡ map (eval₀ v) x +ʷ map (eval₀ v) y + false
+′-eval₂ {zero}  v []       []       = refl
+′-eval₂ {suc i} v (x ∷ xs) (y ∷ ys)
  rewrite +′-eval₁ v x y (+′-build xs ys)
  -- XXX - why does kong fail here?
  = cong (+ʷ+-core (eval₀ v x , eval₀ v y)) (+′-eval₂ v xs ys)

+-eval : ∀ {i} v (x y : Vec Formula₀ i) →
    map (eval₀ v) (+-build x y) ≡ map (eval₀ v) x ⊞ map (eval₀ v) y
+-eval v x y =
  begin
    map (eval₀ v) (+-build x y)                         ≡˘⟨ drop-distr-map (eval₀ v) 1 (+′-build x y) ⟩
    drop 1 (map (eval₀ v) (+′-build x y))               ≡⟨ kong (+′-eval₂ v x y) ⟩
    drop 1 (map (eval₀ v) x +ʷ map (eval₀ v) y + false) ≡⟨⟩
    map (eval₀ v) x ⊞ map (eval₀ v) y                   ∎
  where open ≡-Reasoning

∸-build : {i : ℕ} → (x y : Vec Formula₀ i) → Vec Formula₀ i
∸-build x y = +-build x (↕-build y)

∸-eval : ∀ {i} v (x y : Vec Formula₀ i) →
  map (eval₀ v) (∸-build x y) ≡ map (eval₀ v) x ⊟ map (eval₀ v) y
∸-eval v x y =
  begin
    map (eval₀ v) (∸-build x y)                 ≡⟨⟩
    map (eval₀ v) (+-build x (↕-build y))       ≡⟨ +-eval v x (↕-build y) ⟩
    map (eval₀ v) x ⊞ map (eval₀ v) (↕-build y) ≡⟨ kong (↕-eval v y) ⟩
    map (eval₀ v) x ⊞ ↕ (map (eval₀ v) y)       ≡⟨⟩
    map (eval₀ v) x ⊟ map (eval₀ v) y           ∎
  where open ≡-Reasoning

*′-build : {i k : ℕ} → (x : Vec Formula₀ i) → (y : Vec Formula₀ k) → Vec Formula₀ (k + i)
*′-build {i} {k} x y = foldr (F∘ (_+ i)) (*ʷ-core′ x) (replicate (con₀ false)) y

*-build : {i k : ℕ} → (x : Vec Formula₀ i) → (y : Vec Formula₀ k) → Vec Formula₀ i
*-build {i} {k} = drop k ∘₂ *′-build

*′-eval : ∀ {i k} v (x : Vec Formula₀ i) (y : Vec Formula₀ k) →
    map (eval₀ v) (*′-build x y) ≡ map (eval₀ v) x *ʷ map (eval₀ v) y

*′-eval {i} {zero}  v x []       = mapEvalRepl v (con₀ false)
*′-eval {i} {suc k} v x (y ∷ ys) =
  begin
    map (eval₀ v) (*′-build x (y ∷ ys))                               ≡⟨⟩
    map (eval₀ v) (+′-build (*′-build x ys) ∧₁)                       ≡⟨ +′-eval₂ v (*′-build x ys) ∧₁ ⟩
    -- XXX - why does kong fail here?
    map (eval₀ v) (*′-build x ys) +ʷ map (eval₀ v) ∧₁ + false         ≡⟨ cong (_+ʷ map (eval₀ v) ∧₁ + false) (*′-eval v x ys) ⟩
    -- XXX - why does kong fail here?
    (map (eval₀ v) x *ʷ map (eval₀ v) ys) +ʷ map (eval₀ v) ∧₁ + false ≡⟨ cong ((map (eval₀ v) x *ʷ map (eval₀ v) ys) +ʷ_+ false) ∧-lem ⟩
    (map (eval₀ v) x *ʷ map (eval₀ v) ys) +ʷ ∧₂ + false               ≡⟨⟩
    map (eval₀ v) x *ʷ map (eval₀ v) (y ∷ ys)                         ∎
  where
  open ≡-Reasoning

  l₁ = ++-swap′ i k (x ++ replicate (con₀ false))
  r₁ = replicate y
  ∧₁ = ∧-build l₁ r₁

  l₂ = ++-swap i k (map (eval₀ v) x ++ replicate false)
  r₂ = replicate (eval₀ v y)
  ∧₂ = l₂ ∧ʷ r₂

  ∧ˡ-lem : map (eval₀ v) l₁ ≡ l₂
  ∧ˡ-lem =
    begin
      map (eval₀ v) l₁                                                        ≡⟨⟩
      map (eval₀ v) (++-swap′ i k (x ++ replicate (con₀ false)))              ≡⟨ mapEvalSubst v (+-comm i k) (x ++ replicate (con₀ false)) ⟩
      -- XXX - why does kong fail here?
      ++-swap i k (map (eval₀ v) (x ++ replicate (con₀ false)))               ≡⟨ cong! (map-++ (eval₀ v) x (replicate (con₀ false))) ⟩
      -- XXX - why does kong fail here?
      ++-swap i k (map (eval₀ v) x ++ map (eval₀ v) (replicate (con₀ false))) ≡⟨ cong! (mapEvalRepl v (con₀ false)) ⟩
      ++-swap i k (map (eval₀ v) x ++ replicate false)                        ≡⟨⟩
      l₂                                                                      ∎

  ∧ʳ-lem : map (eval₀ v) r₁ ≡ r₂
  ∧ʳ-lem =
    begin
      map (eval₀ v) r₁            ≡⟨⟩
      map (eval₀ v) (replicate y) ≡⟨ mapEvalRepl v y ⟩
      replicate (eval₀ v y)       ≡⟨⟩
      r₂                          ∎

  ∧-lem : map (eval₀ v) ∧₁ ≡ ∧₂
  ∧-lem =
    begin
      map (eval₀ v) (∧-build l₁ r₁)        ≡⟨ ∧-eval v l₁ r₁ ⟩
      map (eval₀ v) l₁ ∧ʷ map (eval₀ v) r₁ ≡⟨ kong ∧ˡ-lem ⟩
      l₂ ∧ʷ map (eval₀ v) r₁               ≡⟨ kong ∧ʳ-lem ⟩
      l₂ ∧ʷ r₂                             ∎

*-eval : ∀ {i k} v (x : Vec Formula₀ i) (y : Vec Formula₀ k) →
    map (eval₀ v) (*-build x y) ≡ map (eval₀ v) x ⊠ map (eval₀ v) y
*-eval {i} {k} v x y =
  begin
    map (eval₀ v) (*-build x y)                 ≡˘⟨ drop-distr-map (eval₀ v) k (*′-build x y) ⟩
    drop k (map (eval₀ v) (*′-build x y))       ≡⟨ kong (*′-eval v x y) ⟩
    drop k (map (eval₀ v) x *ʷ map (eval₀ v) y) ≡⟨⟩
    map (eval₀ v) x ⊠ map (eval₀ v) y           ∎
  where open ≡-Reasoning

iteBuild : {i : ℕ} → (x : Formula₀) → (y z : Vec Formula₀ i) → Vec Formula₀ i
iteBuild {i} x y z = ∨-build (∧-build (replicate x) y) (∧-build (replicate (not₀ x)) z)

iteEval : ∀ {i} v (x : Formula₀) (y z : Vec Formula₀ i) →
  map (eval₀ v) (iteBuild x y z) ≡ (if eval₀ v x then map (eval₀ v) y else map (eval₀ v) z)
iteEval {i}     v x y        z        with eval₀ v x in p
iteEval {zero}  v x []       []          | true  = refl
iteEval {zero}  v x []       []          | false = refl
iteEval {suc i} v x (y ∷ ys) (z ∷ zs)    | true
  with rec ← iteEval v x ys zs
  rewrite p = cong₂ _∷_ (∨-identityʳ (eval₀ v y)) rec
iteEval {suc i} v x (y ∷ ys) (z ∷ zs) | false
  with rec ← iteEval v x ys zs
  rewrite p = cong (eval₀ v z ∷_) rec

≡-build : {i : ℕ} → (x y : Vec Formula₀ i) → Formula₀
≡-build x y = foldr (const Formula₀) ≡ʷ-core′ (con₀ true) (zip x y)

≡-eval : ∀ {i} v (x y : Vec Formula₀ i) →
  eval₀ v (≡-build x y) ≡ (map (eval₀ v) x ≡ʷ map (eval₀ v) y)
≡-eval {zero}  v []       []       = refl
≡-eval {suc i} v (x ∷ xs) (y ∷ ys) = kong (≡-eval v xs ys)

<-build : {i : ℕ} → (x y : Vec Formula₀ i) → Formula₀
<-build x y =
  let x′ = con₀ false ∷ x in
  let y′ = ↕′-build y in
  not₀ (head (+-build x′ y′))

<-eval : ∀ {i} v (x y : Vec Formula₀ i) →
  eval₀ v (<-build x y) ≡ (map (eval₀ v) x <ʷ map (eval₀ v) y)
<-eval {i} v x y =
  begin
    eval₀ v (<-build x y)                                         ≡⟨⟩
    not (eval₀ v (head (+-build x′ y′)))                          ≡˘⟨ kong (headMap (eval₀ v) (+-build x′ (↕′-build y))) ⟩
    not (head (map (eval₀ v) (+-build x′ y′)))                    ≡⟨ kong (+-eval v x′ (↕′-build y)) ⟩
    not (head (map (eval₀ v) x′ ⊞ map (eval₀ v) y′))              ≡⟨⟩
    not (head ((false ∷ map (eval₀ v) x) ⊞ map (eval₀ v) y′))     ≡⟨ kong (↕′-eval₂ v y) ⟩
    not (head ((false ∷ map (eval₀ v) x) ⊞ ↕′ (map (eval₀ v) y))) ≡⟨⟩
    map (eval₀ v) x <ʷ map (eval₀ v) y                            ∎
  where
  open ≡-Reasoning

  x′ = con₀ false ∷ x
  y′ = ↕′-build y

transformᵇ {i} (eqᵇ x y) = ≡-build (transformʷ x) (transformʷ y)
transformᵇ {i} (neᵇ x y) = not₀ (≡-build (transformʷ x) (transformʷ y))
transformᵇ {i} (ltᵇ x y) = <-build (transformʷ x) (transformʷ y)
transformᵇ {i} (leᵇ x y) = not₀ (<-build (transformʷ y) (transformʷ x))
transformᵇ {i} (gtᵇ x y) = <-build (transformʷ y) (transformʷ x)
transformᵇ {i} (geᵇ x y) = not₀ (<-build (transformʷ x) (transformʷ y))

transformʷ {i} (conʷ x)     = map con₀ x
transformʷ {i} (varʷ x)     = map var₀ (makeSeq (x * i) i)
transformʷ {i} (notʷ x)     = map not₀ (transformʷ x)
transformʷ {i} (andʷ x y)   = ∧-build (transformʷ x) (transformʷ y)
transformʷ {i} (orʷ x y)    = ∨-build (transformʷ x) (transformʷ y)
transformʷ {i} (eorʷ x y)   = eorBuild (transformʷ x) (transformʷ y)
transformʷ {i} (negʷ x)     = ↕-build (transformʷ x)
transformʷ {i} (addʷ x y)   = +-build (transformʷ x) (transformʷ y)
transformʷ {i} (subʷ x y)   = ∸-build (transformʷ x) (transformʷ y)
transformʷ {i} (mulʷ x y)   = *-build (transformʷ x) (transformʷ y)
transformʷ {i} (iteʷ x y z) = iteBuild (transformᵇ x) (transformʷ y) (transformʷ z)

transformᵛ : {i : ℕ} → (ℕ → Word i) → ℕ → Bool
transformᵛ {zero}  v n = false
transformᵛ {suc i} v n = lookup′ (v (n / suc i)) (n % suc i)

transformᵇ-✓ : ∀ {i} v f → eval₀ (transformᵛ {i} v) (transformᵇ f) ≡ evalᵇ v f
transformʷ-✓ : ∀ {i} v f → map (eval₀ (transformᵛ {i} v)) (transformʷ f) ≡ evalʷ v f

transformᵇEq-✓ : ∀ {i} v x y →
  eval₀ (transformᵛ {i} v) (transformᵇ (eqᵇ x y)) ≡ (evalʷ v x ≡ʷ evalʷ v y)
transformᵇEq-✓ {i} v x y =
  begin
    eval₀ tv (transformᵇ (eqᵇ x y))        ≡⟨⟩
    eval₀ tv (≡-build tx ty)               ≡⟨ kong (≡-eval tv tx ty) ⟩
    map (eval₀ tv) tx ≡ʷ map (eval₀ tv) ty ≡⟨ kong (transformʷ-✓ v x) ⟩
    evalʷ v x ≡ʷ map (eval₀ tv) ty         ≡⟨ kong (transformʷ-✓ v y) ⟩
    evalʷ v x ≡ʷ evalʷ v y                 ∎
  where
  open ≡-Reasoning

  tv = transformᵛ v
  tx = transformʷ x
  ty = transformʷ y

transformᵇLt-✓ : ∀ {i} v x y →
  eval₀ (transformᵛ {i} v) (transformᵇ (ltᵇ x y)) ≡ (evalʷ v x <ʷ evalʷ v y)
transformᵇLt-✓ {i} v x y =
  begin
    eval₀ tv (transformᵇ (ltᵇ x y))        ≡⟨⟩
    eval₀ tv (<-build tx ty)               ≡⟨ kong (<-eval tv tx ty) ⟩
    map (eval₀ tv) tx <ʷ map (eval₀ tv) ty ≡⟨ kong (transformʷ-✓ v x) ⟩
    evalʷ v x <ʷ map (eval₀ tv) ty         ≡⟨ kong (transformʷ-✓ v y) ⟩
    evalʷ v x <ʷ evalʷ v y                 ∎
  where
  open ≡-Reasoning

  tv = transformᵛ v
  tx = transformʷ x
  ty = transformʷ y

transformᵇ-✓ {i} v (eqᵇ x y) = transformᵇEq-✓ v x y
transformᵇ-✓ {i} v (neᵇ x y) = cong not (transformᵇEq-✓ v x y)
transformᵇ-✓ {i} v (ltᵇ x y) = transformᵇLt-✓ v x y
transformᵇ-✓ {i} v (leᵇ x y) = cong not (transformᵇLt-✓ v y x)
transformᵇ-✓ {i} v (gtᵇ x y) = transformᵇLt-✓ v y x
transformᵇ-✓ {i} v (geᵇ x y) = cong not (transformᵇLt-✓ v x y)

transformʷ-✓ {i} v (conʷ x) =
  begin
    map (eval₀ (transformᵛ v)) (map con₀ x) ≡˘⟨ map-∘ (eval₀ (transformᵛ v)) con₀ x ⟩
    map id x                                ≡⟨ map-id x ⟩
    x                                       ∎
  where open ≡-Reasoning

transformʷ-✓ {zero}  v (varʷ x) with [] ← v x = refl
transformʷ-✓ {suc i} v (varʷ x) =
  begin
    map ev (transformʷ (varʷ x))                      ≡⟨⟩
    map ev (map var₀ (makeSeq (x * suc i) (suc i)))   ≡˘⟨ map-∘ ev var₀ (makeSeq (x * suc i) (suc i)) ⟩
    map (ev ∘ var₀) (makeSeq (x * suc i) (suc i))     ≡˘⟨ kong (+-identityʳ (x * suc i)) ⟩
    map (ev ∘ var₀) (makeSeq (x * suc i + 0) (suc i)) ≡⟨ evalLookup (suc i) 0 (suc i) v x refl ⟩
    map (lookup′ (v x)) (makeSeq 0 (suc i))           ≡⟨ mapLookup (v x) ⟩
    v x                                               ∎
  where
  ev = eval₀ (transformᵛ v)

  %-simp : ∀ i k x → k < suc i → (x * suc i + k) % suc i ≡ k
  %-simp i k x k<i =
    begin
      (x * suc i + k) % suc i ≡⟨ kong (+-comm (x * suc i) k) ⟩
      (k + x * suc i) % suc i ≡⟨ kong ([m+kn]%n≡m%n k x (suc i) ⦃ _ ⦄) ⟩
      k % suc i               ≡⟨ x<m⇒x%m≡x k<i ⦃ _ ⦄ ⟩
      k                       ∎
    where open ≡-Reasoning

  /-simp : ∀ i k x → k < suc i → (x * suc i + k) / suc i ≡ x
  /-simp i k x k<i =
    begin
      (x * suc i + k) / suc i       ≡⟨ +-distrib-/ (x * suc i) k <-lem ⟩
      x * suc i / suc i + k / suc i ≡⟨ kong (m*n/n≡m x (suc i) ⦃ _ ⦄) ⟩
      x + k / suc i                 ≡⟨ kong (m<n⇒m/n≡0 k<i) ⟩
      x + 0                         ≡⟨ +-identityʳ x ⟩
      x                             ∎
    where
    <-lem : x * suc i % suc i + k % suc i < suc i
    <-lem =
      begin-strict
        x * suc i % suc i + k % suc i ≡⟨ kong (m*n%n≡0 x (suc i) ⦃ _ ⦄) ⟩
        k % suc i                     <⟨ m%n<n k (suc i) ⟩
        suc i                         ∎
      where open ≤-Reasoning

    open ≡-Reasoning

  evalLookup′ : ∀ i k v x → k < i → (eval₀ (transformᵛ {i} v) ∘ var₀) (x * i + k) ≡ lookup′ (v x) k
  evalLookup′ (suc i) k v x k<i =
    begin
      lookup′ (v ((x * suc i + k) / suc i)) ((x * suc i + k) % suc i) ≡⟨ kong (%-simp i k x k<i) ⟩
      lookup′ (v ((x * suc i + k) / suc i)) k                         ≡⟨ kong (/-simp i k x k<i) ⟩
      lookup′ (v x) k                                                 ∎
    where open ≡-Reasoning

  evalLookup : ∀ i k↑ k↓ v x → i ≡ k↑ + k↓ →
    map (eval₀ (transformᵛ {i} v) ∘ var₀) (makeSeq (x * i + k↑) k↓) ≡
    map (lookup′ (v x)) (makeSeq k↑ k↓)
  evalLookup i k↑ zero     v x i≡k↑+k↓ = refl
  evalLookup i k↑ (suc k↓) v x i≡k↑+k↓ = cong₂ _∷_ (evalLookup′ i k↑ v x <-lem) recLem
    where
    <-lem : k↑ < i
    <-lem =
      begin-strict
        k↑          ≡˘⟨ +-identityʳ k↑ ⟩
        k↑ + 0      <⟨ +-monoʳ-< k↑ z<s ⟩
        k↑ + suc k↓ ≡˘⟨ i≡k↑+k↓ ⟩
        i           ∎
      where open ≤-Reasoning

    ≡-lem : i ≡ suc (k↑ + k↓)
    ≡-lem = trans i≡k↑+k↓ (+-suc k↑ k↓)

    recLem : map (eval₀ (transformᵛ v) ∘ var₀) (makeSeq (suc (x * i + k↑)) k↓) ≡
      map (lookup′ (v x)) (makeSeq (suc k↑) k↓)
    recLem =
      begin
        map (eval₀ (transformᵛ v) ∘ var₀) (makeSeq (suc (x * i + k↑)) k↓) ≡˘⟨ kong (+-suc (x * i) k↑) ⟩
        map (eval₀ (transformᵛ v) ∘ var₀) (makeSeq (x * i + suc k↑) k↓)   ≡⟨ evalLookup i (suc k↑) k↓ v x ≡-lem ⟩
        map (lookup′ (v x)) (makeSeq (suc k↑) k↓)                         ∎
      where open ≡-Reasoning

  seqSuc : ∀ k↑ k↓ → makeSeq (suc k↑) k↓ ≡ map suc (makeSeq k↑ k↓)
  seqSuc k↑ zero     = refl
  seqSuc k↑ (suc k↓) = cong (suc k↑ ∷_) (seqSuc (suc k↑) k↓)

  mapLookup : ∀ {i} (w : Word i) → map (lookup′ w) (makeSeq 0 i) ≡ w
  mapLookup {zero}  []       = refl
  mapLookup {suc i} (b ∷ bs) = cong (b ∷_) (trans step (mapLookup bs))
    where
    step : map (lookup′ (b ∷ bs)) (makeSeq 1 i) ≡ map (lookup′ bs) (makeSeq 0 i)
    step =
      begin
        map (lookup′ (b ∷ bs)) (makeSeq 1 i)           ≡⟨ kong (seqSuc 0 i) ⟩
        map (lookup′ (b ∷ bs)) (map suc (makeSeq 0 i)) ≡˘⟨ map-∘ (lookup′ (b ∷ bs)) suc (makeSeq 0 i) ⟩
        map (lookup′ (b ∷ bs) ∘ suc) (makeSeq 0 i)     ≡⟨⟩
        map (lookup′ bs) (makeSeq 0 i)                 ∎
      where open ≡-Reasoning

  open ≡-Reasoning

transformʷ-✓ {i} v (notʷ x) =
  begin
    map (eval₀ tv) (transformʷ (notʷ x)) ≡⟨⟩
    map (eval₀ tv) (~-build tx)          ≡⟨ ~-eval tv tx ⟩
    ~ (map (eval₀ tv) tx)                ≡⟨ kong (transformʷ-✓ v x) ⟩
    ~ (evalʷ v x)                        ∎
  where
  open ≡-Reasoning

  tv = transformᵛ v
  tx = transformʷ x

transformʷ-✓ {i} v (andʷ x y) =
  begin
    map (eval₀ tv) (transformʷ (andʷ x y)) ≡⟨⟩
    map (eval₀ tv) (∧-build tx ty)         ≡⟨ ∧-eval tv tx ty ⟩
    map (eval₀ tv) tx ∧ʷ map (eval₀ tv) ty ≡⟨ kong (transformʷ-✓ v x) ⟩
    evalʷ v x ∧ʷ map (eval₀ tv) ty         ≡⟨ kong (transformʷ-✓ v y) ⟩
    evalʷ v x ∧ʷ evalʷ v y                 ∎
  where
  open ≡-Reasoning

  tv = transformᵛ v
  tx = transformʷ x
  ty = transformʷ y

transformʷ-✓ {i} v (orʷ x y) =
  begin
    map (eval₀ tv) (transformʷ (orʷ x y))  ≡⟨⟩
    map (eval₀ tv) (∨-build tx ty)         ≡⟨ ∨-eval tv tx ty ⟩
    map (eval₀ tv) tx ∨ʷ map (eval₀ tv) ty ≡⟨ kong (transformʷ-✓ v x) ⟩
    evalʷ v x ∨ʷ map (eval₀ tv) ty         ≡⟨ kong (transformʷ-✓ v y) ⟩
    evalʷ v x ∨ʷ evalʷ v y                 ∎
  where
  open ≡-Reasoning

  tv = transformᵛ v
  tx = transformʷ x
  ty = transformʷ y

transformʷ-✓ {i} v (eorʷ x y) =
  begin
    map (eval₀ tv) (transformʷ (eorʷ x y))   ≡⟨⟩
    map (eval₀ tv) (eorBuild tx ty)          ≡⟨ eorEval tv tx ty ⟩
    map (eval₀ tv) tx xorʷ map (eval₀ tv) ty ≡⟨ kong (transformʷ-✓ v x) ⟩
    evalʷ v x xorʷ map (eval₀ tv) ty         ≡⟨ kong (transformʷ-✓ v y) ⟩
    evalʷ v x xorʷ evalʷ v y                 ∎
  where
  open ≡-Reasoning

  tv = transformᵛ v
  tx = transformʷ x
  ty = transformʷ y

transformʷ-✓ {i} v (negʷ x) =
  begin
    map (eval₀ tv) (transformʷ (negʷ x)) ≡⟨⟩
    map (eval₀ tv) (↕-build tx)          ≡⟨ ↕-eval tv tx ⟩
    ↕ (map (eval₀ tv) tx)                ≡⟨ kong (transformʷ-✓ v x) ⟩
    drop 1 (↕′ (evalʷ v x))              ≡⟨⟩
    ↕ (evalʷ v x)                        ∎
  where
  open ≡-Reasoning

  tv = transformᵛ v
  tx = transformʷ x

transformʷ-✓ {i} v (addʷ x y) =
  begin
    map (eval₀ tv) (transformʷ (addʷ x y)) ≡⟨⟩
    map (eval₀ tv) (+-build tx ty)         ≡⟨ +-eval tv tx ty ⟩
    map (eval₀ tv) tx ⊞ map (eval₀ tv) ty  ≡⟨ kong (transformʷ-✓ v x) ⟩
    evalʷ v x ⊞ map (eval₀ tv) ty          ≡⟨ kong (transformʷ-✓ v y) ⟩
    evalʷ v x ⊞ evalʷ v y                  ∎
  where
  open ≡-Reasoning

  tv = transformᵛ v
  tx = transformʷ x
  ty = transformʷ y

transformʷ-✓ {i} v (subʷ x y) =
  begin
    map (eval₀ tv) (transformʷ (subʷ x y)) ≡⟨⟩
    map (eval₀ tv) (∸-build tx ty)         ≡⟨ ∸-eval tv tx ty ⟩
    map (eval₀ tv) tx ⊟ map (eval₀ tv) ty  ≡⟨ kong (transformʷ-✓ v x) ⟩
    evalʷ v x ⊟ map (eval₀ tv) ty          ≡⟨ kong (transformʷ-✓ v y) ⟩
    evalʷ v x ⊟ evalʷ v y                  ∎
  where
  open ≡-Reasoning

  tv = transformᵛ v
  tx = transformʷ x
  ty = transformʷ y

transformʷ-✓ {i} v (mulʷ x y) =
  begin
    map (eval₀ tv) (transformʷ (mulʷ x y)) ≡⟨⟩
    map (eval₀ tv) (*-build tx ty)         ≡⟨ *-eval tv tx ty ⟩
    map (eval₀ tv) tx ⊠ map (eval₀ tv) ty  ≡⟨ kong (transformʷ-✓ v x) ⟩
    evalʷ v x ⊠ map (eval₀ tv) ty          ≡⟨ kong (transformʷ-✓ v y) ⟩
    evalʷ v x ⊠ evalʷ v y                  ∎
  where
  open ≡-Reasoning

  tv = transformᵛ v
  tx = transformʷ x
  ty = transformʷ y

transformʷ-✓ {i} v (iteʷ x y z) =
  begin
    map (eval₀ tv) (transformʷ (iteʷ x y z))                       ≡⟨⟩
    map (eval₀ tv) (iteBuild tx ty tz)                             ≡⟨ iteEval tv tx ty tz ⟩
    (if eval₀ tv tx then map (eval₀ tv) ty else map (eval₀ tv) tz) ≡⟨ kong (transformᵇ-✓ v x) ⟩
    (if evalᵇ v x then map (eval₀ tv) ty else map (eval₀ tv) tz)   ≡⟨ kong (transformʷ-✓ v y) ⟩
    (if evalᵇ v x then evalʷ v y else map (eval₀ tv) tz)           ≡⟨ kong (transformʷ-✓ v z) ⟩
    (if evalᵇ v x then evalʷ v y else evalʷ v z)                   ∎
  where
  open ≡-Reasoning

  tv = transformᵛ v
  tx = transformᵇ x
  ty = transformʷ y
  tz = transformʷ z

unsatʷ-✓ : ∀ {i} f → (∀ v → eval₀ v (transformᵇ {i} f) ≡ false) → (∀ v → evalᵇ v f ≡ false)
unsatʷ-✓ f p v = trans (sym (transformᵇ-✓ v f)) (p (transformᵛ v))
