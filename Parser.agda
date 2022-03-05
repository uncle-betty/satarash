import Data.Nat

module Parser where

open import Agda.Builtin.Nat using () renaming (mod-helper to modʰ ; div-helper to divʰ)
open import Category.Monad using (RawMonad)
open import Data.Bool using (Bool ; true ; false)
open import Data.Char using (Char ; fromℕ ; toℕ) renaming (_≟_ to _≟ᶜ_)
open import Data.List
  using (List ; length) renaming ([] to []ˡ ; _∷_ to _∷ˡ_ ; map to mapˡ ; _++_ to _++ˡ_)
open import Data.List.Properties using (++-assoc)
open import Data.Maybe using (Maybe ; nothing ; just) renaming (map to mapᵐ)
open import Data.Maybe.Categorical using (monad)
open import Data.Nat using (
    ℕ ; zero ; suc ; pred ; _+_ ; _∸_ ; _*_ ; _^_ ; _≤_ ; z≤n ; s≤s ; _≤?_ ; _<_ ; _<?_ ;
    NonZero ; >-nonZero⁻¹
  )
open import Data.Nat.Divisibility using (_∣_ ; n∣m*n)
open import Data.Nat.DivMod using (
    _/_ ; _%_ ; m/n<m ; m*n/n≡m ; m<n⇒m/n≡0 ; +-distrib-/-∣ʳ ; m/n≡1+[m∸n]/n ;
    n%1≡0 ; m%n<n ; m≤n⇒m%n≡m ; [m+n]%n≡m%n ; [m+kn]%n≡m%n ; m≡m%n+[m/n]*n
  )
open import Data.Nat.Induction using (<-wellFounded ; <-wellFounded-fast)
open import Data.Nat.Properties using (
    +-comm ; +-identityʳ ; m+n∸n≡m ; m∸n+n≡m ; +-assoc ; +-∸-assoc ; ∸-+-assoc ;
    *-comm ; *-assoc ; *-identityʳ ; *-distribʳ-+ ;
    <-strictTotalOrder ; module ≤-Reasoning ; ≤-refl ; ≤-trans ; <-trans ; <-transˡ ; n≤1+n ;
    n<1+n ; ≮⇒≥ ; <⇒≤pred ; +-monoˡ-≤ ; ∸-monoˡ-≤ ; ∸-monoʳ-< ; *-monoʳ-≤ )
open import Data.Product using (∃-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ ; map₁ ; map₂)
open import Data.String using (String ; toList ; fromList)
open import Data.Vec using (Vec ; reverse) renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_)
open import Function using (_$_ ; case_of_ ; _∘_)
open import Function.Reasoning using (_|>_ ; ∋-syntax)
open import Induction.WellFounded using (Acc ; acc)
open import Level using (0ℓ)
open import Relation.Binary.Construct.On using (wellFounded)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; cong ; _≢_ ; subst ; module ≡-Reasoning)
open import Relation.Nullary using (¬_ ; yes ; no)
open import Relation.Nullary.Negation using (contradiction)

open RawMonad (monad {0ℓ})

module AgdaSetMap where
  open import Data.Tree.AVL.Sets <-strictTotalOrder using (
      ⟨Set⟩
    ) renaming (
      empty to emptyˢ ; insert to insertˢ ; headTail to headTailˢ
    ) public

  open import Data.Tree.AVL.Map <-strictTotalOrder using (
      Map
    ) renaming (
      empty to emptyᵐ ; insert to insertᵐ ; lookup to lookupᵐ ; delete to deleteᵐ ;
      initLast to initLastᵐ ; toList to toListᵐ
    ) public

module HaskellSetMap where
  {-# FOREIGN GHC
    import qualified Data.List
    import qualified Data.Map
    import qualified Data.Set

    data HeadTail = HeadTail Integer (Data.Set.Set Integer)
    data InitLast a = InitLast (Data.Map.Map Integer a) Integer a
    data KeyValue a = KeyValue Integer a

    headTailAux :: Data.Set.Set Integer -> Maybe HeadTail
    headTailAux s =
      if (Data.Set.null s) then
        Nothing
      else
        let (n, s') = Data.Set.deleteFindMin s in
        Just (HeadTail n s')

    initLastAux :: Data.Map.Map Integer a -> Maybe (InitLast a)
    initLastAux m =
      if (Data.Map.null m) then
        Nothing
      else
        let ((k, v), m') = Data.Map.deleteFindMax m in
        Just (InitLast m' k v)

    toListAux :: Data.Map.Map Integer a -> [KeyValue a]
    toListAux m = Data.List.map (uncurry KeyValue) (Data.Map.toList m)
  #-}

  postulate ⟨Set⟩′ : (S : Set) → Set

  ⟨Set⟩ : Set
  ⟨Set⟩ = ⟨Set⟩′ ℕ

  data HeadTail : Set where
    headTail : ℕ → ⟨Set⟩ → HeadTail

  {-# COMPILE GHC ⟨Set⟩′ = type Data.Set.Set #-}
  {-# COMPILE GHC HeadTail = data HeadTail (HeadTail) #-}

  postulate emptyˢ : ⟨Set⟩
  postulate insertˢ : ℕ → ⟨Set⟩ → ⟨Set⟩
  postulate headTailAux : ⟨Set⟩ → Maybe HeadTail

  {-# COMPILE GHC emptyˢ = Data.Set.empty #-}
  {-# COMPILE GHC insertˢ = Data.Set.insert #-}
  {-# COMPILE GHC headTailAux = headTailAux #-}

  headTailˢ : ⟨Set⟩ → Maybe (ℕ × ⟨Set⟩)
  headTailˢ r = mapᵐ (λ { (headTail n r′) → n , r′ }) (headTailAux r)

  postulate Map′ : (S T : Set) → Set

  Map : (S : Set) → Set
  Map = Map′ ℕ

  data InitLast (S : Set) : Set where
    initLast : Map S → ℕ → S → InitLast S

  data KeyValue (S : Set) : Set where
    keyValue : ℕ → S → KeyValue S

  {-# COMPILE GHC Map′ = type Data.Map.Map #-}
  {-# COMPILE GHC InitLast = data InitLast (InitLast) #-}
  {-# COMPILE GHC KeyValue = data KeyValue (KeyValue) #-}

  postulate emptyᵐ : {S : Set} → Map S
  postulate insertᵐ : {S : Set} → ℕ → S → Map S → Map S
  postulate lookupᵐ : {S : Set} → ℕ → Map S → Maybe S
  postulate deleteᵐ : {S : Set} → ℕ → Map S → Map S
  postulate initLastAux : {S : Set} → Map S → Maybe (InitLast S)
  postulate toListAux : {S : Set} → Map S → List (KeyValue S)

  {-# COMPILE GHC emptyᵐ = \_ -> Data.Map.empty #-}
  {-# COMPILE GHC insertᵐ = \_ -> Data.Map.insert #-}
  {-# COMPILE GHC lookupᵐ = \_ -> Data.Map.lookup #-}
  {-# COMPILE GHC deleteᵐ = \_ -> Data.Map.delete #-}
  {-# COMPILE GHC initLastAux = \_ -> initLastAux #-}
  {-# COMPILE GHC toListAux = \_ -> toListAux #-}

  initLastᵐ : {S : Set} → Map S → Maybe (Map S × (ℕ × S))
  initLastᵐ t = mapᵐ (λ { (initLast t′ k v) → t′ , (k , v) }) (initLastAux t)

  toListᵐ : {S : Set} → Map S → List (ℕ × S)
  toListᵐ t = mapˡ (λ { (keyValue k v) → k , v }) (toListAux t)

-- open AgdaSetMap instead for slower implementation in Agda
open HaskellSetMap

≤-suc : ∀ {m n} → m ≤ n → m ≤ suc n
≤-suc {m} {n} m≤n = ≤-trans m≤n (n≤1+n n)

<-suc : ∀ {m n} → m < n → m < suc n
<-suc {m} {n} m<n = <-trans m<n (n<1+n n)

≤⇒<-suc : ∀ {m n} → m ≤ n → m < suc n
≤⇒<-suc {m} {n} m≤n = s≤s m≤n

data Token : Set where
  isSpace   : Token
  isNewLine : Token
  isDigit   : (n : ℕ) → Token
  isMinus   : Token
  isOther   : Token

token : (c : Char) → Token
token ' '  = isSpace
token '\n' = isNewLine
token '0'  = isDigit 0
token '1'  = isDigit 1
token '2'  = isDigit 2
token '3'  = isDigit 3
token '4'  = isDigit 4
token '5'  = isDigit 5
token '6'  = isDigit 6
token '7'  = isDigit 7
token '8'  = isDigit 8
token '9'  = isDigit 9
token '-'  = isMinus
token _    = isOther

space : List Char → List Char
space []ˡ       = []ˡ
space (c ∷ˡ cs) =
  case token c of λ where
    isSpace   → space cs
    isNewLine → space cs
    _         → c ∷ˡ cs

space-≤ : ∀ cs → length (space cs) ≤ length cs
space-≤ []ˡ       = ≤-refl
space-≤ (c ∷ˡ cs) with token c
space-≤ (c ∷ˡ cs) | isSpace   = ≤-suc (space-≤ cs)
space-≤ (c ∷ˡ cs) | isNewLine = ≤-suc (space-≤ cs)
space-≤ (c ∷ˡ cs) | isDigit _ = ≤-refl
space-≤ (c ∷ˡ cs) | isMinus   = ≤-refl
space-≤ (c ∷ˡ cs) | isOther   = ≤-refl

line : List Char → List Char
line []ˡ       = []ˡ
line (c ∷ˡ cs) =
  case token c of λ where
    isNewLine → space cs
    _         → line cs

line-≤ : ∀ cs → length (line cs) ≤ length cs
line-≤ []ˡ       = ≤-refl
line-≤ (c ∷ˡ cs) with token c
line-≤ (c ∷ˡ cs) | isSpace   = ≤-suc (line-≤ cs)
line-≤ (c ∷ˡ cs) | isNewLine = ≤-suc (space-≤ cs)
line-≤ (c ∷ˡ cs) | isDigit _ = ≤-suc (line-≤ cs)
line-≤ (c ∷ˡ cs) | isMinus   = ≤-suc (line-≤ cs)
line-≤ (c ∷ˡ cs) | isOther   = ≤-suc (line-≤ cs)

known : List Char → List Char → Maybe (List Char)
known []ˡ       []ˡ       = just []ˡ
known []ˡ       (e ∷ˡ es) = nothing
known (c ∷ˡ cs) []ˡ       =
  case token c of λ where
    isSpace   → just (space cs)
    isNewLine → just (space cs)
    _         → nothing
known (c ∷ˡ cs) (e ∷ˡ es) =
  case c ≟ᶜ e of λ where
    (yes _) → known cs es
    (no  _) → nothing

known-≤ : ∀ cs es cs′ → known cs es ≡ just cs′ → length cs′ ≤ length cs
known-≤ []ˡ       []ˡ       cs′ refl = ≤-refl
known-≤ (c ∷ˡ cs) []ˡ       cs′ p    with token c
known-≤ (c ∷ˡ cs) []ˡ       cs′ refl | isSpace   = ≤-suc (space-≤ cs)
known-≤ (c ∷ˡ cs) []ˡ       cs′ refl | isNewLine = ≤-suc (space-≤ cs)
known-≤ (c ∷ˡ cs) (e ∷ˡ es) cs′ p    with c ≟ᶜ e
known-≤ (c ∷ˡ cs) (e ∷ˡ es) cs′ p    | yes _ = ≤-suc (known-≤ cs es cs′ p)

natural′ : List Char → ℕ → Maybe (ℕ × List Char)
natural′ []ˡ       _ = nothing
natural′ (c ∷ˡ cs) a =
  case token c of λ where
    isSpace     → just (a , space cs)
    isNewLine   → just (a , space cs)
    (isDigit n) → natural′ cs (a * 10 + n)
    _           → nothing

natural′-< : ∀ cs a r cs′ → natural′ cs a ≡ just (r , cs′) → length cs′ < length cs
natural′-< (c ∷ˡ cs) a r cs′ p    with token c
natural′-< (c ∷ˡ cs) a r cs′ refl | isSpace   = s≤s (space-≤ cs)
natural′-< (c ∷ˡ cs) a r cs′ refl | isNewLine = s≤s (space-≤ cs)
natural′-< (c ∷ˡ cs) a r cs′ p    | isDigit n = <-suc (natural′-< cs (a * 10 + n) r cs′ p)

natural : List Char → Maybe (ℕ × List Char)
natural cs = natural′ cs 0

natural-< : ∀ cs r cs′ → natural cs ≡ just (r , cs′) → length cs′ < length cs
natural-< cs r cs′ = natural′-< cs 0 r cs′

printDigit : (n : ℕ) → Char
printDigit n = fromℕ (toℕ '0' + n % 10)

printDigit-✓ : ∀ n → token (printDigit n) ≡ isDigit (n % 10)
printDigit-✓ n = go n
  where
  pattern
    10+n n = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n)))))))))

  open ≡-Reasoning

  go : ∀ n → token (printDigit n) ≡ isDigit (n % 10)
  go 0        = refl
  go 1        = refl
  go 2        = refl
  go 3        = refl
  go 4        = refl
  go 5        = refl
  go 6        = refl
  go 7        = refl
  go 8        = refl
  go 9        = refl
  go (10+n n) =
    token (printDigit (10+n n))             ≡⟨⟩
    token (fromℕ (toℕ '0' + (10+n n % 10))) ≡⟨⟩
    token (fromℕ (toℕ '0' + (n % 10)))      ≡⟨ go n ⟩
    isDigit (n % 10)                        ∎

mn≢0 : (m n : ℕ) → .⦃ NonZero m ⦄ → .⦃ NonZero n ⦄ → NonZero (m * n)
mn≢0 (suc m) (suc n) = _

10^e≢0 : ∀ {e} → NonZero (10 ^ e)
10^e≢0 {zero}  = _
10^e≢0 {suc e} = mn≢0 10 (10 ^ e) ⦃ _ ⦄ ⦃ 10^e≢0 {e} ⦄

10^e*10≢0 : ∀ {e} → NonZero (10 ^ e * 10)
10^e*10≢0 {e} = mn≢0 (10 ^ e) 10 ⦃ 10^e≢0 {e} ⦄

infixl 7 _*10^_ _/10^_ _%10^_

_*10^_ : ℕ → ℕ → ℕ
_*10^_ n e = n * 10 ^ e

_/10^_ : ℕ → ℕ → ℕ
_/10^_ n e = _/_ n (10 ^ e) ⦃ 10^e≢0 {e} ⦄

_%10^_ : ℕ → ℕ → ℕ
_%10^_ n e = _%_ n (10 ^ e) ⦃ 10^e≢0 {e} ⦄

n<m⇒n%m≡n : ∀ {n m} → n < m → .⦃ _ : NonZero m ⦄ → n % m ≡ n
n<m⇒n%m≡n {n} {suc m} n<m = m≤n⇒m%n≡m (<⇒≤pred n<m)

m≤n⇒[n∸m]%m≡n%m : ∀ {n m} → m ≤ n → .⦃ _ : NonZero m ⦄ → (n ∸ m) % m ≡ n % m
m≤n⇒[n∸m]%m≡n%m {n} {m} m≤n =
  (n ∸ m) % m     ≡˘⟨ [m+n]%n≡m%n (n ∸ m) m ⟩
  (n ∸ m + m) % m ≡⟨ cong (_% m) (m∸n+n≡m m≤n) ⟩
  n % m           ∎
  where open ≡-Reasoning

km≤n⇒[n∸km]%m≡n%m : ∀ {k m n} → k * m ≤ n → .⦃ _ : NonZero m ⦄ → (n ∸ k * m) % m ≡ n % m
km≤n⇒[n∸km]%m≡n%m {zero}  {m} {n} km≤n     = refl
km≤n⇒[n∸km]%m≡n%m {suc k} {m} {n} m+km≤n = begin-equality
  (n ∸ suc k * m)   % m ≡⟨⟩
  (n ∸ (m + k * m)) % m ≡⟨ cong (λ # → (n ∸ #) % m) (+-comm m (k * m)) ⟩
  (n ∸ (k * m + m)) % m ≡˘⟨ cong (_% m) (∸-+-assoc n (k * m) m) ⟩
  (n ∸ k * m ∸ m)   % m ≡⟨ m≤n⇒[n∸m]%m≡n%m m≤n∸km ⟩
  (n ∸ k * m)       % m ≡⟨ km≤n⇒[n∸km]%m≡n%m {k} km≤n′ ⟩
  n                 % m ∎
  where
  open ≤-Reasoning

  m≤n∸km : m ≤ n ∸ k * m
  m≤n∸km =
       m+km≤n                                   ∶ m + k * m         ≤ n
    |> ∸-monoˡ-≤ (k * m)                        ∶ m + k * m ∸ k * m ≤ n ∸ k * m
    |> subst (_≤ n ∸ k * m) (m+n∸n≡m m (k * m)) ∶ m                 ≤ n ∸ k * m

  km≤n′ : k * m ≤ n
  km≤n′ = begin
    k * m     ≤⟨ +-monoˡ-≤ (k * m) z≤n ⟩
    m + k * m ≤⟨ m+km≤n ⟩
    n         ∎

n%km%m≡n%m : ∀ k m n → .⦃ _ : NonZero k ⦄ → .⦃ _ : NonZero m ⦄ → .⦃ _ : NonZero (k * m) ⦄ →
  n % (k * m) % m ≡ n % m
n%km%m≡n%m k m n = go k m n (<-wellFounded n)
  where
  open ≡-Reasoning

  go : ∀ k m n → Acc _<_ n → .⦃ _ : NonZero k ⦄ → .⦃ _ : NonZero m ⦄ → .⦃ _ : NonZero (k * m) ⦄ →
    n % (k * m) % m ≡ n % m
  go k m n (acc rs) with n <? k * m
  go k m n (acc rs) | yes n<km =
    n % (k * m) % m ≡⟨ cong (_% m) (n<m⇒n%m≡n n<km) ⟩
    n           % m ∎
  go k m n (acc rs) | no ¬n<km =
    let acc′ = rs (n ∸ k * m) n∸km<n in
    n           % (k * m) % m ≡˘⟨ cong (_% m) (m≤n⇒[n∸m]%m≡n%m km≤n) ⟩
    (n ∸ k * m) % (k * m) % m ≡⟨ go k m (n ∸ k * m) acc′ ⟩
    (n ∸ k * m)           % m ≡⟨ km≤n⇒[n∸km]%m≡n%m {k} km≤n ⟩
    n % m                     ∎
    where
    km≤n : k * m ≤ n
    km≤n = ≮⇒≥ ¬n<km

    0<km : .⦃ NonZero (k * m) ⦄ → 0 < k * m
    0<km = >-nonZero⁻¹ (k * m)

    n∸km<n : .⦃ NonZero (k * m) ⦄ → n ∸ k * m < n
    n∸km<n = ∸-monoʳ-< 0<km km≤n

n/i≡∙ : ∀ n m i → .⦃ _ : NonZero i ⦄ → .⦃ _ : NonZero (m * i) ⦄ →
  n / i ≡ n % (m * i) / i + n / (m * i) * m
n/i≡∙ n m i =
  n / i                                     ≡⟨ cong (_/ i) (m≡m%n+[m/n]*n n (m * i)) ⟩
  (n % (m * i) + n / (m * i) * (m * i)) / i ≡⟨ cong (λ # → (n % (m * i) + #) / i) (sym (*-assoc (n / (m * i)) m i)) ⟩
  (n % (m * i) + n / (m * i) * m * i) / i   ≡⟨ +-distrib-/-∣ʳ (n % (m * i)) (n∣m*n (n / (m * i) * m)) ⟩
  n % (m * i) / i + n / (m * i) * m * i / i ≡⟨ cong (n % (m * i) / i +_) (m*n/n≡m (n / (m * i) * m) i) ⟩
  n % (m * i) / i + n / (m * i) * m         ∎
  where open ≡-Reasoning

n<mi⇒n/i<m : ∀ n m i → n < m * i → .⦃ _ : NonZero i ⦄ → n / i < m
n<mi⇒n/i<m n m i n<mi with n <? i
n<mi⇒n/i<m n m i n<mi | yes n<i = begin-strict
  n / i ≡⟨ m<n⇒m/n≡0 n<i ⟩
  0     <⟨ lemma₁ n m i n<mi ⟩
  m     ∎
  where
  open ≤-Reasoning

  lemma₁ : ∀ n m i → n < m * i → 0 < m
  lemma₁ n (suc m) i n<mi = s≤s z≤n

n<mi⇒n/i<m n (suc m) i n<[1+m]i | no ¬n<i = begin-strict
  n / i           ≡⟨ m/n≡1+[m∸n]/n (≮⇒≥ ¬n<i) ⟩
  1 + (n ∸ i) / i <⟨ s≤s (n<mi⇒n/i<m (n ∸ i) m i (lemma₃ (≮⇒≥ ¬n<i))) ⟩
  suc m           ∎
  where
  open ≤-Reasoning

  lemma₁ : suc m * i ∸ i ≡ m * i
  lemma₁ = begin-equality
    suc m * i ∸ i ≡⟨⟩
    i + m * i ∸ i ≡⟨ cong (_∸ i) (+-comm i (m * i)) ⟩
    m * i + i ∸ i ≡⟨ m+n∸n≡m (m * i) i ⟩
    m * i         ∎

  lemma₂ : i ≤ n → suc n ∸ i ≡ suc (n ∸ i)
  lemma₂ i≤n = +-∸-assoc 1 i≤n

  lemma₃ : i ≤ n → n ∸ i < m * i
  lemma₃ i≤n =
       n<[1+m]i                              ∶ n         < suc m * i
    |> ∸-monoˡ-≤ i                           ∶ suc n ∸ i ≤ suc m * i ∸ i
    |> subst (_≤ suc m * i ∸ i) (lemma₂ i≤n) ∶ n ∸ i     < suc m * i ∸ i
    |> subst (n ∸ i <_) lemma₁               ∶ n ∸ i     < m * i

n%mi/i<m : ∀ n m i → .⦃ _ : NonZero i ⦄ → .⦃ _ : NonZero (m * i) ⦄ → n % (m * i) / i < m
n%mi/i<m n m i = n<mi⇒n/i<m (n % (m * i)) m i (m%n<n n (m * i))

n%mi/i≡n/i%m : ∀ n m i → .⦃ _ : NonZero i ⦄ → .⦃ _ : NonZero m ⦄ → .⦃ _ : NonZero (m * i) ⦄ →
  n / i % m ≡ n % (m * i) / i
n%mi/i≡n/i%m n m i = begin
  n / i % m                               ≡⟨ cong (_% m) (n/i≡∙ n m i) ⟩
  (n % (m * i) / i + n / (m * i) * m) % m ≡⟨ [m+kn]%n≡m%n (n % (m * i) / i) (n / (m * i)) m ⟩
  n % (m * i) / i % m                     ≡⟨ n<m⇒n%m≡n (n%mi/i<m n m i) ⟩
  n % (m * i) / i                         ∎
  where open ≡-Reasoning

printNatural″ : ℕ → ℕ → List Char
printNatural″ zero    n = []ˡ
printNatural″ (suc e) n = printDigit (n /10^ e) ∷ˡ printNatural″ e n

printNatural″-✓ : ∀ e n cs a →
  natural′ (printNatural″ e n ++ˡ ' ' ∷ˡ cs) a ≡ just (a *10^ e + n %10^ e , space cs)
printNatural″-✓ zero    n cs a =
  just (a , space cs)                ≡⟨ cong (λ # → just (# , space cs)) lemma₁ ⟩
  just (a * 1 + n %10^ 0 , space cs) ∎
  where
  open ≡-Reasoning

  lemma₁ : a ≡ a * 1 + n %10^ 0
  lemma₁ = sym $
    a * 1 + n %10^ 0 ≡⟨ cong (_+ n %10^ 0) (*-identityʳ a) ⟩
    a     + n %10^ 0 ≡⟨ cong (a +_) (n%1≡0 n) ⟩
    a     + 0        ≡⟨ +-identityʳ a ⟩
    a                ∎

printNatural″-✓ (suc e) n cs a rewrite printDigit-✓ (n /10^ e) =
  natural′ (printNatural″ e n ++ˡ ' ' ∷ˡ cs) (a * 10 + (n /10^ e % 10)) ≡⟨ printNatural″-✓ e n cs (a * 10 + (n /10^ e) % 10) ⟩
  just ((a * 10 + n /10^ e % 10) * 10 ^ e + n %10^ e , space cs)        ≡⟨ cong (λ # → just (# , space cs)) lemma₂ ⟩
  just (a * 10 ^ suc e + n %10^ suc e , space cs)                       ∎
  where
  open ≡-Reasoning

  instance
    _ = 10^e≢0 {e}

  1+e = suc e

  lemma₁ : ∀ n e → n /10^ e % 10 ≡ n %10^ (suc e) /10^ e
  lemma₁ n e =
    n /10^ e % 10         ≡⟨ n%mi/i≡n/i%m n 10 (10 ^ e) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ 10^e≢0 {suc e} ⦄ ⟩
    n %10^ (suc e) /10^ e ∎

  lemma₂ : (a * 10 + n /10^ e % 10) *10^ e + n %10^ e ≡ a *10^ suc e + n %10^ suc e
  lemma₂ =
    (a * 10 + n /10^ e % 10) *10^ e + n %10^ e                  ≡⟨ cong (_+ n %10^ e) (*-distribʳ-+ (10 ^ e) (a * 10) (n /10^ e % 10)) ⟩
    a * 10 *10^ e + n /10^ e % 10 *10^ e + n %10^ e             ≡⟨ +-assoc (a * 10 *10^ e) (n /10^ e % 10 *10^ e) (n %10^ e) ⟩
    a * 10 *10^ e + (n /10^ e % 10 *10^ e + n %10^ e)           ≡⟨ cong (_+ (n /10^ e % 10 *10^ e + n %10^ e)) (*-assoc a 10 (10 ^ e)) ⟩
    a *10^ 1+e + (n /10^ e % 10 *10^ e + n %10^ e)              ≡⟨ cong (λ # → a *10^ 1+e + (# *10^ e + n %10^ e)) (lemma₁ n e) ⟩
    a *10^ 1+e + (n %10^ 1+e /10^ e *10^ e + n %10^ e)          ≡˘⟨ cong (λ # → a *10^ 1+e + (n %10^ 1+e /10^ e *10^ e + #)) (n%km%m≡n%m 10 (10 ^ e) n ⦃ _ ⦄ ⦃ _ ⦄ ⦃ mn≢0 10 (10 ^ e) ⦄ ) ⟩
    a *10^ 1+e + (n %10^ 1+e /10^ e *10^ e + n %10^ 1+e %10^ e) ≡⟨ cong (a *10^ 1+e +_)(+-comm (n %10^ 1+e /10^ e *10^ e) (n %10^ 1+e %10^ e)) ⟩
    a *10^ 1+e + (n %10^ 1+e %10^ e + n %10^ 1+e /10^ e *10^ e) ≡˘⟨ cong (a *10^ 1+e +_) (m≡m%n+[m/n]*n (n %10^ 1+e) (10 ^ e)) ⟩
    a *10^ 1+e + n %10^ 1+e                                     ∎

¬n<10⇒n≢0 : ∀ {n} → ¬ (n < 10) → NonZero n
¬n<10⇒n≢0 {zero}  ¬n<10 = contradiction (s≤s z≤n) ¬n<10
¬n<10⇒n≢0 {suc n} ¬n<10 = _

2≤10 : 2 ≤ 10
2≤10 = s≤s (s≤s z≤n)

n/10<n : ∀ {n} → .⦃ _ : NonZero n ⦄ → n / 10 < n
n/10<n {n} = m/n<m n 10 2≤10

printLength′ : (n : ℕ) → Acc _<_ n → ℕ
printLength′ n (acc rs) =
  case n <? 10 of λ where
    (yes n<10) → 1
    (no ¬n<10) →
      let m′ = rs (n / 10) (n/10<n ⦃ ¬n<10⇒n≢0 ¬n<10 ⦄) in
      suc (printLength′ (n / 10) m′)

printLength′-✓ : ∀ n m → n %10^ (printLength′ n m) ≡ n
printLength′-✓ n (acc rs) with n <? 10
printLength′-✓ n (acc rs) | yes n<10 = n<m⇒n%m≡n n<10
printLength′-✓ n (acc rs) | no ¬n<10 =
  lhs                      ≡⟨ m≡m%n+[m/n]*n lhs 10 ⟩
  lhs % 10 + lhs / 10 * 10 ≡⟨ cong (λ # → lhs % 10 + # * 10) lhs/10≡n/10 ⟩
  lhs % 10 + n   / 10 * 10 ≡⟨ cong (_+ n / 10 * 10) lhs%10≡n%10 ⟩
  n   % 10 + n   / 10 * 10 ≡˘⟨ m≡m%n+[m/n]*n n 10 ⟩
  n                        ∎
  where
  open ≡-Reasoning

  instance
    _ : NonZero n
    _ = ¬n<10⇒n≢0 ¬n<10

  m′ = rs (n / 10) n/10<n
  lhs = n %10^ (suc (printLength′ (n / 10) m′))

  cong-≢0 : (f : (n : ℕ) → .⦃ NonZero n ⦄ → ℕ) {x y : ℕ } → x ≡ y → .⦃ _ : NonZero x ⦄ →
    .⦃ _ : NonZero y ⦄ → f x ≡ f y
  cong-≢0 f refl = refl

  instance
    _ : NonZero (10 ^ printLength′ (n / 10) m′)
    _ = 10^e≢0 {printLength′ (n / 10) m′}

    _ : NonZero (10 ^ suc (printLength′ (n / 10) m′))
    _ = 10^e≢0 {suc (printLength′ (n / 10) m′)}

    _ : NonZero (10 ^ printLength′ (n / 10) m′ * 10)
    _ = mn≢0 (10 ^ printLength′ (n / 10) m′) 10

  lhs/10≡n/10 : lhs / 10 ≡ n / 10
  lhs/10≡n/10 =
    let m′ = rs (n / 10) n/10<n in
    lhs / 10                                      ≡⟨⟩
    n %10^ (suc (printLength′ (n / 10) m′)) / 10  ≡⟨ cong-≢0 (λ # → n % # / 10) (*-comm 10 (10 ^ printLength′ (n / 10) m′)) ⟩
    n % (10 ^ printLength′ (n / 10) m′ * 10) / 10 ≡˘⟨ n%mi/i≡n/i%m n (10 ^ printLength′ (n / 10) m′) 10 ⟩
    n / 10 %10^ printLength′ (n / 10) m′          ≡⟨ printLength′-✓ (n / 10) m′ ⟩
    n / 10                                        ∎

  lhs%10≡n%10 : lhs % 10 ≡ n % 10
  lhs%10≡n%10 =
    let m′ = rs (n / 10) n/10<n in
    lhs % 10                                      ≡⟨⟩
    n %10^ (suc (printLength′ (n / 10) m′)) % 10  ≡⟨ cong-≢0 (λ # → n % # % 10) (*-comm 10 (10 ^ printLength′ (n / 10) m′)) ⟩
    n % (10 ^ printLength′ (n / 10) m′ * 10) % 10 ≡⟨ n%km%m≡n%m (10 ^ printLength′ (n / 10) m′) 10 n ⟩
    n % 10                                        ∎

printLength : ℕ → ℕ
printLength n = printLength′ n (<-wellFounded-fast n)

printLength-✓ : ∀ n → n %10^ (printLength n) ≡ n
printLength-✓ n = printLength′-✓ n (<-wellFounded-fast n)

printNatural′ : ℕ → List Char
printNatural′ n = printNatural″ (printLength n) n

printNatural′-✓ : ∀ n cs →
  natural (printNatural′ n ++ˡ ' ' ∷ˡ cs) ≡ just (n , space cs)
printNatural′-✓ n cs =
  natural (printNatural′ n ++ˡ ' ' ∷ˡ cs)   ≡⟨⟩
  natural (printNatural″ e n ++ˡ ' ' ∷ˡ cs) ≡⟨ printNatural″-✓ e n cs 0 ⟩
  just (n % 10 ^ e , space cs)              ≡⟨ cong (λ # → just (# , space cs)) (printLength-✓ n) ⟩
  just (n , space cs)                       ∎
  where
  open ≡-Reasoning

  e = printLength n

  instance
    _ : NonZero (10 ^ e)
    _ = 10^e≢0 {e}

printNatural : ℕ → List Char
printNatural n = printNatural′ n ++ˡ ' ' ∷ˡ []ˡ

spaceNatural : ∀ n cs → space (printNatural n ++ˡ cs) ≡ printNatural n ++ˡ cs
-- case |n ≡ 0| for |<-wellFounded-skip|
spaceNatural zero cs = refl
-- |suc n <? 10| abstraction changes |p| in parallel with goal
spaceNatural (suc n) cs with (suc n) <? 10 | printDigit-✓ (suc n /10^ pred (printLength (suc n)))
spaceNatural (suc n) cs | yes n<10         | p
  rewrite p = refl
spaceNatural (suc n) cs | no ¬n<10         | p
  rewrite p = refl

printNatural-✓ : ∀ n cs → natural (printNatural n ++ˡ cs) ≡ just (n , space cs)
printNatural-✓ n cs =
  natural (printNatural n ++ˡ cs)                     ≡⟨⟩
  natural ((printNatural″ e n ++ˡ ' ' ∷ˡ []ˡ) ++ˡ cs) ≡⟨ cong natural (lemma₁ (printNatural″ e n) cs) ⟩
  natural (printNatural″ e n ++ˡ ' ' ∷ˡ cs)           ≡⟨⟩
  natural (printNatural′ n ++ˡ ' ' ∷ˡ cs)             ≡⟨ printNatural′-✓ n cs ⟩
  just (n , space cs)                                 ∎
  where
  open ≡-Reasoning

  e = printLength n

  lemma₁ : ∀ xs cs → (xs ++ˡ ' ' ∷ˡ []ˡ) ++ˡ cs ≡ xs ++ˡ ' ' ∷ˡ cs
  lemma₁ []ˡ       cs = refl
  lemma₁ (x ∷ˡ xs) cs = cong (x ∷ˡ_) (lemma₁ xs cs)

spaceNatural-✓ : ∀ n cs → natural (space (printNatural n ++ˡ cs)) ≡ just (n , space cs)
spaceNatural-✓ n cs =
  natural (space (printNatural n ++ˡ cs)) ≡⟨ cong natural (spaceNatural n cs) ⟩
  natural (printNatural n ++ˡ cs)         ≡⟨ printNatural-✓ n cs ⟩
  just (n , space cs)                     ∎
  where open ≡-Reasoning

integer : List Char → Maybe (Bool × ℕ × List Char)
integer []ˡ       = nothing
integer (c ∷ˡ cs) =
  case token c of λ where
    isMinus     → mapᵐ (true ,_) (natural cs)
    (isDigit _) → mapᵐ (false ,_) (natural (c ∷ˡ cs))
    _           → nothing

integer-< : ∀ cs s r cs′ → integer cs ≡ just (s , r , cs′) → length cs′ < length cs
integer-< (c ∷ˡ cs) s r cs′ p    with token c
integer-< (c ∷ˡ cs) s r cs′ p    | isMinus   with natural cs in eq
integer-< (c ∷ˡ cs) s r cs′ refl | isMinus   | just (r′ , cs″) = <-suc (natural-< cs r′ cs″ eq)
integer-< (c ∷ˡ cs) s r cs′ p    | isDigit _ with natural (c ∷ˡ cs) in eq
integer-< (c ∷ˡ cs) s r cs′ refl | isDigit _ | just (r′ , cs″) = natural-< (c ∷ˡ cs) r′ cs″ eq

printInteger : Bool → ℕ → List Char
printInteger true  n = '-' ∷ˡ printNatural n
printInteger false n = printNatural n

spaceInteger : ∀ s n cs → space (printInteger s n ++ˡ cs) ≡ printInteger s n ++ˡ cs
spaceInteger true  n cs = refl
spaceInteger false n cs = spaceNatural n cs

printInteger-✓ : ∀ s n cs → integer (printInteger s n ++ˡ cs) ≡ just (s , n , space cs)
printInteger-✓ true  n       cs = cong (mapᵐ (true ,_)) (printNatural-✓ n cs)
-- case |n ≡ 0| for |<-wellFounded-skip|
printInteger-✓ false zero    cs = refl
{-
  make |p₁| and |p₂| change in parallel with goal:
    - |p₁| and |p₂| affected by |suc n <? 10| abstraction
    - |p₁| affected by rewrites with |p₂|
-}
printInteger-✓ false (suc n) cs with suc n <? 10 | printNatural-✓ (suc n) cs | printDigit-✓ (suc n /10^ pred (printLength (suc n)))
printInteger-✓ false (suc n) cs | yes n<10       | p₁                        | p₂
  rewrite p₂ | p₂
  = cong (mapᵐ (false ,_)) p₁
printInteger-✓ false (suc n) cs | no ¬n<10       | p₁                        | p₂
  rewrite p₂ | p₂
  = cong (mapᵐ (false ,_)) p₁

spaceInteger-✓ : ∀ s n cs → integer (space (printInteger s n ++ˡ cs)) ≡ just (s , n , space cs)
spaceInteger-✓ s n cs =
  integer (space (printInteger s n ++ˡ cs)) ≡⟨ cong integer (spaceInteger s n cs) ⟩
  integer (printInteger s n ++ˡ cs)         ≡⟨ printInteger-✓ s n cs ⟩
  just (s , n , space cs)                   ∎
  where open ≡-Reasoning

with-≡ : {S : Set} → (x : Maybe S) → Maybe (∃[ y ] x ≡ just y)
with-≡ nothing  = nothing
with-≡ (just x) = just (x , refl)

Measure : List Char → Set
Measure = Acc (λ x y → length x < length y)

measure : (cs : List Char) → Measure cs
measure = wellFounded length <-wellFounded

module _ (bitsᶜ : Data.Nat.ℕ) where
  open import Verifier bitsᶜ as V using (
      Proof ; Step ; del ; ext ;
      Clause ; Literal ; pos ; neg ;
      Formula ; Trie ; node ; leaf ; Index
    )

  Translator : Set
  Translator = Map ℕ

  Recycler : Set
  Recycler = ⟨Set⟩

  klause : (cs : List Char) → Measure cs → Maybe (Clause × List Char)
  klause cs (acc rs) = with-≡ (integer cs) >>= λ where
    ((_ , zero , cs′) , p)      → just ([]ˡ , cs′)
    ((false , suc v , cs′) , p) →
      let m′ = rs cs′ (integer-< cs false (suc v) cs′ p) in
      mapᵐ (map₁ (pos v ∷ˡ_)) (klause cs′ m′)
    ((true , suc v , cs′) , p)  →
      let m′ = rs cs′ (integer-< cs true (suc v) cs′ p) in
      mapᵐ (map₁ (neg v ∷ˡ_)) (klause cs′ m′)

  klause-< : ∀ cs r ds″ → (m : Measure cs) → klause cs m ≡ just (r , ds″) → length ds″ < length cs
  klause-< cs r ds″ (acc rs) p with with-≡ (integer cs)
  klause-< cs r ds″ (acc rs) ()   | nothing
  klause-< cs r ds″ (acc rs) refl | just ((_ , zero , cs′) , q) = integer-< cs _ zero cs′ q
  klause-< cs r ds″ (acc rs) p    | just ((false , suc v , cs′) , q)
    with m′ ← rs cs′ (integer-< cs false (suc v) cs′ q)
    with klause cs′ m′ in eq | p
  ... | just (k , cs″) | refl =
    <-trans (klause-< cs′ k cs″ m′ eq) (integer-< cs false (suc v) cs′ q)
  klause-< cs r ds″ (acc rs) p    | just ((true , suc v , cs′) , q)
    with m′ ← rs cs′ (integer-< cs true (suc v) cs′ q)
    with klause cs′ m′ in eq | p
  ... | just (k , cs″) | refl =
    <-trans (klause-< cs′ k cs″ m′ eq) (integer-< cs true (suc v) cs′ q)

  printKlause : Clause → List Char
  printKlause []ˡ          = '0' ∷ˡ '\n' ∷ˡ []ˡ
  printKlause (pos v ∷ˡ k) = printInteger false (suc v) ++ˡ printKlause k
  printKlause (neg v ∷ˡ k) = printInteger true (suc v) ++ˡ printKlause k

  spaceKlause : ∀ k cs → space (printKlause k ++ˡ cs) ≡ printKlause k ++ˡ cs
  spaceKlause []ˡ          cs = refl
  spaceKlause (pos v ∷ˡ k) cs =
    space (printKlause (pos v ∷ˡ k) ++ˡ cs) ≡⟨⟩
    space ((printInteger false (suc v) ++ˡ printKlause k) ++ˡ cs) ≡⟨ cong space (++-assoc (printInteger false (suc v)) (printKlause k) cs) ⟩
    space (printInteger false (suc v) ++ˡ printKlause k ++ˡ cs)   ≡⟨ spaceNatural (suc v) (printKlause k ++ˡ cs) ⟩
    printInteger false (suc v) ++ˡ printKlause k ++ˡ cs           ≡˘⟨ ++-assoc (printInteger false (suc v)) (printKlause k) cs ⟩
    (printInteger false (suc v) ++ˡ printKlause k) ++ˡ cs         ≡⟨⟩
    printKlause (pos v ∷ˡ k) ++ˡ cs ∎
    where open ≡-Reasoning
  spaceKlause (neg v ∷ˡ k) cs = refl

  spaceInteger-with-≡ : ∀ s n cs → with-≡ (integer (space (printInteger s n ++ˡ cs))) ≡
    just ((s , n , space cs) , spaceInteger-✓ s n cs )
  spaceInteger-with-≡ s n cs rewrite spaceInteger-✓ s n cs = refl

  spaceKlause-✓ : ∀ k cs m → klause (space (printKlause k ++ˡ cs)) m ≡ just (k , space cs)
  spaceKlause-✓ []ˡ          cs (acc rs) = refl
  spaceKlause-✓ (pos v ∷ˡ k) cs (acc rs)
    rewrite ++-assoc (printNatural (suc v)) (printKlause k) cs

    with rec ← spaceKlause-✓ k cs -- prepare recursion now, so |rec| gets the |cs′| shortcut
    with cs′ ← printKlause k ++ˡ cs

    rewrite spaceInteger-with-≡ false (suc v) cs′

    with ✓′ ← spaceInteger-✓ false (suc v) cs′
    with <′ ← integer-< (space (printInteger false (suc v) ++ˡ cs′)) false (suc v) (space cs′) ✓′
    with m′ ← rs (space cs′) <′

    rewrite rec m′
    = refl

  spaceKlause-✓ (neg v ∷ˡ k) cs (acc rs)
    rewrite ++-assoc (printNatural (suc v)) (printKlause k) cs

    with rec ← spaceKlause-✓ k cs -- prepare recursion now, so |rec| gets the |cs′| shortcut
    with cs′ ← printKlause k ++ˡ cs

    rewrite spaceInteger-with-≡ true (suc v) cs′

    with ✓′ ← spaceInteger-✓ true (suc v) cs′
    with <′ ← integer-< (space (printInteger true (suc v) ++ˡ cs′)) true (suc v) (space cs′) ✓′
    with m′ ← rs (space cs′) <′

    rewrite rec m′
    = refl

  printKlause-✓ : ∀ k cs m → klause (printKlause k ++ˡ cs) m ≡ just (k , space cs)
  printKlause-✓ k cs m rewrite sym (spaceKlause k cs) = spaceKlause-✓ k cs m

  intro : List Char → Maybe (List Char)
  intro cs = do
    cs₁ ← known cs (toList "p")
    cs₂ ← known cs₁ (toList "cnf")
    _ , cs₃ ← natural cs₂
    _ , cs₄ ← natural cs₃
    return cs₄

  intro-< : ∀ cs cs₄′ → intro cs ≡ just cs₄′ → length cs₄′ < length cs
  intro-< cs cs₄ p
    with known cs (toList "p") in eq₁
  ... | just cs₁
    with known cs₁ (toList "cnf") in eq₂
  ... | just cs₂
    with natural cs₂ in eq₃
  ... | just (_ , cs₃)
    with natural cs₃ in eq₄
  ... | just (_ , cs₄)
    with p
  ... | refl = begin-strict
    length cs₄ <⟨ natural-< cs₃ _ cs₄ eq₄ ⟩
    length cs₃ <⟨ natural-< cs₂ _ cs₃ eq₃ ⟩
    length cs₂ ≤⟨ known-≤ cs₁ (toList "cnf") cs₂ eq₂ ⟩
    length cs₁ ≤⟨ known-≤ cs (toList "p") cs₁ eq₁ ⟩
    length cs  ∎
    where open ≤-Reasoning

  formula′ : (cs : List Char) → Formula → ℕ → Translator → Measure cs → Maybe (Formula × Translator)
  formula′ []ˡ         f n t _        = return $ f , t
  formula′ ('c' ∷ˡ cs) f n t (acc rs) = do
     let cs′ = line cs
     formula′ cs′ f n t (rs cs′ (≤⇒<-suc (line-≤ cs)))
  formula′ (c ∷ˡ cs) f n t (acc rs) = do
    (k , cs′) , p ← with-≡ (klause (c ∷ˡ cs) (acc rs))
    f′ ← V.insert f k
    let t′ = insertᵐ (suc n) n t
    formula′ cs′ f′ (suc n) t′ (rs cs′ (klause-< (c ∷ˡ cs) k cs′ (acc rs) p ))

  formula : (cs : List Char) → Measure cs → Maybe (Formula × Translator)
  formula ('c' ∷ˡ cs) (acc rs) = do
    let cs′ = line cs
    formula cs′ (rs cs′ (≤⇒<-suc (line-≤ cs)))
  formula cs          (acc rs) = do
    cs′ , p ← with-≡ (intro cs)
    formula′ cs′ nothing zero emptyᵐ (rs cs′ (intro-< cs cs′ p))

  lsb : ℕ → Bool
  lsb x = case x % 2 of λ where
    zero    → false
    (suc _) → true

  shr : ℕ → ℕ
  shr x = x / 2

  bin′ : (n : ℕ) → ℕ → Vec Bool n
  bin′ zero    _ = []ᵛ
  bin′ (suc n) x = lsb x ∷ᵛ bin′ n (shr x)

  bin : (n : ℕ) → ℕ → Vec Bool n
  bin n x = reverse $ bin′ n x

  {-# TERMINATING #-}
  delete : List Char → Translator → Recycler →
    Maybe (List Index × List Char × Translator × Recycler)
  delete cs t r = natural cs >>= λ where
    (zero , cs)       → return $ []ˡ , cs , t , r
    (x₀@(suc _) , cs) → do
      x ← lookupᵐ x₀ t
      let t = deleteᵐ x₀ t
      let r = insertˢ x r
      is , cs , t , r ← delete cs t r
      return $ bin bitsᶜ x ∷ˡ is , cs , t , r

  {-# TERMINATING #-}
  indexList : List Char → Translator → Maybe (List Index × ℕ × List Char)
  indexList cs t = integer cs >>= λ where
    (_     , zero , cs) → return $ []ˡ , zero , cs
    (true  , x₀   , cs) → return $ []ˡ , x₀   , cs
    (false , x₀   , cs) → do
      x ← lookupᵐ x₀ t
      is , x₀ , cs ← indexList cs t
      return $ bin bitsᶜ x ∷ˡ is , x₀ , cs

  -- the |Map| keeps the |is|s ordered by mapped indices; also: we drop empty |is|s
  {-# TERMINATING #-}
  indexLists : List Char → ℕ → Translator → Maybe (Map (List Index) × List Char)
  indexLists cs x t = indexList cs t >>= λ where
    ([]ˡ , zero       , cs) → return $ emptyᵐ , cs
    (is  , zero       , cs) → return $ insertᵐ x is emptyᵐ , cs
    ([]ˡ , x₀@(suc _) , cs) → do
      x ← lookupᵐ x₀ t
      indexLists cs x t
    (is  , x₀@(suc _) , cs) → do
      let insert = insertᵐ x is
      x ← lookupᵐ x₀ t
      mis , cs ← indexLists cs x t
      return $ insert mis , cs

  extend : List Char → ℕ → Translator → Recycler → ℕ →
    Maybe (Clause × List Index × List (List Index) × List Char × Translator × Recycler × ℕ)
  extend cs x₀ t r m = do
    let x , r , m = case headTailˢ r of λ {(just (x , r)) → x , r , m ; nothing → suc m , r , suc m}
    let t = insertᵐ x₀ x t
    k , cs ← klause cs (measure cs)
    is , x₀ , cs ← indexList cs t
    case x₀ of λ where
      zero    → return $ k , is , []ˡ , cs , t , r , m
      (suc _) → do
        x ← lookupᵐ x₀ t
        mis , cs ← indexLists cs x t
        let iss = mapˡ proj₂ $ toListᵐ mis
        return $ k , is , iss , cs , t , r , m

  proof′ : List Char → Translator → Recycler → ℕ → Maybe (Proof × Translator × Recycler × ℕ)

  {-# TERMINATING #-}
  proof″ : List Char → ℕ → Translator → Recycler → ℕ → Maybe (Proof × Translator × Recycler × ℕ)
  proof″ []ˡ         x₀ t r m = nothing
  proof″ ('d' ∷ˡ cs) x₀ t r m = do
    let cs = space cs
    is , cs , t , r ← delete cs t r
    p , t , r ,  m ← proof′ cs t r m
    return $ del is ∷ˡ p , t , r , m
  proof″ cs@(_ ∷ˡ _) x₀ t r m = do
    k , is , iss , cs , t , r , m ← extend cs x₀ t r m
    p , t , r , m ← proof′ cs t r m
    return $ ext k is iss ∷ˡ p , t , r , m

  proof′ []ˡ         t r m = return $ []ˡ , t , r , m
  proof′ cs@(_ ∷ˡ _) t r m = do
    x₀ , cs ← natural cs
    proof″ cs x₀ t r m

  proof : List Char → Translator → Maybe Proof
  proof cs t = do
    _ , _ , m ← initLastᵐ t
    p , _ , _ , _ ← proof′ cs t emptyˢ m
    return p

  parse : String → String → Maybe (Formula × Proof)
  parse f p = do
    f ← return $ toList f
    f , t ← formula f (measure f)
    p ← proof (toList p) t
    return $ f , p
