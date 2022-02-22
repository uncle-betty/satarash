import Data.Nat

module Parser where

open import Category.Monad using (RawMonad)
open import Data.Bool using (Bool ; true ; false)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.List using (List ; length) renaming ([] to []ˡ ; _∷_ to _∷ˡ_ ; map to mapˡ)
open import Data.Maybe using (Maybe ; nothing ; just) renaming (map to mapᵐ)
open import Data.Maybe.Categorical using (monad)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _*_ ; _≤_ ; z≤n ; s≤s ; _<_)
open import Data.Nat.DivMod using (_/_ ; _%_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (
    <-strictTotalOrder ; +-comm ; ≤-refl ; ≤-trans ; n≤1+n ; <-trans ; n<1+n ; module ≤-Reasoning
  )
open import Data.Product using (∃-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ ; map₁ ; map₂)
open import Data.String using (String ; toList ; fromList)
open import Data.Vec using (Vec ; reverse) renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_)
open import Function using (_$_ ; case_of_)
open import Induction.WellFounded using (Acc ; acc)
open import Level using (0ℓ)
open import Relation.Binary.Construct.On using (wellFounded)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; subst)
open import Relation.Nullary using (yes ; no)

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

space : List Char → Maybe (List Char)
space []ˡ       = just []ˡ
space (c ∷ˡ cs) =
  case token c of λ where
    isSpace   → space cs
    isNewLine → space cs
    _         → just (c ∷ˡ cs)

space-≤ : ∀ cs cs′ → space cs ≡ just cs′ → length cs′ ≤ length cs
space-≤ []ˡ       cs′ refl = ≤-refl
space-≤ (c ∷ˡ cs) cs′ p    with token c
space-≤ (c ∷ˡ cs) cs′ p    | isSpace   = ≤-suc (space-≤ cs cs′ p)
space-≤ (c ∷ˡ cs) cs′ p    | isNewLine = ≤-suc (space-≤ cs cs′ p)
space-≤ (c ∷ˡ cs) cs′ refl | isDigit _ = ≤-refl
space-≤ (c ∷ˡ cs) cs′ refl | isMinus   = ≤-refl
space-≤ (c ∷ˡ cs) cs′ refl | isOther   = ≤-refl

line : List Char → Maybe (List Char)
line []ˡ       = just []ˡ
line (c ∷ˡ cs) =
  case token c of λ where
    isNewLine → space cs
    _         → line cs

line-≤ : ∀ cs cs′ → line cs ≡ just cs′ → length cs′ ≤ length cs
line-≤ []ˡ       cs′ refl = ≤-refl
line-≤ (c ∷ˡ cs) cs′ p    with token c
line-≤ (c ∷ˡ cs) cs′ p    | isSpace   = ≤-suc (line-≤ cs cs′ p)
line-≤ (c ∷ˡ cs) cs′ p    | isNewLine = ≤-suc (space-≤ cs cs′ p)
line-≤ (c ∷ˡ cs) cs′ p    | isDigit _ = ≤-suc (line-≤ cs cs′ p)
line-≤ (c ∷ˡ cs) cs′ p    | isMinus   = ≤-suc (line-≤ cs cs′ p)
line-≤ (c ∷ˡ cs) cs′ p    | isOther   = ≤-suc (line-≤ cs cs′ p)

known : List Char → List Char → Maybe (List Char)
known []ˡ       []ˡ       = just []ˡ
known []ˡ       (e ∷ˡ es) = nothing
known (c ∷ˡ cs) []ˡ       =
  case token c of λ where
    isSpace   → space cs
    isNewLine → space cs
    _         → nothing
known (c ∷ˡ cs) (e ∷ˡ es) =
  case c ≟ᶜ e of λ where
    (yes _) → known cs es
    (no  _) → nothing

known-≤ : ∀ cs es cs′ → known cs es ≡ just cs′ → length cs′ ≤ length cs
known-≤ []ˡ       []ˡ       cs′ refl = ≤-refl
known-≤ (c ∷ˡ cs) []ˡ       cs′ p    with token c
known-≤ (c ∷ˡ cs) []ˡ       cs′ p    | isSpace   = ≤-suc (space-≤ cs cs′ p)
known-≤ (c ∷ˡ cs) []ˡ       cs′ p    | isNewLine = ≤-suc (space-≤ cs cs′ p)
known-≤ (c ∷ˡ cs) (e ∷ˡ es) cs′ p    with c ≟ᶜ e
known-≤ (c ∷ˡ cs) (e ∷ˡ es) cs′ p    | yes _ = ≤-suc (known-≤ cs es cs′ p)

natural : List Char → ℕ → Maybe (ℕ × List Char)
natural []ˡ       _ = nothing
natural (c ∷ˡ cs) a =
  case token c of λ where
    isSpace     → mapᵐ (a ,_) (space cs)
    isNewLine   → mapᵐ (a ,_) (space cs)
    (isDigit n) → natural cs (a * 10 + n)
    _           → nothing

natural-< : ∀ cs a r cs′ → natural cs a ≡ just (r , cs′) → length cs′ < length cs
natural-< (c ∷ˡ cs) a r cs′ p    with token c
natural-< (c ∷ˡ cs) a r cs′ p    | isSpace   with space cs in eq
natural-< (c ∷ˡ cs) a r cs′ refl | isSpace   | just cs″ = ≤⇒<-suc (space-≤ cs cs″ eq)
natural-< (c ∷ˡ cs) a r cs′ p    | isNewLine with space cs in eq
natural-< (c ∷ˡ cs) a r cs′ refl | isNewLine | just cs″ = ≤⇒<-suc (space-≤ cs cs″ eq)
natural-< (c ∷ˡ cs) a r cs′ p    | isDigit n = <-suc (natural-< cs (a * 10 + n) r cs′ p)

integer : List Char → Maybe (Bool × ℕ × List Char)
integer []ˡ       = nothing
integer (c ∷ˡ cs) =
  case token c of λ where
    isMinus     → mapᵐ (true ,_) (natural cs 0)
    (isDigit _) → mapᵐ (false ,_) (natural (c ∷ˡ cs) 0)
    _           → nothing

integer-< : ∀ cs s r cs′ → integer cs ≡ just (s , r , cs′) → length cs′ < length cs
integer-< (c ∷ˡ cs) s r cs′ p    with token c
integer-< (c ∷ˡ cs) s r cs′ p    | isMinus   with natural cs 0 in eq
integer-< (c ∷ˡ cs) s r cs′ refl | isMinus   | just (r′ , cs″) = <-suc (natural-< cs 0 r′ cs″ eq)
integer-< (c ∷ˡ cs) s r cs′ p    | isDigit _ with natural (c ∷ˡ cs) 0 in eq
integer-< (c ∷ˡ cs) s r cs′ refl | isDigit _ | just (r′ , cs″) = natural-< (c ∷ˡ cs) 0 r′ cs″ eq

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

  intro : List Char → Maybe (List Char)
  intro cs = do
    cs₁ ← known cs (toList "p")
    cs₂ ← known cs₁ (toList "cnf")
    _ , cs₃ ← natural cs₂ 0
    _ , cs₄ ← natural cs₃ 0
    return cs₄

  intro-< : ∀ cs cs₄′ → intro cs ≡ just cs₄′ → length cs₄′ < length cs
  intro-< cs cs₄ p
    with known cs (toList "p") in eq₁
  ... | just cs₁
    with known cs₁ (toList "cnf") in eq₂
  ... | just cs₂
    with natural cs₂ 0 in eq₃
  ... | just (_ , cs₃)
    with natural cs₃ 0 in eq₄
  ... | just (_ , cs₄)
    with p
  ... | refl = begin-strict
    length cs₄ <⟨ natural-< cs₃ 0 _ cs₄ eq₄ ⟩
    length cs₃ <⟨ natural-< cs₂ 0 _ cs₃ eq₃ ⟩
    length cs₂ ≤⟨ known-≤ cs₁ (toList "cnf") cs₂ eq₂ ⟩
    length cs₁ ≤⟨ known-≤ cs (toList "p") cs₁ eq₁ ⟩
    length cs  ∎
    where open ≤-Reasoning

  formula′ : (cs : List Char) → Formula → ℕ → Translator → Measure cs → Maybe (Formula × Translator)
  formula′ []ˡ         f n t _        = return $ f , t
  formula′ ('c' ∷ˡ cs) f n t (acc rs) = do
     cs′ , p ← with-≡ (line cs)
     formula′ cs′ f n t (rs cs′ (≤⇒<-suc (line-≤ cs cs′ p)))
  formula′ (c ∷ˡ cs) f n t (acc rs) = do
    (k , cs′) , p ← with-≡ (klause (c ∷ˡ cs) (acc rs))
    f′ ← V.insert f k
    let t′ = insertᵐ (suc n) n t
    formula′ cs′ f′ (suc n) t′ (rs cs′ (klause-< (c ∷ˡ cs) k cs′ (acc rs) p ))

  formula : (cs : List Char) → Measure cs → Maybe (Formula × Translator)
  formula ('c' ∷ˡ cs) (acc rs) = do
    cs′ , p ← with-≡ (line cs)
    formula cs′ (rs cs′ (≤⇒<-suc (line-≤ cs cs′ p)))
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
  delete cs t r = natural cs 0 >>= λ where
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
    cs ← space cs
    is , cs , t , r ← delete cs t r
    p , t , r ,  m ← proof′ cs t r m
    return $ del is ∷ˡ p , t , r , m
  proof″ cs@(_ ∷ˡ _) x₀ t r m = do
    k , is , iss , cs , t , r , m ← extend cs x₀ t r m
    p , t , r , m ← proof′ cs t r m
    return $ ext k is iss ∷ˡ p , t , r , m

  proof′ []ˡ         t r m = return $ []ˡ , t , r , m
  proof′ cs@(_ ∷ˡ _) t r m = do
    x₀ , cs ← natural cs 0
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
