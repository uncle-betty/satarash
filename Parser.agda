import Data.Nat

module Parser where

open import Category.Monad using (RawMonad)
open import Data.Bool using (Bool ; true ; false)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.List using (List) renaming ([] to []ˡ ; _∷_ to _∷ˡ_ ; map to mapˡ)
open import Data.Maybe using (Maybe ; nothing ; just) renaming (map to mapᵐ)
open import Data.Maybe.Categorical using (monad)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _*_)
open import Data.Nat.DivMod using (_/_ ; _%_)
open import Data.Nat.Properties using (<-strictTotalOrder ; +-comm)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁ ; map₂)
open import Data.String using (String ; toList ; fromList)
open import Data.Vec using (Vec ; reverse) renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_)
open import Function using (_$_ ; case_of_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; subst)
open import Relation.Nullary using (yes ; no)

open RawMonad (monad {0ℓ})

open import Data.Tree.AVL.Sets <-strictTotalOrder using (
    ⟨Set⟩
  ) renaming (
    empty to emptyˢ ; insert to insertˢ ; headTail to headTailˢ
  )
open import Data.Tree.AVL.Map <-strictTotalOrder using (
    Map
  ) renaming (
    empty to emptyᵐ ; insert to insertᵐ ; lookup to lookupᵐ ; delete to deleteᵐ ;
    initLast to initLastᵐ ; toList to toListᵐ
  )

digit : Char → Maybe ℕ
digit '0' = just 0
digit '1' = just 1
digit '2' = just 2
digit '3' = just 3
digit '4' = just 4
digit '5' = just 5
digit '6' = just 6
digit '7' = just 7
digit '8' = just 8
digit '9' = just 9
digit _   = nothing

space : List Char → Maybe (List Char)
space []ˡ          = just []ˡ
space (' ' ∷ˡ cs)  = space cs
space ('\n' ∷ˡ cs) = space cs
space cs@(_ ∷ˡ _)  = just cs

line : List Char → Maybe (List Char)
line []ˡ          = just []ˡ
line ('\n' ∷ˡ cs) = space cs
line (_ ∷ˡ cs)    = line cs

known : List Char → List Char → Maybe (List Char)
known []ˡ          _   = nothing
known (' ' ∷ˡ cs)  []ˡ = space cs
known ('\n' ∷ˡ cs) []ˡ = space cs
known (_ ∷ˡ _)     []ˡ = nothing
known (c ∷ˡ cs) (e ∷ˡ es)
  with c ≟ᶜ e
... | yes _ = known cs es
... | no  _ = nothing

natural : List Char → ℕ → Maybe (ℕ × List Char)
natural []ˡ          _   = nothing
natural (' ' ∷ˡ cs)  acc = mapᵐ (acc ,_) (space cs)
natural ('\n' ∷ˡ cs) acc = mapᵐ (acc ,_) (space cs)
natural (c ∷ˡ cs)    acc = do
  d ← digit c
  natural cs (10 * acc + d)

integer : List Char → Maybe (Bool × ℕ × List Char)
integer []ˡ         = nothing
integer ('-' ∷ˡ cs) = do
  n ← natural cs 0
  return $ true , n
integer cs@(_ ∷ˡ _) = do
  n ← natural cs 0
  return $ false , n

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

  {-# TERMINATING #-}
  klause : List Char → Maybe (Clause × List Char)
  klause cs = integer cs >>= λ where
    (_     , zero  , cs) → just $ []ˡ , cs
    (false , suc v , cs) → do
      k , cs ← klause cs
      return $ pos v ∷ˡ k , cs
    (true ,  suc v , cs) → do
      k , cs ← klause cs
      return $ neg v ∷ˡ k , cs

  intro : List Char → Maybe (List Char)
  intro cs = do
    cs ← known cs (toList "p")
    cs ← known cs (toList "cnf")
    _ , cs ← natural cs 0
    _ , cs ← natural cs 0
    return cs

  {-# TERMINATING #-}
  formula′ : List Char → Formula → ℕ → Translator → Maybe (Formula × Translator)
  formula′ []ˡ         f n t = return $ f , t
  formula′ ('c' ∷ˡ cs) f n t = do
    cs ← line cs
    formula′ cs f n t
  formula′ cs@(_ ∷ˡ _) f n t = do
    k , cs ← klause cs
    f ← V.insert f k
    let t = insertᵐ (suc n) n t
    formula′ cs f (suc n) t

  {-# TERMINATING #-}
  formula : List Char → Maybe (Formula × Translator)
  formula ('c' ∷ˡ cs) = do
    cs ← line cs
    formula cs
  formula cs          = do
    cs ← intro cs
    formula′ cs nothing zero emptyᵐ

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
    k , cs ← klause cs
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
    f , t ← formula (toList f)
    p ← proof (toList p) t
    return $ f , p
