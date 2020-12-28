import Data.Nat

module Parser where

open Data.Nat using (ℕ ; zero ; suc)

open import Category.Monad using (RawMonad)
open import Data.Bool using (Bool ; true ; false)
open import Data.Char using (Char)
open import Data.List using (List) renaming ([] to []ˡ ; _∷_ to _∷ˡ_)
open import Data.Maybe using (Maybe ; nothing ; just ; map)
open import Data.Maybe.Categorical using (monad)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String using (String ; toList ; fromList)
open import Data.Vec using (Vec) renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_)
open import Function using (_$_)
open import Level using (0ℓ)

open RawMonad (monad {0ℓ})

module _ (bitsᵛ : Data.Nat.ℕ) (bitsᶜ : Data.Nat.ℕ) where
  open import Correct bitsᵛ bitsᶜ using (
      Proof ; Step ; del ; ext ;
      Clause ; Literal ; pos ; neg ;
      Formula ; Trie ; node ; leaf ; Index
    )

  parseBinary : List Char → (n : ℕ) → Maybe (Vec Bool n × List Char)
  parseBinary cs          zero    = just $ []ᵛ , cs
  parseBinary []ˡ         (suc n) = nothing
  parseBinary ('0' ∷ˡ cs) (suc n) = do
    (is , cs′) ← parseBinary cs n
    return $ false ∷ᵛ is , cs′
  parseBinary ('1' ∷ˡ cs) (suc n) = do
    (is , cs′) ← parseBinary cs n
    return $ true ∷ᵛ is , cs′
  parseBinary _           (suc n) = nothing

  {-# TERMINATING #-}
  parseIndices : List Char → Maybe (List Index × List Char)
  parseIndices []ˡ         = nothing
  parseIndices ('I' ∷ˡ cs) = do
    (i , cs₁) ← parseBinary cs bitsᶜ
    (is , cs₂) ← parseIndices cs₁
    return $ i ∷ˡ is , cs₂
  parseIndices ('.' ∷ˡ cs) = just $ []ˡ , cs
  parseIndices _           = nothing

  parseLiteral : List Char → Maybe (Literal × List Char)
  parseLiteral []ˡ         = nothing
  parseLiteral ('+' ∷ˡ cs) = do
    (v , cs₁) ← parseBinary cs bitsᵛ
    return $ pos v , cs₁
  parseLiteral ('-' ∷ˡ cs) = do
    (v , cs₁) ← parseBinary cs bitsᵛ
    return $ neg v , cs₁
  parseLiteral _           = nothing

  {-# TERMINATING #-}
  parseLiterals : List Char → Maybe (List Literal × List Char)
  parseLiterals []ˡ         = nothing
  parseLiterals ('L' ∷ˡ cs) = do
    (l , cs₁) ← parseLiteral cs
    (ls , cs₂) ← parseLiterals cs₁
    return $ l ∷ˡ ls , cs₂
  parseLiterals ('.' ∷ˡ cs) = just $ []ˡ , cs
  parseLiterals _           = nothing

  {-# TERMINATING #-}
  parseHints : List Char → Maybe (List (List Index) × List Char)
  parseHints []ˡ         = nothing
  parseHints ('H' ∷ˡ cs) = do
    (is , cs₁) ← parseIndices cs
    (iss , cs₂) ← parseHints cs₁
    return $ is ∷ˡ iss , cs₂
  parseHints ('.' ∷ˡ cs) = just $ []ˡ , cs
  parseHints _           = nothing

  {-# TERMINATING #-}
  parseProof′ : List Char → Maybe (List Step × List Char)
  parseProof′ []ˡ          = just $ []ˡ , []ˡ
  parseProof′ ('D' ∷ˡ cs)  = do
    (is , cs₁) ← parseIndices cs
    (ss , cs₂) ← parseProof′ cs₁
    return $ del is ∷ˡ ss , cs₂
  parseProof′ ('E' ∷ˡ cs)  = do
    (ls , cs₁) ← parseLiterals cs
    (is , cs₂) ← parseIndices cs₁
    (hs , cs₃) ← parseHints cs₂
    (ss , cs₄) ← parseProof′ cs₃
    return $ ext ls is hs ∷ˡ ss , cs₄
  parseProof′ ('\n' ∷ˡ cs) = parseProof′ cs
  parseProof′ _            = nothing

  parseProof : String → Maybe Proof
  parseProof s = parseProof′ (toList s) >>= λ where
    (p , []ˡ) → just p
    _         → nothing

  parseFormula′ : (n : ℕ) → List Char → Maybe (Maybe (Trie n) × List Char)
  parseFormula′ zero    []ˡ          = just $ nothing , []ˡ
  parseFormula′ zero    ('C' ∷ˡ cs)  = do
    (ls , cs′) ← parseLiterals cs
    return $ just (leaf ls) , cs′
  parseFormula′ zero    ('\n' ∷ˡ cs) = parseFormula′ zero cs
  parseFormula′ zero    _            = nothing
  parseFormula′ (suc n) cs           = do
    (tˡ , cs₁) ← parseFormula′ n cs
    (tʳ , cs₂) ← parseFormula′ n cs₁
    return $ just (node tˡ tʳ) , cs₂

  parseFormula : String → Maybe Formula
  parseFormula s = parseFormula′ bitsᶜ (toList s) >>= λ where
    (f , []ˡ) → just f
    _         → nothing
