import Data.Nat

module Parser (bitsᵛ : Data.Nat.ℕ) (bitsᶜ : Data.Nat.ℕ) where

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

open import Correct bitsᵛ bitsᶜ using (
    Proof ; Step ; del ; ext ;
    Clause ; Literal ; pos ; neg ;
    Formula ; Trie ; node ; leaf ; Index
  )

open RawMonad (monad {0ℓ})

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
parseIndices (':' ∷ˡ cs) = do
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
parseLiterals (':' ∷ˡ cs) = do
  (l , cs₁) ← parseLiteral cs
  (ls , cs₂) ← parseLiterals cs₁
  return $ l ∷ˡ ls , cs₂
parseLiterals ('.' ∷ˡ cs) = just $ []ˡ , cs
parseLiterals _           = nothing

{-# TERMINATING #-}
parseHints : List Char → Maybe (List (List Index) × List Char)
parseHints []ˡ         = nothing
parseHints ('|' ∷ˡ cs) = do
  (is , cs₁) ← parseIndices cs
  (iss , cs₂) ← parseHints cs₁
  return $ is ∷ˡ iss , cs₂
parseHints ('.' ∷ˡ cs) = just $ []ˡ , cs
parseHints _           = nothing

{-# TERMINATING #-}
parseProof′ : List Char → Maybe (List Step × List Char)
parseProof′ []ˡ          = nothing
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
parseProof′ ('#' ∷ˡ cs)  = just $ []ˡ , cs
parseProof′ _            = nothing

parseProof : String → Maybe (Proof × String)
parseProof s = do
  (ss , cs) ← parseProof′ (toList s)
  return $ ss , fromList cs

parseFormula′ : (n : ℕ) → List Char → Maybe (Bool × Maybe (Trie n) × List Char)
parseFormula′ _       []ˡ          = nothing
parseFormula′ zero    ('C' ∷ˡ cs)  = do
  (ls , cs′) ← parseLiterals cs
  return $ false , just (leaf ls) , cs′
parseFormula′ zero    ('\n' ∷ˡ cs) = parseFormula′ zero cs
parseFormula′ zero    ('#' ∷ˡ cs)  = just $ true , nothing , cs
parseFormula′ zero    _            = nothing
parseFormula′ (suc n) cs           = do
  (false , tˡ , cs₁) ← parseFormula′ n cs
    where (true , tˡ , cs₁) → just $ true , just (node tˡ nothing) , cs₁
  (false , tʳ , cs₂) ← parseFormula′ n cs₁
    where (true , tʳ , cs₂) → just $ true , just (node tˡ tʳ) , cs₂
  return $ false , just (node tˡ tʳ) , cs₂

parseFormula : String → Maybe (Formula × String)
parseFormula s =
  parseFormula′ bitsᶜ (toList s) >>= λ where
    (true , f , cs)         → just $ f , fromList cs
    (false , f , '#' ∷ˡ cs) → just $ f , fromList cs
    (false , f , _)         → nothing
