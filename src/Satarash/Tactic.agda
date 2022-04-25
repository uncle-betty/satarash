{-# OPTIONS --allow-exec #-}

module Satarash.Tactic where

open import Data.Bool using (Bool ; false ; true ; _∧_ ; _∨_ ; not ; _xor_ ; if_then_else_)
open import Data.Char using (Char)
open import Function using (_∘_ ; _$_ ; _$!_ ; case_of_ ; const)
open import Data.List using (List ; [] ; _∷_ ; [_] ; length ; map ; _++_ ; _∷ʳ_)
open import Data.Maybe using (Maybe ; nothing ; just ; fromMaybe)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _∸_)
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃-syntax)
open import Data.String using (String ; fromList) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality using (
    _≡_ ; refl ; cong ; trans ; _≢_ ; module ≡-Reasoning
  )
open import Reflection using (
    TC ; typeError ; inferType ; quoteTC ; unify ; debugPrint ;
    ErrorPart ; strErr ; termErr ; nameErr
  )
open import Reflection.AST using (
    Term ; def ; con ; lam ; pi ; var ; lit ; nat ; Abs ; abs ; Arg ; arg ;
    arg-info ; visible ; modality ; relevant ; quantity-ω ; Name ;
    showTerm
  )
open import Reflection.External using (CmdSpec ; cmdSpec ; runCmdTC ; StdOut)
open import Reflection.TCM.Syntax using (pure ; _>>=_ ; _>>_ ; _<$>_)

open import Data.Tree.AVL.Map <-strictTotalOrder using (Map ; empty ; insert ; lookup)

open import Satarash.Tseytin using (
    _⇔_ ; _⇒_ ;
    Formula₀ ; con₀ ; var₀ ; and₀ ; or₀ ; not₀ ; xor₀ ; iff₀ ; imp₀ ; ite₀ ; eval₀ ; show₀ ;
    Formula₆ ; transform₆ ; eval₆ ; Formula₇ ; transform₇ ; eval₇ ; transform₇-✓ ;
    maxVar
  )

import Satarash.Parser as P
import Satarash.Tseytin as T
import Satarash.Verifier as V
import Satarash.Word as W

open W using (
    Word ; showᶜ ; showᵇ ; showʷ ;  evalᵇ ; transformᵛ ; transformᵇ ; transformᵇ-✓ ;
    Formulaᵇ ; eqᵇ ; neᵇ ; ltᵇ ; leᵇ ; gtᵇ ; geᵇ ; impᵇ ;
    Formulaʷ ; conʷ ; varʷ ; notʷ ; andʷ ; orʷ ; eorʷ ; negʷ ; addʷ ; subʷ ; mulʷ ; iteʷ ;
    ~ ; _∧ʷ_ ; _∨ʷ_ ; _xorʷ_ ; _⊞_ ; ↕ ; _⊟_  ; _⊠_ ; _≡ʷ_ ; _≢ʷ_ ; _<ʷ_ ; _≤ʷ_ ; _>ʷ_ ; _≥ʷ_ ;
    _<ˡ_ ; _≤ˡ_ ; _>ˡ_ ; _≥ˡ_ ; zeroWord
  )

printParse-✓ : ∀ nᵛ nᶜ f₀ ps f₇ p →
  P.parse (P.printFormula nᵛ nᶜ (transform₆ (not₀ f₀))) ps ≡ just (f₇ , p) →
  transform₇ (not₀ f₀) ≡ just f₇
printParse-✓ nᵛ nᶜ f₀ ps f₇ p p₁ = P.printParse-✓ nᵛ nᶜ (transform₆ (not₀ f₀)) ps f₇ p p₁

postulate
  trust : (f₀ : Formula₀) → ∃[ f₇ ] transform₇ (not₀ f₀) ≡ just f₇ × ∀ v → eval₇ v f₇ ≡ false
  trust′ : (S : Set) → S

runSatarash : (f₀ : Formula₀) →
  TC (∃[ f₇ ] transform₇ (not₀ f₀) ≡ just f₇ × ∀ v → eval₇ v f₇ ≡ false)
runSatarash f₀ = do
    let f₆ = transform₆ (not₀ f₀)
    let nᵛ = maxVar f₆
    let nᶜ = length f₆
    let cs = P.printFormula nᵛ nᶜ f₆

    debugPrint "satarash" 15 (strErr "DIMACS = " ∷ strErr (fromList cs) ∷ [])

    "ok\n" ← runCmdTC (cmdSpec "satarash.sh" [] (fromList cs))
      where out → typeError (strErr "satarash.sh output: " ∷ strErr out ∷ [])

    pure (trust f₀)

not-injective : ∀ {x y} → not x ≡ not y → x ≡ y
not-injective {true}  {true}  refl = refl
not-injective {false} {false} refl = refl

unsat→∀₁ : ∀ f₀ f₇ → transform₇ (not₀ f₀) ≡ just f₇ → (∀ v → eval₇ v f₇ ≡ false) →
  ∀ v → eval₀ v f₀ ≡ true
unsat→∀₁ f₀ f₇ p₁ p₂ v = not-injective $
  begin
    not (eval₀ v f₀)                   ≡˘⟨ transform₇-✓ v (not₀ f₀) f₇ p₁ ⟩
    eval₇ (T.makeTrue₅ v (not₀ f₀)) f₇ ≡⟨ p₂ (T.makeTrue₅ v (not₀ f₀)) ⟩
    false                              ≡⟨⟩
    not true                           ∎
  where open ≡-Reasoning

unsat→∀₂ : ∀ {i} fᵇ f₇ → transform₇ (not₀ (transformᵇ {i} fᵇ)) ≡ just f₇ →
  (∀ v → eval₇ v f₇ ≡ false) → ∀ v → evalᵇ v fᵇ ≡ true
unsat→∀₂ fᵇ f₇ p₁ p₂ v =
  begin
    evalᵇ v fᵇ                           ≡˘⟨ transformᵇ-✓ v fᵇ ⟩
    eval₀ (transformᵛ v) (transformᵇ fᵇ) ≡⟨ unsat→∀₁ (transformᵇ fᵇ) f₇ p₁ p₂ (transformᵛ v) ⟩
    true                                 ∎
  where open ≡-Reasoning

to-⇒ : ∀ {x y} → (x ≡ true → y ≡ true) → (x ⇒ y) ≡ true
to-⇒ {true}  {true}  p = refl
to-⇒ {true}  {false} p = p refl
to-⇒ {false} {true}  p = refl
to-⇒ {false} {false} p = refl

from-⇒ : ∀ {x y} → (x ⇒ y) ≡ true → x ≡ true → y ≡ true
from-⇒ {.true} {true} refl refl = refl

to-⇔ : ∀ {x y} → x ≡ y → (x ⇔ y) ≡ true
to-⇔ {true}  {.true}  refl = refl
to-⇔ {false} {.false} refl = refl

from-⇔ : ∀ {x y} → (x ⇔ y) ≡ true → x ≡ y
from-⇔ {true}  {true}  refl = refl
from-⇔ {false} {false} refl = refl

collectParts : ℕ → Term → List String
collectParts n (pi (arg _ _) (abs _ t)) = ("a" ++ˢ show n) ∷ collectParts (suc n) t
collectParts n _                        = []

makeArgument : Term → Arg Term
makeArgument t = arg (arg-info visible (modality relevant quantity-ω)) t

makeLambdas : List String → Term → Term
makeLambdas []       t = t
makeLambdas (v ∷ vs) t = lam visible (abs v (makeLambdas vs t))

makeVariableMap : ℕ → ℕ → ℕ → Term
makeVariableMap zero     n↑ o = def (quote empty) []
makeVariableMap (suc n↓) n↑ o = def (quote insert) (arg₁ ∷ arg₂ ∷ arg₃ ∷ [])
  where
  arg₁ = makeArgument (lit (nat n↑))
  arg₂ = makeArgument (var (suc n↓ + o) []) -- suc, because of makeAssignment's lambda
  arg₃ = makeArgument (makeVariableMap n↓ (suc n↑) o)

makeAssignment : Term → ℕ → ℕ → Term
makeAssignment ini n o = lam visible (abs "n" (def (quote fromMaybe) (arg₂₁ ∷ arg₂₂ ∷ [])))
  where
  arg₁₁ = makeArgument (var 0 [])
  arg₁₂ = makeArgument (makeVariableMap n zero o)
  arg₂₁ = makeArgument ini
  arg₂₂ = makeArgument (def (quote lookup) (arg₁₁ ∷ arg₁₂ ∷ []))

makeApplication : Term → List String → List String → Term → Term
makeApplication ini vs as ty = (def (quote trust′) (arg₁ ∷ arg₂ ∷ []))
  where
  arg₁ = makeArgument ty
  arg₂ = makeArgument (makeAssignment ini (length vs) (length as))

pattern args₀₁ t₁       =         arg _ t₁                       ∷ []
pattern args₀₂ t₁ t₂    =         arg _ t₁ ∷ arg _ t₂            ∷ []
pattern args₁₁ t₁       =     _ ∷ arg _ t₁                       ∷ []
pattern args₁₂ t₁ t₂    =     _ ∷ arg _ t₁ ∷ arg _ t₂            ∷ []
pattern args₂₂ t₁ t₂    = _ ∷ _ ∷ arg _ t₁ ∷ arg _ t₂            ∷ []
pattern args₂₃ t₁ t₂ t₃ = _ ∷ _ ∷ arg _ t₁ ∷ arg _ t₂ ∷ arg _ t₃ ∷ []

pattern argLitNat n = arg _ (lit (nat n)) ∷ []

module TransBool where
  data RelType : Set where
    rel-≡      : RelType

  showRelType : RelType → String
  showRelType rel-≡ = "rel-≡"

  translateFormula : ℕ → Term → TC Formula₀

  translateFormula₁ : ℕ → (Formula₀ → Formula₀) → Term → TC Formula₀
  translateFormula₁ n c t = do
    f ← translateFormula n t
    pure (c f)

  translateFormula₂ : ℕ → (Formula₀ → Formula₀ → Formula₀) → Term → Term → TC Formula₀
  translateFormula₂ n c t₁ t₂ = do
    f₁ ← translateFormula n t₁
    f₂ ← translateFormula n t₂
    pure (c f₁ f₂)

  translateFormula₃ : ℕ → (Formula₀ → Formula₀ → Formula₀ → Formula₀) → Term → Term → Term →
    TC Formula₀
  translateFormula₃ n c t₁ t₂ t₃ = do
    f₁ ← translateFormula n t₁
    f₂ ← translateFormula n t₂
    f₃ ← translateFormula n t₃
    pure (c f₁ f₂ f₃)

  translateFormula n (con (quote true) _)  = pure (con₀ true)
  translateFormula n (con (quote false) _) = pure (con₀ false)
  translateFormula n (var x _)             = pure (var₀ (n ∸ (suc x)))

  translateFormula n (def (quote _∧_) (args₀₂ t₁ t₂))   = translateFormula₂ n and₀ t₁ t₂
  translateFormula n (def (quote _∨_) (args₀₂ t₁ t₂))   = translateFormula₂ n or₀ t₁ t₂
  translateFormula n (def (quote not) (args₀₁ t))       = translateFormula₁ n not₀ t
  translateFormula n (def (quote _xor_) (args₀₂ t₁ t₂)) = translateFormula₂ n xor₀ t₁ t₂
  translateFormula n (def (quote _⇔_) (args₀₂ t₁ t₂))   = translateFormula₂ n iff₀ t₁ t₂
  translateFormula n (def (quote _⇒_) (args₀₂ t₁ t₂))   = translateFormula₂ n imp₀ t₁ t₂

  translateFormula n (def (quote if_then_else_) (args₂₃ t₁ t₂ t₃)) =
    translateFormula₃ n ite₀ t₁ t₂ t₃

  translateFormula n t = typeError (strErr "bad formula part: " ∷ strErr (showTerm t) ∷ [])

  translatePart : ℕ → Term → TC (RelType × Formula₀)
  translatePart n (def (quote _≡_) (args₂₂ t₁ t₂)) = do
    fˡ ← translateFormula n t₁
    fʳ ← translateFormula n t₂
    pure (rel-≡ , iff₀ fˡ fʳ)

  translatePart n t = typeError (strErr "bad goal part: " ∷ strErr (showTerm t) ∷ [])

  translateParts : ℕ → Term → TC (List RelType × Formula₀)
  translateParts n (pi (arg _ t₁) (abs _ t₂)) = do
    r  , f₁ ← translatePart  n t₁
    rs , f₂ ← translateParts (suc n) t₂
    pure (r ∷ rs , imp₀ f₁ f₂)
  translateParts n t = do
    r , f ← translatePart n t
    pure ([ r ] , f)

  collectVariables : Term → TC (List String × Term)
  collectVariables (pi (arg _ (def (quote Bool) _)) (abs v t)) = do
    vs , t′ ← collectVariables t
    pure (v ∷ vs , t′)
  collectVariables t = pure ([] , t)

  translateGoal : Term → TC (List String × List String × List RelType × Formula₀)
  translateGoal t = do
    vs , t′ ← collectVariables t
    let as = collectParts 1 t′
    rs , f₀ ← (translateParts $! length vs) t′
    pure (vs , as , rs , f₀)

  makeTransformed : List RelType → Term → Term
  makeTransformed []               t = t
  makeTransformed (rel-≡ ∷ [])     t = def (quote from-⇔) (arg₁ ∷ [])
    where
    arg₁ = makeArgument t
  makeTransformed (rel-≡ ∷ r ∷ rs) t = makeTransformed (r ∷ rs) t′
    where
    arg₁₁ = makeArgument (var (length rs) [])
    arg₂₁ = makeArgument t
    arg₂₂ = makeArgument (def (quote to-⇔) (arg₁₁ ∷ []))
    t′ = def (quote from-⇒) (arg₂₁ ∷ arg₂₂ ∷ [])

  makeProof : List String → List String → List RelType → Term → Term
  makeProof vs as rs ty =
    makeLambdas (vs ++ as) transformed
    where
    application = makeApplication (con (quote false) []) vs as ty
    transformed = makeTransformed rs application

module TransWord where
  data RelType : Set where
    rel-≡      : RelType
    rel-≢      : RelType
    rel-<      : RelType
    rel-≤      : RelType
    rel->      : RelType
    rel-≥      : RelType

  showRelType : RelType → String
  showRelType rel-≡ = "rel-≡"
  showRelType rel-≢ = "rel-≢"
  showRelType rel-< = "rel-<"
  showRelType rel-≤ = "rel-≤"
  showRelType rel-> = "rel->"
  showRelType rel-≥ = "rel-≥"

  relTo : RelType → Name
  relTo rel-≡ = quote W.≡ʷ-✓₃
  relTo rel-≢ = quote W.≢ʷ-✓₃
  relTo rel-< = quote W.<ˡ⇒<ʷ₁
  relTo rel-≤ = quote W.≤ˡ⇒≤ʷ₁
  relTo rel-> = quote W.>ˡ⇒>ʷ₁
  relTo rel-≥ = quote W.≥ˡ⇒≥ʷ₁

  relFrom : RelType → Name
  relFrom rel-≡ = quote W.≡ʷ-✓₁
  relFrom rel-≢ = quote W.≢ʷ-✓₁
  relFrom rel-< = quote W.<ʷ⇒<ˡ₁
  relFrom rel-≤ = quote W.≤ʷ⇒≤ˡ₁
  relFrom rel-> = quote W.>ʷ⇒>ˡ₁
  relFrom rel-≥ = quote W.≥ʷ⇒≥ˡ₁

  translateFormulaʷ : (i : ℕ) → ℕ → Term → TC (Formulaʷ i)

  translateFormulaᵇ₂ : (i : ℕ) → ℕ → (Formulaʷ i → Formulaʷ i → Formulaᵇ i) → Term → Term →
    TC (Formulaᵇ i)
  translateFormulaᵇ₂ i n c t₁ t₂ = do
    f₁ ← translateFormulaʷ i n t₁
    f₂ ← translateFormulaʷ i n t₂
    pure (c f₁ f₂)

  translateFormulaᵇ : (i : ℕ) → ℕ → Term → TC (RelType × Formulaᵇ i)
  translateFormulaᵇ i n (def (quote _≡_) (args₂₂ t₁ t₂)) = (rel-≡ ,_)  <$> translateFormulaᵇ₂ i n eqᵇ t₁ t₂
  translateFormulaᵇ i n (def (quote _≢_) (args₂₂ t₁ t₂)) = (rel-≢ ,_)  <$> translateFormulaᵇ₂ i n neᵇ t₁ t₂
  translateFormulaᵇ i n (def (quote _<ˡ_) (args₁₂ t₁ t₂)) = (rel-< ,_) <$> translateFormulaᵇ₂ i n ltᵇ t₁ t₂
  translateFormulaᵇ i n (def (quote _≤ˡ_) (args₁₂ t₁ t₂)) = (rel-≤ ,_) <$> translateFormulaᵇ₂ i n leᵇ t₁ t₂
  translateFormulaᵇ i n (def (quote _>ˡ_) (args₁₂ t₁ t₂)) = (rel-> ,_) <$> translateFormulaᵇ₂ i n gtᵇ t₁ t₂
  translateFormulaᵇ i n (def (quote _≥ˡ_) (args₁₂ t₁ t₂)) = (rel-≥ ,_) <$> translateFormulaᵇ₂ i n geᵇ t₁ t₂

  translateFormulaᵇ i n t = typeError (strErr "bad goal part: " ∷ strErr (showTerm t) ∷ [])

  translateFormulaʷ₁ : (i : ℕ) → ℕ → (Formulaʷ i → Formulaʷ i) → Term → TC (Formulaʷ i)
  translateFormulaʷ₁ i n c t = do
    f ← translateFormulaʷ i n t
    pure (c f)

  translateFormulaʷ₂ : (i : ℕ) → ℕ → (Formulaʷ i → Formulaʷ i → Formulaʷ i) → Term → Term →
    TC (Formulaʷ i)
  translateFormulaʷ₂ i n c t₁ t₂ = do
    f₁ ← translateFormulaʷ i n t₁
    f₂ ← translateFormulaʷ i n t₂
    pure (c f₁ f₂)

  translateFormulaʷ₃ : (i : ℕ) → ℕ → (Formulaᵇ i → Formulaʷ i → Formulaʷ i → Formulaʷ i) → Term →
    Term → Term → TC (Formulaʷ i)
  translateFormulaʷ₃ i n c t₁ t₂ t₃ = do
    _ , f₁ ← translateFormulaᵇ i n t₁
    f₂ ← translateFormulaʷ i n t₂
    f₃ ← translateFormulaʷ i n t₃
    pure (c f₁ f₂ f₃)

  translateFormulaʷ i n (var x _) = pure (varʷ (n ∸ (suc x)))

  translateFormulaʷ i n (def (quote ~) (args₁₁ t))          = translateFormulaʷ₁ i n notʷ t
  translateFormulaʷ i n (def (quote _∧ʷ_) (args₁₂ t₁ t₂))   = translateFormulaʷ₂ i n andʷ t₁ t₂
  translateFormulaʷ i n (def (quote _∨ʷ_) (args₁₂ t₁ t₂))   = translateFormulaʷ₂ i n orʷ t₁ t₂
  translateFormulaʷ i n (def (quote _xorʷ_) (args₁₂ t₁ t₂)) = translateFormulaʷ₂ i n eorʷ t₁ t₂
  translateFormulaʷ i n (def (quote ↕) (args₁₁ t))          = translateFormulaʷ₁ i n negʷ t
  translateFormulaʷ i n (def (quote _⊞_) (args₁₂ t₁ t₂))    = translateFormulaʷ₂ i n addʷ t₁ t₂
  translateFormulaʷ i n (def (quote _⊟_) (args₁₂ t₁ t₂))    = translateFormulaʷ₂ i n subʷ t₁ t₂
  translateFormulaʷ i n (def (quote _⊠_) (args₂₂ t₁ t₂))    = translateFormulaʷ₂ i n mulʷ t₁ t₂

  translateFormulaʷ i n t = typeError (strErr "bad formula part: " ∷ strErr (showTerm t) ∷ [])

  translateParts : (i : ℕ) → ℕ → Term → TC (List RelType × Formulaᵇ i)
  translateParts i n (pi (arg _ t₁) (abs _ t₂)) = do
    r  , f₁ ← translateFormulaᵇ i n t₁
    rs , f₂ ← translateParts i (suc n) t₂
    pure (r ∷ rs , impᵇ f₁ f₂)
  translateParts i n t = do
    r , f ← translateFormulaᵇ i n t
    pure ([ r ] , f)
  collectVariables : Term → TC (List String × Term)
  collectVariables (pi (arg _ (def (quote Word) _)) (abs v t)) = do
    vs , t′ ← collectVariables t
    pure (v ∷ vs , t′)
  collectVariables t = pure ([] , t)

  peekWidth : Term → TC ℕ
  peekWidth (pi (arg _ (def (quote Word) (argLitNat n))) _) = pure n
  peekWidth t = typeError (strErr "bad width: " ∷ strErr (showTerm t) ∷ [])

  translateGoal : Term → TC (∃[ i ] List String × List String × List RelType × Formulaᵇ i)
  translateGoal t = do
    i ← peekWidth t
    vs , t′ ← collectVariables t
    let as = collectParts 1 t′
    rs , fᵇ ← (translateParts i $! length vs) t′
    pure (i , vs , as , rs , fᵇ)

  makeTransformed : List RelType → Term → Term
  makeTransformed []            t = t
  makeTransformed (r ∷ [])      t = def (relFrom r) (arg₁ ∷ [])
    where
    arg₁ = makeArgument t
  makeTransformed (r ∷ r′ ∷ rs) t = makeTransformed (r′ ∷ rs) t′
    where
    arg₁₁ = makeArgument (var (length rs) [])
    arg₂₁ = makeArgument t
    arg₂₂ = makeArgument (def (relTo r) (arg₁₁ ∷ []))
    t′ = def (quote from-⇒) (arg₂₁ ∷ arg₂₂ ∷ [])

  makeProof : List String → List String → List RelType → Term → Term
  makeProof vs as rs ty =
    makeLambdas (vs ++ as) transformed
    where
    application = makeApplication (def (quote zeroWord) []) vs as ty
    transformed = makeTransformed rs application

macro
  bool-∀ : Term → TC ⊤
  bool-∀ hole = do
    goal ← inferType hole

    vs , as , rs , f₀ ← TransBool.translateGoal goal

    debugPrint "satarash" 5 (strErr "vs =" ∷ map (strErr ∘ (" " ++ˢ_)) vs)
    debugPrint "satarash" 5 (strErr "as =" ∷ map (strErr ∘ (" " ++ˢ_)) as)
    debugPrint "satarash" 5 (strErr "rs =" ∷ map (strErr ∘ (" " ++ˢ_) ∘ TransBool.showRelType) rs)
    debugPrint "satarash" 5 (strErr "f₀ = " ∷ strErr (show₀ f₀) ∷ [])

    f₇ , p₁ , p₂ ← runSatarash f₀

    let ∀-proof = unsat→∀₁ f₀ f₇ p₁ p₂

    ∀-proof′ ← quoteTC ∀-proof
    ∀-type   ← inferType ∀-proof′

    -- use identically-typed value that unifies faster
    let proof = TransBool.makeProof vs as rs ∀-type

    debugPrint "satarash" 10 (strErr "proof = " ∷ termErr proof ∷ [])

    unify hole proof

  word-∀ : Term → TC ⊤
  word-∀ hole = do
    goal ← inferType hole

    i , vs , as , rs , fᵇ ← TransWord.translateGoal goal

    debugPrint "satarash" 5 (strErr "i = " ∷ strErr (show i) ∷ [])
    debugPrint "satarash" 5 (strErr "vs =" ∷ map (strErr ∘ (" " ++ˢ_)) vs)
    debugPrint "satarash" 5 (strErr "as =" ∷ map (strErr ∘ (" " ++ˢ_)) as)
    debugPrint "satarash" 5 (strErr "rs =" ∷ map (strErr ∘ (" " ++ˢ_) ∘ TransWord.showRelType) rs)
    debugPrint "satarash" 5 (strErr "fᵇ = " ∷ strErr (showᵇ fᵇ) ∷ [])

    let f₀ = transformᵇ fᵇ

    debugPrint "satarash" 15 (strErr "f₀ = " ∷ strErr (show₀ f₀) ∷ [])

    f₇ , p₁ , p₂ ← runSatarash f₀

    let ∀-proof = unsat→∀₂ fᵇ f₇ p₁ p₂

    ∀-proof′ ← quoteTC ∀-proof
    ∀-type   ← inferType ∀-proof′

    -- use identically-typed value that unifies faster
    let proof = TransWord.makeProof vs as rs ∀-type

    debugPrint "satarash" 10 (strErr "proof = " ∷ termErr proof ∷ [])

    unify hole proof
