{-
trying to directly solve problem in ex2:
- separate out terms and types again 
- use type ascription as a thing that will eventually be leibniz-ified into transport
-} 
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String)
import Data.String as String
open import Data.Bool using (if_then_else_)
open import Relation.Nullary using (does)

infix 10 _⊢_
infixl 20 _◂_
infixl 30 _`∙_

data Term : Set where
  `♯ : ℕ → Term
  `λ : Term → Term
  `Π : Term → Term → Term
  _`∙_ : Term → Term → Term
  `𝒰 : Term
  _`⦂_ : Term → Term → Term
  _`＝_ : Term → Term → Term

data Ctx : Set where 
  ∅ : Ctx
  _◂_ : Ctx → Term → Ctx

data _⊢_ : Ctx → Term → Set where
  ⊢λ : ∀ {Γ} {t u} → 
    -- PROBLEM: but if u is an ascription (a : A) then this doesn't really make sense
    Γ ◂ t ⊢ u → 
    Γ ⊢ `λ u

  ⊢∙ : ∀ {Γ} {t u} → 
    Γ ⊢ `λ u → 
    Γ ⊢ t → 
    Γ ⊢ u
