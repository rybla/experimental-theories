open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String)
import Data.String as String
open import Data.Bool using (if_then_else_)
open import Relation.Nullary using (does)

infix 10 _⊢_
infixr 20 _◂_
infixl 30 `♯_⦂_
infixl 31 _`∙_

data Term : Set where
  `♯_⦂_ : String → Term → Term
  `λ : Term → Term → Term
  _`∙_ : Term → Term → Term
  `𝒰 : Term
  _`＝_ : Term → Term → Term

data Ctx : Set where
  ∅ : Ctx
  _◂_ : Ctx → Term → Ctx

postulate substTerm : String → Term → Term → Term

data _⊢_ : Ctx → Term → Set where
  -- SOLUTION: don't have lambdas, actually
  -- PROBLEM: what about binders?
  ⊢∙ : ∀ {Γ} {t u} →
    Γ ◂ t ⊢ u → 
    Γ ⊢ t → 
    Γ ⊢ u

  ⊢♯∙ : ∀ {Γ} {x} {t u} →
    Γ ◂ `♯ x ⦂ t ⊢ u →
    Γ ⊢ t → 
    Γ ⊢ substTerm x t u
