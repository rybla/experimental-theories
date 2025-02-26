open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String)
import Data.String as String
open import Data.Bool using (if_then_else_)
open import Relation.Nullary using (does)

infix 10 _⊢_ _≺_
infixl 20 _◂_
infixl 30 _`∙_

data Term : Set where
  `♯ : ℕ → Term
  `λ : Term → Term → Term
  _`∙_ : Term → Term → Term
  `𝒰 : Term
  _`＝_ : Term → Term → Term
  `- : Term

data Ctx : Set where
  ∅ : Ctx
  _◂_ : Ctx → Term → Ctx

data _≺_ : Term → Term → Set where
  ≺♯ : ∀ {n} →
    `♯ n ≺ `♯ n

  ≺λ : ∀ {t t′ u u′} →
    t ≺ t′ → 
    u ≺ u′ →
    `λ t u ≺ `λ t′ u′

  ≺∙ : ∀ {t t′ u u′} →
    t ≺ t′ → 
    u ≺ u′ →
    t `∙ u ≺ t′ `∙ t′

  ≺𝒰 :
    `𝒰 ≺ `𝒰

  ≺＝ : ∀ {t t′ u u′} →
    t ≺ t′ → 
    u ≺ u′ → 
    t `＝ u ≺ t′ `＝ u′

  ≺- : ∀ {t} → 
    `- ≺ t

data _⊢_ : Ctx → Term → Set where
  ⊢λ : ∀ {Γ} {t u} →
    Γ ◂ t ⊢ u →
    Γ ⊢ `λ t u

  -- PROBLEM: can't express a function that's not already a lambda
  ⊢∙ : ∀ {Γ} {t t′ u} →
    Γ ⊢ `λ t′ u →
    Γ ⊢ t →
    t ≺ t′ →
    Γ ⊢ u `∙ t

  ⊢𝒰 : ∀ {Γ} →
    Γ ⊢ `𝒰

  ⊢＝ : ∀ {Γ} {t u} →
    Γ ⊢ t `＝ u

  ⊢- : ∀ {Γ} →
    Γ ⊢ `-

-- let a f = f a
-- let = λ a . λ f . f a

-- PROBLEM: I think actually that you do need to separate apart terms and types, for the sake of type ascription being a construct that can then be leibniz equality-ified into transport
⊢let : ∀ {Γ} {A B} → Γ ⊢ `λ A (`λ (`λ A B) B)
⊢let = ⊢λ (⊢λ {! ? `∙ ?  !})

-- f : Π A B 
-- λ A (f (#0 : A) : B)
