{-
GOAL: intrinsically contexted and typed

-}

open import Data.String using (String)
import Data.String as String
open import Data.Bool using (if_then_else_)
open import Relation.Nullary using (does)

infixl 20 _◂[_⦂_]
infixl 40 _`∙_

mutual
  data Ctx : Set
  data Type : Ctx → Set
  data Term : ∀ Γ → Type Γ → Set
  normCtx : Ctx → Ctx
  normType : ∀ {Γ} → Type Γ → Type (normCtx Γ)
  normTerm : ∀ {Γ} {t} → Term Γ t → Term (normCtx Γ) (normType t)

  data Ctx where
    ∅ : Ctx
    _◂[_⦂_] : ∀ (Γ : Ctx) → String → Type Γ → Ctx

  -- postulate substType : ∀ {Γ} {x} {t} → Term Γ t → Type (Γ ◂[ x ⦂ t ]) → Type Γ

  data Type where
    `𝒰 : ∀ {Γ} → Type Γ
    `Π : ∀ {Γ} x (t : Type Γ) → Type (Γ ◂[ x ⦂ t ]) → Type Γ
    `substType : ∀ {Γ} x {t} → Term Γ t → Type (Γ ◂[ x ⦂ t ]) → Type Γ
    `term : ∀ {Γ} → Term Γ `𝒰 → Type Γ
    `↑ : ∀ {Γ} {x} {t} → Type Γ → Type (Γ ◂[ x ⦂ t ])

  data Term where
    -- `⇓ : ∀ {Γ} {t} → Term Γ t → Term (normCtx Γ) (normType t)
    `♯ : ∀ {Γ} x {t} → Term (Γ ◂[ x ⦂ t ]) (`↑ t)
    `↑ : ∀ {Γ} {t} {x} {u} → Term Γ t → Term (Γ ◂[ x ⦂ u ]) (`↑ t)
    `λ : ∀ {Γ} x (t : Type Γ) {u : Type (Γ ◂[ x ⦂ t ])} → Term (Γ ◂[ x ⦂ t ]) u → Term Γ (`Π x t u)
    _`∙_ : ∀ {Γ} {x} {t} {u} → Term Γ (`Π x t u) → (a : Term Γ t) → Term Γ (`substType x a u)

  normCtx ∅ = ∅
  normCtx (Γ ◂[ x ⦂ t ]) = normCtx Γ ◂[ x ⦂ normType t ]

  normType `𝒰 = `𝒰
  normType (`Π x t u) = `Π x (normType t) (normType u)
  normType (`substType x a t) = {!   !}
  normType (`term t) = `term (normTerm t)
  normType (`↑ t) = `↑ (normType t)

  -- normTerm (`⇓ t) = `⇓ (normTerm t)
  normTerm (`♯ x) = {!   !} -- `♯ x
  normTerm (`↑ t) = `↑ (normTerm t)
  normTerm (`λ x t b) = `λ x (normType t) (normTerm b)
  normTerm (f `∙ a) = {!   !} -- normTerm f `∙ normTerm a

`id : ∀ {Γ} → Term Γ (`Π "A" `𝒰 (`Π "x" (`term {! `♯ "A"  !}) {!   !}))
`id = {!   !}
