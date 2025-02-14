open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; compare; less; equal; greater; _+_)

--------------------------------------------------------------------------------
-- infix precendences
--------------------------------------------------------------------------------

infix 10 _⊢♯_⦂_ _⊢_⦂_
infixr 20 _≅_
-- infixr 21 _◂_ _`∙_ _`+_ _`×_ _`,_
infixr 21 _◂_
infixl 21 _`∙_

--------------------------------------------------------------------------------
-- synax
--------------------------------------------------------------------------------

data Syn : Set where
  -- basic
  `♯ : ℕ → Syn
  `λ : Syn → Syn 
  _`∙_ : Syn → Syn → Syn
  `Π : Syn → Syn → Syn
  `𝒰 : Syn

lift : Syn → Syn
lift (`♯ x) = `♯ (suc x)
lift (`λ b) = `λ (lift b)
lift (b `∙ a) = lift b `∙ lift a
lift (`Π A B) = `Π (lift A) (lift B)
lift `𝒰 = `𝒰

subst : ℕ → Syn → Syn → Syn
subst x v (`♯ y) with compare x y
subst x v (`♯ y)    | less .x k {- y = suc (x + k) -} = `♯ (x + k)
subst x v (`♯ y)    | equal .x = v
subst x v (`♯ y)    | greater .y k {- x = suc (y + k) -} = `♯ y
subst x v (`λ b) = `λ (subst (suc x) (lift v) b)
subst x v (b `∙ a) = subst x v b `∙ subst x v a
subst x v (`Π A B) = `Π (subst x v A) (subst x v B)
subst x v `𝒰 = `𝒰

--------------------------------------------------------------------------------
-- typing derivation
--------------------------------------------------------------------------------

data Ctx : Set where 
  ∅ : Ctx 
  _◂_ : Syn → Ctx → Ctx

data Judgment : Set where
  _⊢♯_⦂_ : Ctx → ℕ → Syn → Judgment
  _⊢_⦂_ : Ctx → Syn → Syn → Judgment

data Drv : Judgment → Set where
  
  ⊢♯zero : ∀ {Γ} {T} → 
    Drv (T ◂ Γ ⊢♯ 0 ⦂ lift T)

  ⊢♯suc : ∀ {Γ} {n} {T U} → 
    Drv (Γ ⊢♯ n ⦂ T) → 
    Drv (U ◂ Γ ⊢♯ (ℕ.suc n) ⦂ lift T)

  ⊢♯ : ∀ {Γ} {n} {T} →
    Drv (Γ ⊢♯ n ⦂ T) →
    Drv (Γ ⊢ `♯ n ⦂ T)

  ⊢Π : ∀ {Γ} {T U} → 
    Drv (T ◂ Γ ⊢ U ⦂ `𝒰) →
    Drv (Γ ⊢ `Π T U ⦂ `𝒰)

  ⊢λ : ∀ {Γ} {T U b} →
    Drv (Γ ⊢ T ⦂ `𝒰) →
    Drv (T ◂ Γ ⊢ U ⦂ `𝒰) →
    Drv (T ◂ Γ ⊢ b ⦂ U) → 
    Drv (Γ ⊢ `λ b ⦂ `Π T U)

  ⊢∙ : ∀ {Γ} {T U b a} → 
    Drv (Γ ⊢ b ⦂ `Π T U) →
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (Γ ⊢ b `∙ a ⦂ subst 0 a U)

  ⊢𝒰 : ∀ {Γ} →
    Drv (Γ ⊢ `𝒰 ⦂ `𝒰)

--------------------------------------------------------------------------------
-- tactics
--------------------------------------------------------------------------------

module tactics where
  -- TODO: is normalisation actually necessary in the places suc i commented it out?
  -- or is suc only needed in special circumstances
  -- im not sure how unify applies metavar substsitutions... perhaps in-place??

  open import Reflection
  open import Data.Unit using (⊤; tt)
  open import Data.Bool using (Bool; true; false)
  open import Data.List using (List; []; _∷_; [_])
  open import Data.Product using (_×_; _,_)

  arg′ : ∀ {a} {A : Set a} → A → Arg A
  arg′ = arg (arg-info visible (modality relevant quantity-ω))

  ------------------------------------------------------------------------------

  extract-ℕ : Term → TC ℕ
  extract-ℕ (lit (nat n)) = pure n -- TODO: does zero make sense?
  extract-ℕ t = typeError (termErr t ∷ strErr " is not a literal natural number" ∷ [])
    
  ------------------------------------------------------------------------------

  extract-⊢ : Term → TC (Term × Term × Term)
  extract-⊢ (def (quote Drv) (arg _ (con (quote _⊢_⦂_) (arg _ Γ ∷ arg _ n ∷ arg _ T ∷ [])) ∷ [])) = pure (Γ , n , T)
  extract-⊢ t = typeError (termErr t ∷ strErr " is not of the form Drv (Γ ⊢ a ⦂ T)" ∷ [])

  extract-⊢♯ : Term → TC (Term × Term × Term)
  extract-⊢♯ (def (quote Drv) (arg _ (con (quote _⊢♯_⦂_) (arg _ Γ ∷ arg _ n ∷ arg _ T ∷ [])) ∷ [])) = pure (Γ , n , T)
  extract-⊢♯ t = typeError (termErr t ∷ strErr " is not of the form Drv (Γ ⊢♯ n ⦂ T)" ∷ [])

  -- extract-◂ : Term → TC (Term × Term)
  -- extract-◂ (con (quote (_◂_)) (arg _ T ∷ arg _ Γ ∷ [])) = pure (T , Γ)
  -- extract-◂ t = typeError (termErr t ∷ strErr " is not of the form T ◂ Γ" ∷ [])

  $⊢♯-helper : ℕ → TC Term
  $⊢♯-helper ℕ.zero = pure (con (quote ⊢♯zero) [])
  $⊢♯-helper (ℕ.suc n) = do
    drv ← $⊢♯-helper n
    pure (con (quote ⊢♯suc) [ arg′ drv ])

  macro
    $⊢♯ : Term → TC ⊤
    $⊢♯ hole = withNormalisation true do
      goal ← inferType hole
      -- goal ← normalise goal
      Γ , n , T ← extract-⊢♯ goal
      -- n ← normalise n
      n ← extract-ℕ n
      drv ← $⊢♯-helper n
      unify hole drv

  $⊢-helper : Term → Term → Term → TC Term
  $⊢-helper Γ (con (quote `♯) (arg _ n ∷ [])) T = do
    n ← normalise n
    n ← extract-ℕ n
    drv ← $⊢♯-helper n
    pure (con (quote ⊢♯) (arg′ drv ∷ []))
  $⊢-helper Γ a T = typeError (strErr "failed to synthesize typing derivation for " ∷ termErr (con (quote _⊢_⦂_) (arg′ Γ ∷ arg′ a ∷ arg′ T ∷ [])) ∷ [])

  macro
    $⊢ : Term → TC ⊤
    $⊢ hole = withNormalisation true do
      goal ← inferType hole
      -- goal ← normalise goal
      Γ , a , T ← extract-⊢ goal
      -- a ← normalise a
      drv ← $⊢-helper Γ a T
      unify hole drv

    $⊢′ : Term → Term → TC ⊤
    $⊢′ a′ hole = withNormalisation true do
      goal ← inferType hole
      Γ , a , T ← extract-⊢ goal
      unify a a′
      drv ← $⊢-helper Γ a T
      unify hole drv

  ex-♯0 : ∀ {Γ} {T0 T1 T2 T3} → Drv (T0 ◂ T1 ◂ T2 ◂ T3 ◂ Γ ⊢ `♯ 0 ⦂ _)
  ex-♯0 = $⊢

  ex-♯1 : ∀ {Γ} {T0 T1 T2 T3} → Drv (T0 ◂ T1 ◂ T2 ◂ T3 ◂ Γ ⊢ `♯ 1 ⦂ _)
  ex-♯1 = $⊢

  ex-♯2 : ∀ {Γ} {T0 T1 T2 T3} → Drv (T0 ◂ T1 ◂ T2 ◂ T3 ◂ Γ ⊢ `♯ 2 ⦂ _)
  ex-♯2 = $⊢

open tactics using ($⊢; $⊢♯)

drv0 : ∀ {Γ} {T a} → 
  Drv (Γ ⊢ T ⦂ `𝒰) → 
  Drv (Γ ⊢ a ⦂ T) → 
  Drv (Γ ⊢ `λ `𝒰 `∙ a ⦂ `𝒰)
drv0 ⊢T ⊢a = ⊢∙ (⊢λ ⊢T ⊢𝒰 ⊢𝒰) ⊢a
