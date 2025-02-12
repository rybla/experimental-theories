open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat as ℕ

--------------------------------------------------------------------------------
-- infix precendences
--------------------------------------------------------------------------------

infix 10 _⊢♯_⦂_ _⊢_⦂_
infixr 20 _`≡_
infixr 21 _◂_ _`∙_ _`+_ _`×_ _`,_

--------------------------------------------------------------------------------
-- syntax
--------------------------------------------------------------------------------

data Syn : Set where
  -- basic
  `♯ : ℕ → Syn
  `λ : Syn → Syn
  _`∙_ : Syn → Syn → Syn
  `Π : Syn → Syn → Syn
  `𝒰 : Syn

  -- equality
  _`≡_ : Syn → Syn → Syn
  `reflexivity : Syn → Syn
  `symmetry : Syn → Syn → Syn → Syn
  `transitivity : Syn → Syn → Syn → Syn → Syn → Syn
  `congruence : Syn → Syn → Syn → Syn → Syn → Syn
  `beta : Syn → Syn → Syn

--------------------------------------------------------------------------------
-- ⊢lifted into larger context
--------------------------------------------------------------------------------

lift : Syn → Syn
lift (`♯ x) = `♯ (ℕ.suc x)
lift (`λ b) = `λ (lift b)
lift (b `∙ a) = lift b `∙ lift a
lift (`Π a b) = `Π (lift a) (lift b)
lift (a `≡ b) = lift a `≡ lift b
lift (`reflexivity a) = `reflexivity (lift a)
lift (`symmetry a b pab) = `symmetry (lift a) (lift b) (lift pab)
lift (`transitivity a b c pab pbc) = `transitivity (lift a) (lift b) (lift c) (lift pab) (lift pbc)
lift (`congruence a b U c pab) = `congruence (lift a) (lift b) (lift U) (lift c) (lift pab)
lift (`beta a b) = `beta (lift a) (lift b)
lift a = a

--------------------------------------------------------------------------------
-- substitution
--------------------------------------------------------------------------------

subst : ℕ → Syn → Syn → Syn
subst x v (`♯ y) with ℕ.compare x y
subst x v (`♯ y) | ℕ.less .x k {- y = suc (x + k) -} = `♯ (x ℕ.+ k)
subst x v (`♯ y) | ℕ.equal .x = v
subst x v (`♯ y) | ℕ.greater .y k = `♯ y
subst n v (`λ b) = `λ (subst (ℕ.suc n) (lift v) b)
subst n v (b `∙ a) = subst n v b `∙ subst n v a
subst n v (`Π a b) = `Π (subst n v a) (subst (ℕ.suc n) (lift v) b)
subst n v (a `≡ b) = subst n v a `≡ subst n v b
subst n v (`reflexivity a) = `reflexivity (subst n v a)
subst n v (`symmetry a b pab) = `symmetry (subst n v a) (subst n v b) (subst n v pab)
subst n v (`transitivity a b c pab pbc) = `transitivity (subst n v a) (subst n v b) (subst n v c) (subst n v pab) (subst n v pbc)
subst n v (`congruence a b U c pab) = `congruence (subst n v a) (subst n v b) (subst n v U) (subst n v c) (subst n v pab)
subst n v (`beta a b) = `beta (subst n v a) (subst (ℕ.suc n) (lift v) b)
subst _ _ a = a

--------------------------------------------------------------------------------
-- typing derivation
--------------------------------- -----------------------------------------------

data Ctx : Set where
  ∅ : Ctx
  _◂_ : Syn → Ctx → Ctx

data Judgment : Set where
  -- ♯ type judgement
  _⊢♯_⦂_ : Ctx → ℕ → Syn → Judgment
  -- type judgement
  _⊢_⦂_ : Ctx → Syn → Syn → Judgment

data Drv : Judgment → Set where

  ⊢♯this : ∀ {Γ} {T} → 
    Drv (T ◂ Γ ⊢♯ 0 ⦂ lift T)

  ⊢♯that : ∀ {Γ} {n} {T U} → 
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
    Drv (Γ ⊢ b ⦂ `Π T (U `∙ (`♯ 0))) → 
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (Γ ⊢ b `∙ a ⦂ U `∙ a)

  -- this is inconsistent, but its fine for this toy implementation
  ⊢𝒰 : ∀ {Γ} →
    Drv (Γ ⊢ `𝒰 ⦂ `𝒰)

  -- equality stuff

  ⊢≡ : ∀ {Γ} {T a b} →
      Drv (Γ ⊢ a ⦂ T) → 
      Drv (Γ ⊢ b ⦂ T) → 
      Drv (Γ ⊢ a `≡ b ⦂ `𝒰)

  ⊢transport : ∀ {Γ} {T U p a} → 
    Drv (Γ ⊢ p ⦂ T `≡ U) →
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (Γ ⊢ a ⦂ U)

  ⊢reflexivity : ∀ {Γ} {a} → 
    Drv (Γ ⊢ `reflexivity a ⦂ a `≡ a)

  ⊢symmetry : ∀ {Γ} {a b p} → 
    Drv (Γ ⊢ p ⦂ a `≡ b) →
    Drv (Γ ⊢ `symmetry a b p ⦂ b `≡ a)

  ⊢transitivity : ∀ {Γ} {a b c pab pbc} → 
    Drv (Γ ⊢ pab ⦂ a `≡ b) →
    Drv (Γ ⊢ pbc ⦂ b `≡ c) →
    Drv (Γ ⊢ `transitivity a b c pab pbc ⦂ a `≡ b)

  ⊢congruence : ∀ {Γ} {a b U c pab} → 
    Drv (Γ ⊢ pab ⦂ a `≡ b) →
    Drv (Γ ⊢ `congruence a b U c pab ⦂ c `∙ a `≡ c `∙ b)

  ⊢beta : ∀ {Γ} {a b} →  
    Drv (Γ ⊢ `beta a b ⦂ `λ b `∙ a `≡ subst 0 a b)

--------------------------------------------------------------------------------
-- prelude
--------------------------------------------------------------------------------

-- TODO

--------------------------------------------------------------------------------
-- examples
--------------------------------------------------------------------------------

