{-# OPTIONS --rewriting #-}
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
{-# BUILTIN REWRITE _≡_ #-}
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat as ℕ

--------------------------------------------------------------------------------
-- infix precendences
--------------------------------------------------------------------------------

infix 10 _⊢♯_⦂_ _⊢_⦂_
infix 20 _`≡_
infixr 21 _◂_
infixl 21 _`∙_

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

  -- identity
  _`≡_ : Syn → Syn → Syn
  `refl : Syn
  `sym : Syn → Syn
  `trans : Syn → Syn → Syn
  `cong : Syn → Syn
  `β : Syn
  `η : Syn
  `υ : Syn

`0 = `♯ 0
`1 = `♯ 1
`2 = `♯ 2
`3 = `♯ 3

--------------------------------------------------------------------------------
-- ⊢lifted into larger context
--------------------------------------------------------------------------------

lift : Syn → Syn
lift (`♯ x) = `♯ (ℕ.suc x)
lift (`λ b) = `λ (lift b)
lift (b `∙ a) = lift b `∙ lift a
lift (`Π a b) = `Π (lift a) (lift b)
lift `𝒰 = `𝒰
lift (a `≡ b) = lift a `≡ lift b
lift `refl = `refl
lift (`sym pab) = `sym (lift pab)
lift (`trans pab pbc) = `trans (lift pab) (lift pbc)
lift (`cong p) = `cong (lift p)
lift `β = `β
lift `η = `η
lift `υ = `υ

--------------------------------------------------------------------------------
-- substitution
--------------------------------------------------------------------------------

subst : ℕ → Syn → Syn → Syn
subst x v (`♯ y) with ℕ.compare x y
subst x v (`♯ y)    | ℕ.less .x k {- y = suc (x + k) -} = `♯ (x ℕ.+ k)
subst x v (`♯ y)    | ℕ.equal .x = v
subst x v (`♯ y)    | ℕ.greater .y k = `♯ y
subst n v (`λ b) = `λ (subst (ℕ.suc n) (lift v) b)
subst n v (b `∙ a) = subst n v b `∙ subst n v a
subst n v (`Π a b) = `Π (subst n v a) (subst (ℕ.suc n) (lift v) b)
subst n v `𝒰 = `𝒰
subst n v (a `≡ b) = subst n v a `≡ subst n v b
subst n v `refl = `refl
subst n v (`sym pab) = `sym (subst n v pab)
subst n v (`trans pab pbc) = `trans (subst n v pab) (subst n v pbc)
subst n v (`cong p) = `cong (subst n v p)
subst n v `β = `β
subst n v `η = `η
subst n v `υ = `υ

--------------------------------------------------------------------------------
-- typing derivation
--------------------------------- -----------------------------------------------

data Ctx : Set where
  ∅ : Ctx
  _◂_ : Syn → Ctx → Ctx

data Judgment : Set where
  -- ♯ type judgment
  _⊢♯_⦂_ : Ctx → ℕ → Syn → Judgment
  -- type judgment
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

  -- zero is inconsistent, but its fine for zero toy implementation
  ⊢𝒰 : ∀ {Γ} →
    Drv (Γ ⊢ `𝒰 ⦂ `𝒰)

  -- identity

  ⊢≡ : ∀ {Γ} {a b} →
    Drv (Γ ⊢ a `≡ b ⦂ `𝒰)

  -- identity is an equivalence relation
  
  ⊢refl : ∀ {Γ} {a} → 
    Drv (Γ ⊢ `refl ⦂ a `≡ a)

  ⊢sym : ∀ {Γ} {a b pab} → 
    Drv (Γ ⊢ pab ⦂ a `≡ b) →
    Drv (Γ ⊢ `sym pab ⦂ b `≡ a)

  ⊢trans : ∀ {Γ} {a} b {c pab pbc} → 
    Drv (Γ ⊢ pab ⦂ a `≡ b) →
    Drv (Γ ⊢ pbc ⦂ b `≡ c) →
    Drv (Γ ⊢ `trans pab pbc ⦂ a `≡ c)

  ⊢cong : ∀ {Γ} {a b} c {pab} → 
    Drv (Γ ⊢ pab ⦂ a `≡ b) →
    Drv (Γ ⊢ `cong pab ⦂ c `∙ a `≡ c `∙ b)

  -- extra identities

  ⊢β : ∀ {Γ} {a b} →  
    Drv (Γ ⊢ `β ⦂ `λ b `∙ a `≡ subst 0 a b)

  ⊢η : ∀ {Γ} {b} → 
    Drv (Γ ⊢ `refl ⦂ (`λ (lift b `∙ `♯ 0)) `≡ b)

  ⊢υ : ∀ {Γ} {p a b} →
    Drv (Γ ⊢ p ⦂ a `≡ b) →
    Drv (Γ ⊢ `υ ⦂ p `≡ `refl)

  -- identity supports transport

  ⊢transport : ∀ {Γ} T {U p a} → 
    Drv (Γ ⊢ p ⦂ T `≡ U) →
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (Γ ⊢ a ⦂ U)

postulate
  ⊢lift : ∀ {Γ} {U T a} →
    Drv (Γ ⊢ U ⦂ `𝒰) →
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (U ◂ Γ ⊢ lift a ⦂ lift T)

  ⊢unlift : ∀ {Γ} {U T a} →
    Drv (U ◂ Γ ⊢ lift a ⦂ lift T) →
    Drv (Γ ⊢ a ⦂ T)

  subst-0-lift : ∀ a T →
    subst 0 a (lift T) ≡ T


{-# REWRITE subst-0-lift #-}

--------------------------------------------------------------------------------
-- prelude
--------------------------------------------------------------------------------

-- TODO

--------------------------------------------------------------------------------
-- examples
--------------------------------------------------------------------------------

module tactics where

  open import Reflection
  open import Data.Unit using (⊤; tt)
  open import Data.Bool using (Bool; true; false)
  open import Data.List using (List; []; _∷_; [_])
  open import Data.Product using (_×_; _,_)

  arg′ : ∀ {a} {A : Set a} → A → Arg A
  arg′ = arg (arg-info visible (modality relevant quantity-ω))

  ------------------------------------------------------------------------------

  extract-ℕ : Term → TC ℕ
  extract-ℕ (lit (nat n)) = pure n
  extract-ℕ t = typeError (termErr t ∷ strErr " is not a literal natural number" ∷ [])
    
  ------------------------------------------------------------------------------

  extract-⊢ : Term → TC (Term × Term × Term)
  extract-⊢ (def (quote Drv) (arg _ (con (quote _⊢_⦂_) (arg _ Γ ∷ arg _ n ∷ arg _ T ∷ [])) ∷ [])) = pure (Γ , n , T)
  extract-⊢ t = typeError (termErr t ∷ strErr " is not of the form Drv (Γ ⊢ a ⦂ T)" ∷ [])

  extract-⊢♯ : Term → TC (Term × Term × Term)
  extract-⊢♯ (def (quote Drv) (arg _ (con (quote _⊢♯_⦂_) (arg _ Γ ∷ arg _ n ∷ arg _ T ∷ [])) ∷ [])) = pure (Γ , n , T)
  extract-⊢♯ t = typeError (termErr t ∷ strErr " is not of the form Drv (Γ ⊢♯ n ⦂ T)" ∷ [])

  extract-◂ : Term → TC (Term × Term)
  extract-◂ (con (quote (_◂_)) (arg _ T ∷ arg _ Γ ∷ [])) = pure (T , Γ)
  extract-◂ t = typeError (termErr t ∷ strErr " is not of the form T ◂ Γ" ∷ [])

  $⊢♯-helper : ℕ → TC Term
  $⊢♯-helper ℕ.zero = pure (con (quote ⊢♯zero) [])
  $⊢♯-helper (ℕ.suc n) = do
    drv ← $⊢♯-helper n
    pure (con (quote ⊢♯suc) [ arg′ drv ])

  macro
    $⊢♯ : Term → TC ⊤
    $⊢♯ hole = withNormalisation true do
      goal ← inferType hole
      Γ , n , T ← extract-⊢♯ goal
      n ← extract-ℕ n
      drv ← $⊢♯-helper n
      unify hole drv

    $⊢♯[_] : ℕ → Term → TC ⊤
    $⊢♯[ n ] hole = withNormalisation true do
      goal ← inferType hole
      Γ , _ , T ← extract-⊢♯ goal
      drv ← $⊢♯-helper n
      unify hole drv

  $⊢⦂-helper : Term → Term → Term → TC Term
  $⊢⦂-helper Γ (con (quote `♯) (arg _ n ∷ [])) T = do
    n ← normalise n
    n ← extract-ℕ n
    drv ← $⊢♯-helper n
    pure (con (quote ⊢♯) (arg′ drv ∷ []))
  $⊢⦂-helper Γ a T = typeError (strErr "failed to synthesize typing derivation for " ∷ termErr (con (quote _⊢_⦂_) (arg′ Γ ∷ arg′ a ∷ arg′ T ∷ [])) ∷ [])

  macro
    $⊢⦂ : Term → TC ⊤
    $⊢⦂ hole = withNormalisation true do
      goal ← inferType hole
      Γ , a , T ← extract-⊢ goal
      drv ← $⊢⦂-helper Γ a T
      unify hole drv

    $⊢[_]⦂ : Term → Term → TC ⊤
    $⊢[ a ]⦂ hole = withNormalisation true do
      goal ← inferType hole
      Γ , a′ , T ← extract-⊢ goal
      unify a′ a
      drv ← $⊢⦂-helper Γ a T
      unify hole drv

  ex-♯0 : ∀ {Γ} {T0 T1 T2 T3} → Drv (T0 ◂ T1 ◂ T2 ◂ T3 ◂ Γ ⊢ `♯ 0 ⦂ _)
  ex-♯0 = $⊢⦂

  ex-♯1 : ∀ {Γ} {T0 T1 T2 T3} → Drv (T0 ◂ T1 ◂ T2 ◂ T3 ◂ Γ ⊢ `♯ 1 ⦂ _)
  ex-♯1 = $⊢⦂

  ex-♯2 : ∀ {Γ} {T0 T1 T2 T3} → Drv (T0 ◂ T1 ◂ T2 ◂ T3 ◂ Γ ⊢ `♯ 2 ⦂ _)
  ex-♯2 = $⊢⦂

  ex-♯2′ : ∀ {Γ} {T0 T1 T2 T3} → Drv (T0 ◂ T1 ◂ T2 ◂ T3 ◂ Γ ⊢ `♯ 3 ⦂ _)
  ex-♯2′ = $⊢[ `♯ 3 ]⦂

open tactics using ($⊢⦂; $⊢[_]⦂; $⊢♯; $⊢♯[_])

module `≡-reasoning where
  
  infix  1 begin_ 
  infixl 2 step-`≡-∣ step-`≡-〉
  infix  3 _■

  begin_ : ∀ {Γ} {a b pab} → Drv (Γ ⊢ pab ⦂ a `≡ b) → Drv (Γ ⊢ pab ⦂ a `≡ b)
  begin pab = pab

  step-`≡-∣ : ∀ {Γ} a {b pab} → Drv (Γ ⊢ pab ⦂ a `≡ b) → Drv (Γ ⊢ _ ⦂ a `≡ b)
  step-`≡-∣ _ pab = pab
  
  step-`≡-〉 : ∀ {Γ} a {b c pab pbc} → Drv (Γ ⊢ pab ⦂ a `≡ b) → Drv (Γ ⊢ pbc ⦂ b `≡ c) → Drv (Γ ⊢ _ ⦂ a `≡ c)
  step-`≡-〉 _ pab pbc = ⊢trans _ pab pbc

  syntax step-`≡-∣ a pab      =  a `≡⟨⟩ pab
  syntax step-`≡-〉 a pbc pab  =  a `≡⟨  pab ⟩ pbc

  _■ : ∀ {Γ} a → Drv (Γ ⊢ _ ⦂ a `≡ a)
  _ ■ = ⊢refl

-- open `≡-reasoning

⊢ex0 : ∀ {Γ} {T a} → 
  Drv (Γ ⊢ T ⦂ `𝒰) →
  Drv (Γ ⊢ a ⦂ T) →
  Drv (Γ ⊢ `λ `𝒰 `∙ a ⦂ `𝒰)
⊢ex0 ⊢T ⊢a =
  ⊢∙ (⊢λ ⊢T ⊢𝒰 ⊢𝒰) ⊢a

`id = `λ (`λ `0)
⊢id : ∀ {Γ} → 
  Drv (Γ ⊢ `id ⦂ `Π `𝒰 (`Π `0 (`♯ 1)))
⊢id = 
  ⊢λ ⊢𝒰 (⊢Π $⊢⦂) (⊢λ $⊢⦂ $⊢⦂ $⊢⦂)

⊢ex1 : ∀ {Γ} {T} →
  Drv (Γ ⊢ T ⦂ `𝒰) →
  Drv (Γ ⊢ _ ⦂ `id `∙ `𝒰 `∙ T `≡ T)
⊢ex1 {Γ} {T} ⊢T =
  ⊢trans (                        `id `∙ `𝒰 `∙ T)     ⊢refl (
  ⊢trans ((`λ (`0 `∙ lift T)) `∙ (`id `∙ `𝒰)    )     (⊢sym ⊢β) (
  ⊢trans ((`λ (`0 `∙ lift T)) `∙ (`λ `0)        )      (⊢cong (`λ (`0 `∙ lift T)) ⊢β) (
  ⊢trans (`λ `0 `∙ T)                                  ⊢β (
  ⊢trans T                                             ⊢β (
  ⊢refl)))))
