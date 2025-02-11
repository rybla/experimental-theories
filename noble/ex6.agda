open import Data.Nat using (ℕ)
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
  -- usual terms
  `♯ : ℕ → Syn
  `λ : Syn → Syn
  _`∙_ : Syn → Syn → Syn
  `Π : Syn → Syn → Syn
  `𝒰 : Syn

  -- data types
  `⊥ : Syn
  `⊤ : Syn
  `it : Syn
  `𝐁 : Syn
  `true : Syn 
  `false : Syn
  `Σ : Syn → Syn → Syn
  _`,_ : Syn → Syn → Syn
  `μ : Syn → Syn

  -- equality
  _`≡_ : Syn → Syn → Syn
  -- equality axioms
  `reflexivity : Syn → Syn → Syn
  `symmetry : Syn → Syn → Syn → Syn → Syn
  `transitivity : Syn → Syn → Syn → Syn → Syn → Syn → Syn
  `congruence : Syn → Syn → Syn → Syn → Syn → Syn → Syn
  `beta : Syn → Syn → Syn → Syn

--------------------------------------------------------------------------------
-- lifted into larger context
--------------------------------------------------------------------------------

`lift : Syn → Syn
`lift (`♯ x) = `♯ (ℕ.suc x)
`lift (`λ b) = `λ (`lift b)
`lift (b `∙ a) = `lift b `∙ `lift a
`lift (`Π a b) = `Π (`lift a) (`lift b)
`lift `𝒰 = `𝒰
`lift `⊥ = `⊥
`lift `⊤ = `⊤
`lift `𝐁 = `𝐁
`lift `true = `true
`lift `false = `false
`lift `it = `it
`lift (`Σ a b) = `Σ (`lift a) (`lift b)
`lift (a `, b) = `lift a `, `lift b
`lift (`μ b) = `μ (`lift b)
`lift (a `≡ b) = `lift a `≡ `lift b
`lift (`reflexivity T a) = `reflexivity (`lift T) (`lift a)
`lift (`symmetry T a b pab) = `symmetry (`lift T) (`lift a) (`lift b) (`lift pab)
`lift (`transitivity T a b c pab pbc) = `transitivity (`lift T) (`lift a) (`lift b) (`lift c) (`lift pab) (`lift pbc)
`lift (`congruence T a b U c pab) = `congruence (`lift T) (`lift a) (`lift b) (`lift U) (`lift c) (`lift pab)
`lift (`beta T a b) = `beta (`lift T) (`lift a) (`lift b)

--------------------------------------------------------------------------------
-- substitution
--------------------------------------------------------------------------------

`substitute : ℕ → Syn → Syn → Syn
`substitute x v (`♯ y) with ℕ.compare x y
`substitute x v (`♯ y) | ℕ.less .x k {- y = suc (x + k) -} = `♯ (x ℕ.+ k)
`substitute x v (`♯ y) | ℕ.equal .x = v
`substitute x v (`♯ y) | ℕ.greater .y k = `♯ y
`substitute n v (`λ b) = `λ (`substitute (ℕ.suc n) (`lift v) b)
`substitute n v (b `∙ a) = `substitute n v b `∙ `substitute n v a
`substitute n v (`Π a b) = `Π (`substitute n v a) (`substitute (ℕ.ℕ.suc n) (`lift v) b)
`substitute n v `𝒰 = `𝒰
`substitute n v `⊥ = `⊥
`substitute n v `⊤ = `⊤
`substitute n v `it = `it
`substitute n v `𝐁 = `𝐁
`substitute n v `true = `true
`substitute n v `false = `false
`substitute n v (`Σ a b) = `Σ (`substitute n v a) (`substitute n v b)
`substitute n v (a `, b) = `substitute n v a `, `substitute n v b
`substitute n v (`μ b) = `μ (`substitute n v b)
`substitute n v (a `≡ b) = `substitute n v a `≡ `substitute n v b
`substitute n v (`reflexivity T a) = `reflexivity (`substitute n v T) (`substitute n v a)
`substitute n v (`symmetry T a b pab) = `symmetry (`substitute n v T) (`substitute n v a) (`substitute n v b) (`substitute n v pab)
`substitute n v (`transitivity T a b c pab pbc) = `transitivity (`substitute n v T) (`substitute n v a) (`substitute n v b) (`substitute n v c) (`substitute n v pab) (`substitute n v pbc)
`substitute n v (`congruence T a b U c pab) = `congruence (`substitute n v T) (`substitute n v a) (`substitute n v b) (`substitute n v U) (`substitute n v c) (`substitute n v pab)
`substitute n v (`beta T a b) = `beta (`substitute n v T) (`substitute n v a) (`substitute (ℕ.suc n) (`lift v) b)

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
    Drv (Γ ⊢ T ⦂ `𝒰) →
    Drv (T ◂ Γ ⊢♯ 0 ⦂ `lift T)

  ⊢♯that : ∀ {Γ} {n} {T U} → 
    Drv (Γ ⊢ U ⦂ `𝒰) →
    Drv (Γ ⊢ T ⦂ `𝒰) →
    Drv (Γ ⊢♯ n ⦂ T) → 
    Drv (U ◂ Γ ⊢♯ (ℕ.suc n) ⦂ `lift T)

  ⊢♯ : ∀ {Γ} {n} {T} →
    Drv (Γ ⊢ T ⦂ `𝒰) → 
    Drv (Γ ⊢♯ n ⦂ T) → 
    Drv (Γ ⊢ `♯ n ⦂ T)

  ⊢lam : ∀ {Γ} {T U b} → 
    Drv (Γ ⊢ T ⦂ `𝒰) →
    Drv (T ◂ Γ ⊢ U ⦂ `𝒰) →
    Drv (T ◂ Γ ⊢ b ⦂ U) → 
    Drv (Γ ⊢ `λ b ⦂ `Π T U)

  ⊢∙ : ∀ {Γ} {T U b a} → 
    Drv (Γ ⊢ T ⦂ `𝒰) →
    Drv (T ◂ Γ ⊢ U ⦂ `𝒰) →
    Drv (Γ ⊢ b ⦂ `Π T U) → 
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (Γ ⊢ b `∙ a ⦂ `substitute 0 T U)

  ⊢pi : ∀ {Γ} {T U} → 
    Drv (Γ ⊢ T ⦂ `𝒰) →
    Drv (T ◂ Γ ⊢ U ⦂ `𝒰) → 
    Drv (Γ ⊢ `Π T U ⦂ `𝒰)

  -- this is inconsistent, but its fine for this toy implementation
  ⊢𝒰 : ∀ {Γ} →
    Drv (Γ ⊢ `𝒰 ⦂ `𝒰)

  ⊢Σ : ∀ {Γ} {T U} → 
    Drv (Γ ⊢ T ⦂ `𝒰) → 
    Drv (T ◂ Γ ⊢ U ⦂ `𝒰) → 
    Drv (Γ ⊢ `Σ T U ⦂ `𝒰)

  ⊢, : ∀ {Γ} {T U a b} → 
    Drv (Γ ⊢ T ⦂ `𝒰) → 
    Drv (T ◂ Γ ⊢ U ⦂ `𝒰) → 
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (T ◂ Γ ⊢ b ⦂ U) → 
    Drv (Γ ⊢ a `, b ⦂ `Σ T U)

  ⊢μ : ∀ {Γ} {T} → 
    Drv (Γ ⊢ T ⦂ `Π `𝒰 `𝒰) →
    Drv (Γ ⊢ `μ T ⦂ `𝒰)

  ⊢≡ : ∀ {Γ} {T a b} →
      Drv (Γ ⊢ T ⦂ `𝒰) → 
      Drv (Γ ⊢ a ⦂ T) → 
      Drv (Γ ⊢ b ⦂ T) → 
      Drv (Γ ⊢ a `≡ b ⦂ `𝒰)

  ⊢transport : ∀ {Γ} {T U p a} → 
    Drv (Γ ⊢ T ⦂ `𝒰) →
    Drv (Γ ⊢ U ⦂ `𝒰) →
    Drv (Γ ⊢ p ⦂ T `≡ U) →
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (Γ ⊢ a ⦂ U)

  ⊢reflexivity : ∀ {Γ} {T a} → 
    Drv (Γ ⊢ T ⦂ `𝒰) →
    Drv (Γ ⊢ `reflexivity T a ⦂ a `≡ a)

  ⊢symmetry : ∀ {Γ} {T a b p} → 
    Drv (Γ ⊢ T ⦂ `𝒰) →
    Drv (Γ ⊢ p ⦂ a `≡ b) →
    Drv (Γ ⊢ `symmetry T a b p ⦂ b `≡ a)

  ⊢transitivity : ∀ {Γ} {T a b c pab pbc} → 
    Drv (Γ ⊢ T ⦂ `𝒰) →
    Drv (Γ ⊢ pab ⦂ a `≡ b) →
    Drv (Γ ⊢ pbc ⦂ b `≡ c) →
    Drv (Γ ⊢ `transitivity T a b c pab pbc ⦂ a `≡ b)

  ⊢congruence : ∀ {Γ} {T a b U c pab} → 
    Drv (Γ ⊢ T ⦂ `𝒰) → 
    Drv (Γ ⊢ a ⦂ T) →
    Drv (Γ ⊢ b ⦂ T) →
    Drv (Γ ⊢ U ⦂ `Π T `𝒰) →
    Drv (Γ ⊢ c ⦂ `Π T (U `∙ `♯ 0)) →
    Drv (Γ ⊢ pab ⦂ a `≡ b) →
    Drv (Γ ⊢ `congruence T a b U c pab ⦂ c `∙ a `≡ c `∙ b)

  ⊢beta : ∀ {Γ} {T a U b} →  
    Drv (Γ ⊢ T ⦂ `𝒰) → 
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (T ◂ Γ ⊢ U ⦂ `𝒰) → 
    Drv (T ◂ Γ ⊢ b ⦂ U) →
    Drv (Γ ⊢ `beta T a b ⦂ `λ b `∙ a `≡ `substitute 0 a b)

-- mutual
--   ♯lift : ∀ {Γ} {T U n} →
--     Drv (Γ ⊢ U ⦂ `𝒰) →
--     Drv (Γ ⊢♯ n ⦂ T) →
--     Drv (U ◂ Γ ⊢♯ ℕ.suc n ⦂ `lift T)
--   ♯lift {Γ = T ◂ Γ} {T′} {U} {0} ⊢U (♯this ⊢T) =
--     ♯that ⊢U (lift ⊢T ⊢T) (♯this ⊢T)
--   ♯lift {Γ = T ◂ Γ} {T′} {U} {n = ℕ.suc n} ⊢U (♯that ⊢T ⊢T′ ⊢[♯n]) = 
--     ♯that ⊢U (lift ⊢T ⊢T′) (♯lift ⊢T ⊢[♯n])

--   postulate
--     lift : ∀ {Γ} {T U a} →
--       Drv (Γ ⊢ U ⦂ `𝒰) →
--       Drv (Γ ⊢ a ⦂ T) →
--       Drv (U ◂ Γ ⊢ `lift a ⦂ `lift T)
--     -- lift {Γ} {T} {U} {a = ♯ n} ⊢U (♯ ⊢T ⊢a) = ♯ (lift ⊢U ⊢T) (⊢♯lift ⊢U ⊢a)
--     -- lift {Γ} {T = `Π V W} {U} {a} ⊢U (lam ⊢V ⊢W ⊢b) = lam (lift ⊢U ⊢V) (lift (lift ⊢U ⊢V) {! ⊢W  !}) {!   !}
--     -- lift {Γ} {T} {U} {a} ⊢U ⊢a = {!   !}

-- `ℕ : Syn
-- `ℕ = mu (`Π 𝒰 {!   !})
-- ⊢Nat : 