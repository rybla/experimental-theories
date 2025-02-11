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
  `𝔹 : Syn
  `true : Syn 
  `false : Syn
  `elim-𝔹 : Syn → Syn → Syn → Syn
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
-- ⊢lifted into larger context
--------------------------------------------------------------------------------

lift : Syn → Syn
lift (`♯ x) = `♯ (ℕ.suc x)
lift (`λ b) = `λ (lift b)
lift (b `∙ a) = lift b `∙ lift a
lift (`Π a b) = `Π (lift a) (lift b)
lift `𝒰 = `𝒰
lift `⊥ = `⊥
lift `⊤ = `⊤
lift `𝔹 = `𝔹
lift (`elim-𝔹 a b c) = `elim-𝔹 (lift a) (lift b) (lift c)
lift `true = `true
lift `false = `false
lift `it = `it
lift (`Σ a b) = `Σ (lift a) (lift b)
lift (a `, b) = lift a `, lift b
lift (`μ b) = `μ (lift b)
lift (a `≡ b) = lift a `≡ lift b
lift (`reflexivity T a) = `reflexivity (lift T) (lift a)
lift (`symmetry T a b pab) = `symmetry (lift T) (lift a) (lift b) (lift pab)
lift (`transitivity T a b c pab pbc) = `transitivity (lift T) (lift a) (lift b) (lift c) (lift pab) (lift pbc)
lift (`congruence T a b U c pab) = `congruence (lift T) (lift a) (lift b) (lift U) (lift c) (lift pab)
lift (`beta T a b) = `beta (lift T) (lift a) (lift b)

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
subst n v (`Π a b) = `Π (subst n v a) (subst (ℕ.ℕ.suc n) (lift v) b)
subst n v `𝒰 = `𝒰
subst n v `⊥ = `⊥
subst n v `⊤ = `⊤
subst n v `it = `it
subst n v `𝔹 = `𝔹
subst n v `true = `true
subst n v `false = `false
subst n v (`elim-𝔹 a b c) = `elim-𝔹 (subst n v a) (subst n v b) (subst n v c)
subst n v (`Σ a b) = `Σ (subst n v a) (subst n v b)
subst n v (a `, b) = subst n v a `, subst n v b
subst n v (`μ b) = `μ (subst n v b)
subst n v (a `≡ b) = subst n v a `≡ subst n v b
subst n v (`reflexivity T a) = `reflexivity (subst n v T) (subst n v a)
subst n v (`symmetry T a b pab) = `symmetry (subst n v T) (subst n v a) (subst n v b) (subst n v pab)
subst n v (`transitivity T a b c pab pbc) = `transitivity (subst n v T) (subst n v a) (subst n v b) (subst n v c) (subst n v pab) (subst n v pbc)
subst n v (`congruence T a b U c pab) = `congruence (subst n v T) (subst n v a) (subst n v b) (subst n v U) (subst n v c) (subst n v pab)
subst n v (`beta T a b) = `beta (subst n v T) (subst n v a) (subst (ℕ.suc n) (lift v) b)

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
    Drv (T ◂ Γ ⊢♯ 0 ⦂ lift T)

  ⊢♯that : ∀ {Γ} {n} {T U} → 
    Drv (Γ ⊢ U ⦂ `𝒰) →
    Drv (Γ ⊢ T ⦂ `𝒰) →
    Drv (Γ ⊢♯ n ⦂ T) → 
    Drv (U ◂ Γ ⊢♯ (ℕ.suc n) ⦂ lift T)

  ⊢♯ : ∀ {Γ} {n} {T} →
    Drv (Γ ⊢ T ⦂ `𝒰) → 
    Drv (Γ ⊢♯ n ⦂ T) → 
    Drv (Γ ⊢ `♯ n ⦂ T)

  ⊢Π : ∀ {Γ} {T U} → 
    Drv (Γ ⊢ T ⦂ `𝒰) →
    Drv (T ◂ Γ ⊢ U ⦂ `𝒰) → 
    Drv (Γ ⊢ `Π T U ⦂ `𝒰)

  ⊢λ : ∀ {Γ} {T U b} → 
    Drv (Γ ⊢ T ⦂ `𝒰) →
    Drv (T ◂ Γ ⊢ U ⦂ `𝒰) →
    Drv (T ◂ Γ ⊢ b ⦂ U) → 
    Drv (Γ ⊢ `λ b ⦂ `Π T U)

  ⊢∙ : ∀ {Γ} {T U b a} → 
    Drv (Γ ⊢ T ⦂ `𝒰) →
    Drv (Γ ⊢ U ⦂ `Π T `𝒰) →
    Drv (Γ ⊢ b ⦂ `Π T U) → 
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (Γ ⊢ b `∙ a ⦂ T `∙ U)

  -- this is inconsistent, but its fine for this toy implementation
  ⊢𝒰 : ∀ {Γ} →
    Drv (Γ ⊢ `𝒰 ⦂ `𝒰)

  -- datatype stuff

  ⊢⊥ : ∀ {Γ} → 
    Drv (Γ ⊢ `⊥ ⦂ `𝒰)
  
  ⊢⊤ : ∀ {Γ} → 
    Drv (Γ ⊢ `⊤ ⦂ `𝒰)
  
  ⊢it : ∀ {Γ} → 
    Drv (Γ ⊢ `it ⦂ `⊤)

  ⊢𝔹 : ∀ {Γ} → 
    Drv (Γ ⊢ `𝔹 ⦂ `𝒰)
  
  ⊢true : ∀ {Γ} → 
    Drv (Γ ⊢ `true ⦂ `𝔹)
  
  ⊢false : ∀ {Γ} → 
    Drv (Γ ⊢ `false ⦂ `𝔹)
  
  ⊢elim-𝔹 : ∀ {Γ} {T a b c} →
    Drv (Γ ⊢ T ⦂ `Π `𝔹 `𝒰) →
    Drv (Γ ⊢ a ⦂ `Π (c `≡ `true)  (T `∙ `true)) →
    Drv (Γ ⊢ b ⦂ `Π (c `≡ `false) (T `∙ `false)) →
    Drv (Γ ⊢ c ⦂ `𝔹) →
    Drv (Γ ⊢ `elim-𝔹 a b c ⦂ T `∙ c)

  ⊢Σ : ∀ {Γ} {T U} → 
    Drv (Γ ⊢ T ⦂ `𝒰) → 
    Drv (Γ ⊢ U ⦂ `Π T `𝒰) → 
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

  -- equality stuff

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
    Drv (Γ ⊢ `beta T a b ⦂ `λ b `∙ a `≡ subst 0 a b)

{-
mutual
  ⊢♯lift : ∀ {Γ} {T U n} →
    Drv (Γ ⊢ U ⦂ `𝒰) →
    Drv (Γ ⊢♯ n ⦂ T) →
    Drv (U ◂ Γ ⊢♯ ℕ.suc n ⦂ lift T)
  ⊢♯lift {Γ = T ◂ Γ} {T′} {U} {0} ⊢U (♯this ⊢T) =
    ♯that ⊢U (⊢lift ⊢T ⊢T) (♯this ⊢T)
  ⊢♯lift {Γ = T ◂ Γ} {T′} {U} {n = ℕ.suc n} ⊢U (♯that ⊢T ⊢T′ ⊢[♯n]) = 
    ♯that ⊢U (⊢lift ⊢T ⊢T′) (⊢♯lift ⊢T ⊢[♯n])

  postulate
    ⊢lift : ∀ {Γ} {T U a} →
      Drv (Γ ⊢ U ⦂ `𝒰) →
      Drv (Γ ⊢ a ⦂ T) →
      Drv (U ◂ Γ ⊢ lift a ⦂ lift T)
    -- ⊢lift {Γ} {T} {U} {a = ♯ n} ⊢U (♯ ⊢T ⊢a) = ♯ (⊢lift ⊢U ⊢T) (⊢⊢♯lift ⊢U ⊢a)
    -- ⊢lift {Γ} {T} {U} {a} ⊢U ⊢a = {!   !}
-}

-- TODO: seems a little bit suspect that I'm using lift in these definitions
-- since that means that im basically defining a metaprogram that generates types 
-- rather than a function over types (since lift is a metaprogram)

-- non-dependent product type is built from dependent product type
_`×_ : Syn → Syn → Syn
T `× U = `Π `𝔹 (`λ (`elim-𝔹 (`λ (lift T)) (`λ (lift U)) (`♯ 0)))

-- non-dependent sum type is build from dependent sum type
_`+_ : Syn → Syn → Syn
T `+ U = `Σ `𝔹 (`λ (`elim-𝔹 (`λ (lift T)) (`λ (lift U)) (`♯ 0)))

`ℕ : Syn
`ℕ = `μ (`λ (`⊤ `+ `♯ 0))

postulate
  `lemma1 : Syn → Syn
  lemma1 : ∀ {Γ} {b a : Syn} → Drv (Γ ⊢ `lemma1 b ⦂ (`λ b) `∙ a `≡ b)

⊢Nat : ∀ {Γ} → Drv (Γ ⊢ `ℕ ⦂ `𝒰)
⊢Nat = 
  (⊢μ (⊢λ ⊢𝒰 ⊢𝒰 (⊢Σ ⊢𝔹 (⊢λ ⊢𝔹 ⊢𝒰 
    -- (⊢transport {!   !} {!   !} {!   !} 
    --   (⊢elim-𝔹 {!   !} {!   !} {!   !} {!   !}))))))
    -- GOAL: Drv (`𝔹 ◂ `𝒰 ◂ Γ ⊢ `elim-𝔹 `⊤ (`♯ 1) (`♯ 0) ⦂ `𝒰)
    --   - to use ⊢elim-𝔹, i need to convert the goal type from `𝒰 to T `∙ (`♯ 0) for some T
    --   - i dont care about the arg, to T = `λ `𝒰
    --   - in other words, i need to transport along `𝒰 `≡ (`λ `𝒰) `∙ (`♯ 0)
    (⊢transport {T = (`λ `𝒰) `∙ (`♯ 0)} {U = `𝒰} {!   !} {!   !} {!   !} 
      (⊢elim-𝔹 
        (⊢λ ⊢𝔹 ⊢𝒰 ⊢𝒰)
        (⊢λ (⊢≡ ⊢𝔹 (⊢♯ ⊢𝔹 (⊢♯this ⊢𝔹)) ⊢true) 
          -- convert goal to `λ `𝒰 `∙ `true ⦂ `λ `𝒰 `∙ `true
          -- via `λ `𝒰 `∙ `true `≡ `𝒰
          (⊢transport {!   !} {!   !} (lemma1 {a = `true})
            -- (⊢∙ ⊢𝔹 {!   !} 
            --   (⊢λ ⊢𝔹 {!   !} ⊢𝒰)
            --   ⊢true)
            (⊢∙ {!   !} {!   !} {!   !} {!   !}))
          {!   !})
        {!   !}
        {!   !}))))))
