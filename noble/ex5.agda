open import Data.Nat

--------------------------------------------------------------------------------
-- infix precendences
--------------------------------------------------------------------------------

infix 10 _⊢var_⦂_
infix 10 _⊢_⦂_
infixr 20 _≡_
infixr 21 _,_
infixl 21 _∙_

--------------------------------------------------------------------------------
-- syntax
--------------------------------------------------------------------------------

data Syn : Set where
  var : ℕ → Syn
  lam : Syn → Syn
  _∙_ : Syn → Syn → Syn
  pi : Syn → Syn → Syn
  uni : Syn

  -- equality
  _≡_ : Syn → Syn → Syn
  -- equality axioms
  reflexivity : Syn → Syn → Syn
  symmetry : Syn → Syn → Syn → Syn → Syn
  transitivity : Syn → Syn → Syn → Syn → Syn → Syn → Syn
  congruence : Syn → Syn → Syn → Syn → Syn → Syn → Syn
  beta : Syn → Syn → Syn → Syn

--------------------------------------------------------------------------------
-- lifted into larger context
--------------------------------------------------------------------------------

lift : Syn → Syn
lift (var x) = var (suc x)
lift (lam b) = lam (lift b)
lift (b ∙ a) = lift b ∙ lift a
lift (pi a b) = pi (lift a) (lift b)
lift uni = uni
lift (a ≡ b) = lift a ≡ lift b
lift (reflexivity T a) = reflexivity (lift T) (lift a)
lift (symmetry T a b pab) = symmetry (lift T) (lift a) (lift b) (lift pab)
lift (transitivity T a b c pab pbc) = transitivity (lift T) (lift a) (lift b) (lift c) (lift pab) (lift pbc)
lift (congruence T a b U c pab) = congruence (lift T) (lift a) (lift b) (lift U) (lift c) (lift pab)
lift (beta T a b) = beta (lift T) (lift a) (lift b)

--------------------------------------------------------------------------------
-- substitution
--------------------------------------------------------------------------------

substitute : ℕ → Syn → Syn → Syn
substitute x v (var y) with compare x y
substitute x v (var y) | less .x k {- y = suc (x + k) -} = var (x + k)
substitute x v (var y) | equal .x = v
substitute x v (var y) | greater .y k = var y
substitute n v (lam b) = lam (substitute (suc n) (lift v) b)
substitute n v (b ∙ a) = substitute n v b ∙ substitute n v a
substitute n v (pi a b) = pi (substitute n v a) (substitute (suc n) (lift v) b)
substitute n v uni = uni
substitute n v (a ≡ b) = substitute n v a ≡ substitute n v b
substitute n v (reflexivity T a) = reflexivity (substitute n v T) (substitute n v a)
substitute n v (symmetry T a b pab) = symmetry (substitute n v T) (substitute n v a) (substitute n v b) (substitute n v pab)
substitute n v (transitivity T a b c pab pbc) = transitivity (substitute n v T) (substitute n v a) (substitute n v b) (substitute n v c) (substitute n v pab) (substitute n v pbc)
substitute n v (congruence T a b U c pab) = congruence (substitute n v T) (substitute n v a) (substitute n v b) (substitute n v U) (substitute n v c) (substitute n v pab)
substitute n v (beta T a b) = beta (substitute n v T) (substitute n v a) (substitute (suc n) (lift v) b)

--------------------------------------------------------------------------------
-- typing derivation
--------------------------------- -----------------------------------------------

data Ctx : Set where
  ∅ : Ctx
  _,_ : Syn → Ctx → Ctx

data Judgment : Set where
  -- var type judgement
  _⊢var_⦂_ : Ctx → ℕ → Syn → Judgment
  -- type judgement
  _⊢_⦂_ : Ctx → Syn → Syn → Judgment

data Drv : Judgment → Set where

  ⊢var-this : ∀ {Γ} {T} → 
    Drv (Γ ⊢ T ⦂ uni) →
    Drv (T , Γ ⊢var 0 ⦂ lift T)

  ⊢var-that : ∀ {Γ} {n} {T U} → 
    Drv (Γ ⊢ U ⦂ uni) →
    Drv (Γ ⊢ T ⦂ uni) →
    Drv (Γ ⊢var n ⦂ T) → 
    Drv (U , Γ ⊢var (suc n) ⦂ lift T)

  ⊢-var : ∀ {Γ} {n} {T} →
    Drv (Γ ⊢ T ⦂ uni) → 
    Drv (Γ ⊢var n ⦂ T) → 
    Drv (Γ ⊢ var n ⦂ T)

  ⊢-lam : ∀ {Γ} {T U b} → 
    Drv (Γ ⊢ T ⦂ uni) →
    Drv (T , Γ ⊢ U ⦂ uni) →
    Drv (T , Γ ⊢ b ⦂ U) → 
    Drv (Γ ⊢ lam b ⦂ pi T U)

  ⊢-∙ : ∀ {Γ} {T U b a} → 
    Drv (Γ ⊢ T ⦂ uni) →
    Drv (T , Γ ⊢ U ⦂ uni) →
    Drv (Γ ⊢ b ⦂ pi T U) → 
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (Γ ⊢ b ∙ a ⦂ substitute 0 T U)

  ⊢-pi : ∀ {Γ} {T U} → 
    Drv (Γ ⊢ T ⦂ uni) →
    Drv (T , Γ ⊢ U ⦂ uni) → 
    Drv (Γ ⊢ pi T U ⦂ uni)

  -- this is inconsistent, but its fine for this toy implementation
  ⊢-uni : ∀ {Γ} →
    Drv (Γ ⊢ uni ⦂ uni)

  ⊢-equal : ∀ {Γ} {T a b} →
      Drv (Γ ⊢ T ⦂ uni) → 
      Drv (Γ ⊢ a ⦂ T) → 
      Drv (Γ ⊢ b ⦂ T) → 
      Drv (Γ ⊢ a ≡ b ⦂ uni)

  ⊢-transport : ∀ {Γ} {T U p a} → 
    Drv (Γ ⊢ T ⦂ uni) →
    Drv (Γ ⊢ U ⦂ uni) →
    Drv (Γ ⊢ p ⦂ T ≡ U) →
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (Γ ⊢ a ⦂ U)

  ≡-reflexivity : ∀ {Γ} {T a} → 
    Drv (Γ ⊢ T ⦂ uni) →
    Drv (Γ ⊢ reflexivity T a ⦂ a ≡ a)

  ≡-symmetry : ∀ {Γ} {T a b p} → 
    Drv (Γ ⊢ T ⦂ uni) →
    Drv (Γ ⊢ p ⦂ a ≡ b) →
    Drv (Γ ⊢ symmetry T a b p ⦂ b ≡ a)

  ≡-transitivity : ∀ {Γ} {T a b c pab pbc} → 
    Drv (Γ ⊢ T ⦂ uni) →
    Drv (Γ ⊢ pab ⦂ a ≡ b) →
    Drv (Γ ⊢ pbc ⦂ b ≡ c) →
    Drv (Γ ⊢ transitivity T a b c pab pbc ⦂ a ≡ b)

  ≡-congruence : ∀ {Γ} {T a b U c pab} → 
    Drv (Γ ⊢ T ⦂ uni) → 
    Drv (Γ ⊢ a ⦂ T) →
    Drv (Γ ⊢ b ⦂ T) →
    Drv (Γ ⊢ U ⦂ pi T uni) →
    Drv (Γ ⊢ c ⦂ pi T (U ∙ var 0)) →
    Drv (Γ ⊢ pab ⦂ a ≡ b) →
    Drv (Γ ⊢ congruence T a b U c pab ⦂ c ∙ a ≡ c ∙ b)

  ≡-beta : ∀ {Γ} {T a U b} →  
    Drv (Γ ⊢ T ⦂ uni) → 
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (T , Γ ⊢ U ⦂ uni) → 
    Drv (T , Γ ⊢ b ⦂ U) →
    Drv (Γ ⊢ beta T a b ⦂ (lam b) ∙ a ≡ substitute 0 a b)

-- -- TODO: this should be provable
-- postulate
--   ⊢-lift′ : ∀ {Γ} {T U a} →
--     Drv (Γ ⊢ U ⦂ uni) →
--     Drv (Γ ⊢ a ⦂ T) →
--     Drv (U , Γ ⊢ lift a ⦂ lift T)

mutual
  ⊢var-lift′ : ∀ {Γ} {T U n} →
    Drv (Γ ⊢ U ⦂ uni) →
    Drv (Γ ⊢var n ⦂ T) →
    Drv (U , Γ ⊢var suc n ⦂ lift T)
  ⊢var-lift′ {Γ = T , Γ} {T′} {U} {0} ⊢U (⊢var-this ⊢T) =
    ⊢var-that ⊢U (⊢-lift′ ⊢T ⊢T) (⊢var-this ⊢T)
  ⊢var-lift′ {Γ = T , Γ} {T′} {U} {n = suc n} ⊢U (⊢var-that ⊢T ⊢T′ ⊢[var-n]) = 
    ⊢var-that ⊢U (⊢-lift′ ⊢T ⊢T′) (⊢var-lift′ ⊢T ⊢[var-n])

  postulate
    ⊢-lift′ : ∀ {Γ} {T U a} →
      Drv (Γ ⊢ U ⦂ uni) →
      Drv (Γ ⊢ a ⦂ T) →
      Drv (U , Γ ⊢ lift a ⦂ lift T)
    -- ⊢-lift′ {Γ} {T} {U} {a = var n} ⊢U (⊢-var ⊢T ⊢a) = ⊢-var (⊢-lift′ ⊢U ⊢T) (⊢var-lift′ ⊢U ⊢a)
    -- ⊢-lift′ {Γ} {T = pi V W} {U} {a} ⊢U (⊢-lam ⊢V ⊢W ⊢b) = ⊢-lam (⊢-lift′ ⊢U ⊢V) (⊢-lift′ (⊢-lift′ ⊢U ⊢V) {! ⊢W  !}) {!   !}
    -- ⊢-lift′ {Γ} {T} {U} {a} ⊢U ⊢a = {!   !}
    