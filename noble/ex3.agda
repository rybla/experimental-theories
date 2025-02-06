{-
If we accept ⊢that transport must be a typing derivation rule, 
then what are the minimal other rules ⊢that are required to define equivalence?
Do we really need to postulate all the usual equivalence properties? 
Or, can they be derived all from a simple clever definition?
-}

open import Data.Nat

--------------------------------------------------------------------------------
-- infix precendences
--------------------------------------------------------------------------------

infix 10 _⊢var_⦂_
infix 10 _⊢_⦂_
infix 10 _⊢_≡_
infixr 20 _,_
infixl 20 _∙_

--------------------------------------------------------------------------------
-- syntax
--------------------------------------------------------------------------------

data Syn : Set where
  var : ℕ → Syn
  lam : Syn → Syn
  _∙_ : Syn → Syn → Syn
  pi : Syn → Syn → Syn
  uni : Syn

-- _≡_ : Syn → Syn → Syn
-- a ≡ b = equivalent ∙ a ∙ b

--------------------------------------------------------------------------------
-- embedding into larger context
--------------------------------------------------------------------------------

embed : Syn → Syn
embed (var x) = var (x + 1)
embed (lam b) = lam (embed b)
embed (b ∙ a) = embed b ∙ embed a
embed (pi a b) = pi (embed a) (embed b)
embed uni = uni

--------------------------------------------------------------------------------
-- substitution
--------------------------------------------------------------------------------

substitute : ℕ → Syn → Syn → Syn
substitute x v (var y) with compare x y
substitute x v (var y) | less .x k {- y = suc (x + k) -} = var (x + k)
substitute x v (var y) | equal .x = v
substitute x v (var y) | greater .y k = var y
substitute n v (lam b) = lam (substitute (n + 1) (embed v) b)
substitute n v (b ∙ a) = substitute n v b ∙ substitute n v a
substitute n v (pi a b) = pi (substitute n v a) (substitute (n + 1) (embed v) b)
substitute n v uni = uni

--------------------------------------------------------------------------------
-- typing derivation
--------------------------------------------------------------------------------

data Ctx : Set where
  ∅ : Ctx
  _,_ : Syn → Ctx → Ctx

data Judgment : Set where
  _⊢var_⦂_ : Ctx → ℕ → Syn → Judgment
  _⊢_⦂_ : Ctx → Syn → Syn → Judgment
  _⊢_≡_ : Ctx → Syn → Syn → Judgment

data Drv : Judgment → Set where

  ⊢-this : ∀ {Γ} {T} → 
    Drv (T , Γ ⊢var 0 ⦂ embed T)
  ⊢-that : ∀ {Γ} {n} {T U} → 
    Drv (Γ ⊢var n ⦂ T) → 
    Drv (U , Γ ⊢var (suc n) ⦂ embed T)

  ⊢-var : ∀ {Γ} {n} {T} → 
    Drv (Γ ⊢var n ⦂ T) → 
    Drv (Γ ⊢ var n ⦂ T)

  ⊢-lam : ∀ {Γ} {T U b} → 
    Drv (T , Γ ⊢ b ⦂ U) → 
    Drv (Γ ⊢ lam b ⦂ pi T U)

  ⊢-∙ : ∀ {Γ} {T U b a} → 
    Drv (Γ ⊢ b ⦂ pi T U) → 
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (Γ ⊢ b ∙ a ⦂ substitute 0 T U)

  ⊢-pi : ∀ {Γ} {T U} → 
    Drv (Γ ⊢ T ⦂ uni) → 
    Drv (T , Γ ⊢ U ⦂ uni) → 
    Drv (Γ ⊢ pi T U ⦂ uni)

  ⊢-uni : ∀ {Γ} →
    Drv (Γ ⊢ uni ⦂ uni)

  ⊢-embed : ∀ {Γ} {T U a} →
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (U , Γ ⊢ embed a ⦂ embed T)

  -- accepted as necessary for this experiment

  ⊢transport : ∀ {Γ} {T U a} →
    Drv (Γ ⊢ T ⦂ uni) → 
    Drv (Γ ⊢ U ⦂ uni) →
    Drv (Γ ⊢ T ≡ U) → 
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (Γ ⊢ a ⦂ U)

  -- what other rules are required?

  ≡-reflexivity : ∀ {Γ} {T a} →
    Drv (Γ ⊢ T ⦂ uni) → 
    Drv (Γ ⊢ a ⦂ T) →
    Drv (Γ ⊢ a ≡ a)

  ≡-symmetry : ∀ {Γ} {T a b} →
    Drv (Γ ⊢ T ⦂ uni) → 
    Drv (Γ ⊢ a ⦂ T) →
    Drv (Γ ⊢ b ⦂ T) →
    Drv (Γ ⊢ a ≡ b) → 
    Drv (Γ ⊢ b ≡ a)

  ≡-transitivity : ∀ {Γ} {T a b c} → 
    Drv (Γ ⊢ T ⦂ uni) → 
    Drv (Γ ⊢ a ⦂ T) →
    Drv (Γ ⊢ b ⦂ T) →
    Drv (Γ ⊢ c ⦂ T) →
    Drv (Γ ⊢ a ≡ b) → 
    Drv (Γ ⊢ b ≡ c) → 
    Drv (Γ ⊢ a ≡ c)
  
  ≡-congruence : ∀ {Γ} {T a b U c} →
    Drv (Γ ⊢ T ⦂ uni) → 
    Drv (Γ ⊢ a ⦂ T) →
    Drv (Γ ⊢ b ⦂ T) →
    Drv (T , Γ ⊢ c ⦂ U) →
    Drv (Γ ⊢ a ≡ b) → 
    Drv (Γ ⊢ substitute 0 c a ≡ substitute 0 c b)

  ≡-beta : ∀ {Γ} {T a b} →
    Drv (Γ ⊢ T ⦂ uni) → 
    Drv (Γ ⊢ a ⦂ T) →
    Drv (Γ ⊢ b ⦂ T) →
    Drv (Γ ⊢ b ∙ a ≡ substitute 0 a b)

-- PROBLEM: which this all works for in-place proofs of equivlance, it doesn't
-- let you state properties of equivalence and prove lemmas about it

