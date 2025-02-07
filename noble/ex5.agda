{-
- axiomatic transport-equality rules, with no formal equality
  - these rules should encapsulate both transport and equality derivation rules
-}

open import Data.Nat

--------------------------------------------------------------------------------
-- infix precendences
--------------------------------------------------------------------------------

infix 10 _⊨_
infix 10 _⊢var_⦂_
infix 10 _⊢_⦂_
infixr 20 _,_
infix 20 _≡_
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
  equal : Syn
  reflexivity : Syn
  symmetry : Syn
  transitivity : Syn
  congruence : Syn

_≡_ : Syn → Syn → Syn
a ≡ b = equal ∙ a ∙ b

--------------------------------------------------------------------------------
-- lifted into larger context
--------------------------------------------------------------------------------

lift : Syn → Syn
lift (var x) = var (x + 1)
lift (lam b) = lam (lift b)
lift (b ∙ a) = lift b ∙ lift a
lift (pi a b) = pi (lift a) (lift b)
lift uni = uni
lift equal = equal
lift reflexivity = equal
lift symmetry = equal
lift transitivity = equal
lift congruence = equal

--------------------------------------------------------------------------------
-- substitution
--------------------------------------------------------------------------------

substitute : ℕ → Syn → Syn → Syn
substitute x v (var y) with compare x y
substitute x v (var y) | less .x k {- y = suc (x + k) -} = var (x + k)
substitute x v (var y) | equal .x = v
substitute x v (var y) | greater .y k = var y
substitute n v (lam b) = lam (substitute (n + 1) (lift v) b)
substitute n v (b ∙ a) = substitute n v b ∙ substitute n v a
substitute n v (pi a b) = pi (substitute n v a) (substitute (n + 1) (lift v) b)
substitute n v uni = uni
substitute n v equal = equal
substitute n v reflexivity = equal
substitute n v symmetry = equal
substitute n v transitivity = equal
substitute n v congruence = equal

--------------------------------------------------------------------------------
-- typing derivation
--------------------------------- -----------------------------------------------

data Ctx : Set where
  ∅ : Ctx
  _,_ : Syn → Ctx → Ctx

data Judgment : Set where
  -- kind judgement
  _⊨_ : Ctx → Syn → Judgment
  -- var type judgement
  _⊢var_⦂_ : Ctx → ℕ → Syn → Judgment
  -- type judgement
  _⊢_⦂_ : Ctx → Syn → Syn → Judgment

data Drv : Judgment → Set where

  ⊨-uni : ∀ {Γ} → 
    Drv (Γ ⊨ uni)
  
  ⊨-pi-uni : ∀ {Γ T U} → 
    Drv (Γ ⊢ U ⦂ uni) →
    Drv (U , Γ ⊨ T) →
    Drv (Γ ⊨ pi U T)
  
  ⊨-pi : ∀ {Γ T U} → 
    Drv (Γ ⊨ U) →
    Drv (U , Γ ⊨ T) →
    Drv (Γ ⊨ pi U T)

  ⊢-var-this : ∀ {Γ} {T} → 
    Drv (T , Γ ⊢var 0 ⦂ lift T)
  ⊢-var-that : ∀ {Γ} {n} {T U} → 
    Drv (Γ ⊢var n ⦂ T) → 
    Drv (U , Γ ⊢var (suc n) ⦂ lift T)

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

  ⊢-lift : ∀ {Γ} {T U a} →
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (U , Γ ⊢ lift a ⦂ lift T)

  ⊢-equal :
      -- equal : ∀ T (a b : T) → uni
      Drv (
        ∅ ⊢ equal ⦂ 
          -- T : uni
          pi uni (
          -- a : T
          pi (var 0) (
          -- b : T
          pi (var 1) 
            uni
          )))

  ⊢-transport : ∀ {Γ} {T U p a} → 
    Drv (Γ ⊢ T ⦂ uni) →
    Drv (Γ ⊢ p ⦂ T ≡ U) →
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (Γ ⊢ a ⦂ U)

  -- -- beta is special: 
  -- -- uses substitute, which can't appear in the type of a term.
  -- ≡-beta : ∀ {Γ} {T a U b} →
  --   Drv (Γ ⊢ T ⦂ uni) →
  --   Drv (Γ ⊢ a ⦂ T) → 
  --   Drv (T , Γ ⊢ b ⦂ U) → 
  --   Drv (Γ ⊢ path ⦂ b ∙ a ≡ substitute 0 a b)

  -- -- the following are not special;
  -- -- they're just non-computational terms that need to be postulated.

  -- ≡-reflexivity : ∀ T (a : T) → a ≡ a
  ≡-reflexivity : Drv (
      ∅ ⊢ reflexivity ⦂ 
        -- pi (T : uni)
        pi uni (
        -- pi (a : T)
        pi (var 0) (
          -- a ≡ a
          var 0 ≡ var 0
        ))
    )

  -- ≡-symmetry : ∀ T (a b : T) → a ≡ b → b ≡ a
  ≡-symmetry : Drv (
      ∅ ⊢ symmetry ⦂ 
        -- pi (T : uni)
        pi uni (
        -- pi (a : T)
        pi (var 0) (
        -- pi (b : T)
        pi (var 0) (
        -- pi (_ : a ≡ b)
        pi (var 1 ≡ var 0) (
          -- b ≡ a
          var 1 ≡ var 2
        ))))
    )
  
  -- ≡-transitivity : ∀ T (a b c : T) → a ≡ b → b ≡ c → a ≡ c
  ≡-transitivity : Drv (
      ∅ ⊢ transitivity ⦂ 
        -- pi (T : uni)
        pi uni (
        -- pi (a : T)
        pi (var 0) (
        -- pi (b : T)
        pi (var 1) (
        -- pi (c : T)
        pi (var 2) (
        -- pi (_ : a ≡ b)
        pi (var 2 ≡ var 1) (
        -- pi (_ : b ≡ c)
        pi (var 2 ≡ var 1) (
          -- pi (_ : a ≡ c)
          var 4 ≡ var 2
        ))))))
    )

  -- ≡-congruence : ∀ T (a b : T) U (c : pi T U) → a ≡ b → c a ≡ c b
  ≡-congruence : Drv (
      ∅ ⊢ congruence ⦂ 
        -- pi (T : uni)
        pi  uni (
        -- pi (a : T)
        pi (var 0)  (
        -- pi (b : T)
        pi (var 1) (
        -- pi (U : uni)
        pi  uni (
        -- pi (c : pi T U)
        pi (pi (var 3) (var 1)) (
        -- pi (_ : a ≡ b)
        pi (var 2 ≡ var 1) (
          -- c a ≡ c b
          (var 1 ∙ var 4 ≡ var 1 ∙ var 3)
        ))))))
    )
