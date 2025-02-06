{-
If we accept ⊢that transport must be a typing derivation rule, 
then what are the minimal other rulesthat are required to define equivalence?
Do we really need to postulate all the usual equivalence properties? 
Or, can they be derived all from a simple clever definition or smaller set of 
rules?
-}

open import Data.Nat

--------------------------------------------------------------------------------
-- infix precendences
--------------------------------------------------------------------------------

infix 10 _⊢var_⦂_
infix 10 _⊢_⦂_
infix 11 _≡_
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
  _≡_ : Syn → Syn → Syn
  reflexivity : Syn
  symmetry : Syn
  transitivity : Syn
  congruence : Syn
  beta : Syn

--------------------------------------------------------------------------------
-- embedding into larger context
--------------------------------------------------------------------------------

embed : Syn → Syn
embed (var x) = var (x + 1)
embed (lam b) = lam (embed b)
embed (b ∙ a) = embed b ∙ embed a
embed (pi a b) = pi (embed a) (embed b)
embed uni = uni
embed (a ≡ b) = embed a ≡ embed b
embed reflexivity = reflexivity
embed symmetry = symmetry
embed transitivity = transitivity
embed congruence = congruence
embed beta = beta

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
substitute n v (a ≡ b) = substitute n v a ≡ substitute n v b
substitute n v reflexivity = reflexivity
substitute n v symmetry = reflexivity
substitute n v transitivity = reflexivity
substitute n v congruence = reflexivity
substitute n v beta = reflexivity

--------------------------------------------------------------------------------
-- typing derivation
--------------------------------------------------------------------------------

data Ctx : Set where
  ∅ : Ctx
  _,_ : Syn → Ctx → Ctx

data Judgment : Set where
  _⊢var_⦂_ : Ctx → ℕ → Syn → Judgment
  _⊢_⦂_ : Ctx → Syn → Syn → Judgment

data Drv : Judgment → Set where

  -- ⊢var rules

  ⊢var-this : ∀ {Γ} {T} → 
    Drv (T , Γ ⊢var 0 ⦂ embed T)
  ⊢var-that : ∀ {Γ} {n} {T U} → 
    Drv (Γ ⊢var n ⦂ T) → 
    Drv (U , Γ ⊢var (suc n) ⦂ embed T)

  ⊢-var : ∀ {Γ} {n} {T} → 
    Drv (Γ ⊢var n ⦂ T) → 
    Drv (Γ ⊢ var n ⦂ T)

  -- ⊢ rules

  ⊢-lam : ∀ {Γ} {T U b} → 
    Drv (T , Γ ⊢ b ⦂ U) → 
    Drv (Γ ⊢ lam b ⦂ pi T U)

  ⊢-app : ∀ {Γ} {T U b a} → 
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

  ⊢-transport : ∀ {Γ} {T U p a} →
    Drv (Γ ⊢ T ⦂ uni) → 
    Drv (Γ ⊢ U ⦂ uni) →
    Drv (Γ ⊢ p ⦂ T ≡ U) → 
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (Γ ⊢ a ⦂ U)

  -- ≡ rules

  -- must be a Drv rather than just a postulate since uses substitute
  ≡-congruence : ∀ {Γ} {T a b p U c} →
    Drv (Γ ⊢ T ⦂ uni) →
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (Γ ⊢ b ⦂ T) → 
    Drv (Γ ⊢ p ⦂ a ≡ b) → 
    Drv (T , Γ ⊢ c ⦂ U) →
    Drv (Γ ⊢ congruence ∙ a ∙ b ∙ c ∙ p ⦂ substitute 0 a c ≡ substitute 0 b c)

  -- must be a Drv rather than just a postulate since uses substitute
  ≡-beta : ∀ {Γ} {T a U b} →
    Drv (Γ ⊢ T ⦂ uni) →
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (T , Γ ⊢ b ⦂ U) → 
    Drv (Γ ⊢ beta ∙ a ∙ b ⦂ b ∙ a ≡ substitute 0 a b)

-- ≡-reflexivity : ∀ T (a : T) → a ≡ a
postulate ≡-reflexivity : Drv (∅ ⊢ reflexivity ⦂ pi uni (pi (var 0) (var 0 ≡ var 0)))
-- ≡-symmetry : ∀ T (a b : T) → a ≡ b → b ≡ a
postulate ≡-symmetry : Drv (∅ ⊢ symmetry ⦂ pi uni (pi (var 0) (pi (var 0) (pi (var 1 ≡ var 0) (var 1 ≡ var 2)))))
-- ≡-transitivity : ∀ T (a b c : T) → a ≡ b → b ≡ c → a ≡ c
postulate ≡-transitivity : Drv (∅ ⊢ transitivity ⦂ pi uni (pi (var 0) (pi (var 1) (pi (var 2) (pi (var 2 ≡ var 1) (pi (var 2 ≡ var 1) (var 4 ≡ var 2)))))))
