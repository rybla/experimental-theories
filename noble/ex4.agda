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
infix 11 _≡_
infixr 20 _,_

--------------------------------------------------------------------------------
-- syntax
--------------------------------------------------------------------------------

data Syn : Set where
  var : ℕ → Syn
  lam : Syn → Syn
  app : Syn → Syn → Syn
  pi : Syn → Syn → Syn
  uni : Syn
  _≡_ : Syn → Syn → Syn
  reflexivity : Syn → Syn → Syn → Syn
  symmetry : Syn → Syn
  transitivity : Syn → Syn → Syn
  congruence : Syn → Syn → Syn → Syn → Syn
  beta : Syn → Syn → Syn

--------------------------------------------------------------------------------
-- embedding into larger context
--------------------------------------------------------------------------------

embed : Syn → Syn
embed (var x) = var (x + 1)
embed (lam b) = lam (embed b)
embed (app b a) = app (embed b) (embed a)
embed (pi a b) = pi (embed a) (embed b)
embed uni = uni
embed (a ≡ b) = embed a ≡ embed b
embed (reflexivity T a b) = reflexivity (embed T) (embed a) (embed b)
embed (symmetry p) = symmetry (embed p)
embed (transitivity p1 p2) = transitivity (embed p1) (embed p2)
embed (congruence a b c p) = congruence (embed a) (embed b) (embed c) (embed p)
embed (beta b a) = beta (embed b) (embed a)

--------------------------------------------------------------------------------
-- substitution
--------------------------------------------------------------------------------

substitute : ℕ → Syn → Syn → Syn
substitute x v (var y) with compare x y
substitute x v (var y) | less .x k {- y = suc (x + k) -} = var (x + k)
substitute x v (var y) | equal .x = v
substitute x v (var y) | greater .y k = var y
substitute n v (lam b) = lam (substitute (n + 1) (embed v) b)
substitute n v (app b a) = app (substitute n v b) (substitute n v a)
substitute n v (pi a b) = pi (substitute n v a) (substitute (n + 1) (embed v) b)
substitute n v uni = uni
substitute n v (a ≡ b) = substitute n v a ≡ substitute n v b
substitute n v (reflexivity T a b) = reflexivity (substitute n v T) (substitute n v a) (substitute n v b)
substitute n v (symmetry p) = symmetry (substitute n v p)
substitute n v (transitivity p1 p2) = transitivity (substitute n v p1) (substitute n v p2)
substitute n v (congruence a b c p) = congruence (substitute n v a) (substitute n v b) (substitute n v c) (substitute n v p)
substitute n v (beta b a) = beta (substitute n v b) (substitute n v a)

--------------------------------------------------------------------------------
-- typing derivation
--------------------------------------------------------------------------------

data Ctx : Set where
  ∅ : Ctx
  _,_ : Syn → Ctx → Ctx

data Judgment : Set where
  _⊢var_⦂_ : Ctx → ℕ → Syn → Judgment
  _⊢_⦂_ : Ctx → Syn → Syn → Judgment

data Valid : Judgment → Set where

  ⊢var-this : ∀ {Γ} {T} → 
    Valid (T , Γ ⊢var 0 ⦂ embed T)
  ⊢var-that : ∀ {Γ} {n} {T U} → 
    Valid (Γ ⊢var n ⦂ T) → 
    Valid (U , Γ ⊢var (suc n) ⦂ embed T)

  ⊢-var : ∀ {Γ} {n} {T} → 
    Valid (Γ ⊢var n ⦂ T) → 
    Valid (Γ ⊢ var n ⦂ T)

  ⊢-lam : ∀ {Γ} {T U b} → 
    Valid (T , Γ ⊢ b ⦂ U) → 
    Valid (Γ ⊢ lam b ⦂ pi T U)

  ⊢-app : ∀ {Γ} {T U b a} → 
    Valid (Γ ⊢ b ⦂ pi T U) → 
    Valid (Γ ⊢ a ⦂ T) → 
    Valid (Γ ⊢ app b a ⦂ substitute 0 T U)

  ⊢-pi : ∀ {Γ} {T U} → 
    Valid (Γ ⊢ T ⦂ uni) → 
    Valid (T , Γ ⊢ U ⦂ uni) → 
    Valid (Γ ⊢ pi T U ⦂ uni)

  ⊢-uni : ∀ {Γ} →
    Valid (Γ ⊢ uni ⦂ uni)

  ⊢-embed : ∀ {Γ} {T U a} →
    Valid (Γ ⊢ a ⦂ T) → 
    Valid (U , Γ ⊢ embed a ⦂ embed T)

  -- accepted as necessary for this experiment

  ⊢-transport : ∀ {Γ} {T U p a} →
    Valid (Γ ⊢ T ⦂ uni) → 
    Valid (Γ ⊢ U ⦂ uni) →
    Valid (Γ ⊢ p ⦂ T ≡ U) → 
    Valid (Γ ⊢ a ⦂ T) → 
    Valid (Γ ⊢ a ⦂ U)

  -- what other rules are required?

  ≡-reflexivity : ∀ {Γ} {T a} →
    Valid (Γ ⊢ T ⦂ uni) →
    Valid (Γ ⊢ reflexivity T a a ⦂ a ≡ a)

  ≡-symmetry : ∀ {Γ} {T a b p} →
    Valid (Γ ⊢ T ⦂ uni) → 
    Valid (Γ ⊢ a ⦂ T) → 
    Valid (Γ ⊢ b ⦂ T) → 
    Valid (Γ ⊢ p ⦂ a ≡ b) → 
    Valid (Γ ⊢ symmetry p ⦂ b ≡ a)

  ≡-transitivity : ∀ {Γ} {T a b c p1 p2} → 
    Valid (Γ ⊢ T ⦂ uni) → 
    Valid (Γ ⊢ a ⦂ T) → 
    Valid (Γ ⊢ b ⦂ T) → 
    Valid (Γ ⊢ c ⦂ T) → 
    Valid (Γ ⊢ p1 ⦂ a ≡ b) → 
    Valid (Γ ⊢ p2 ⦂ b ≡ c) → 
    Valid (Γ ⊢ transitivity p1 p2 ⦂ a ≡ c)
  
  ≡-congruence : ∀ {Γ} {T a b p U c} →
    Valid (Γ ⊢ T ⦂ uni) →
    Valid (Γ ⊢ a ⦂ T) → 
    Valid (Γ ⊢ b ⦂ T) → 
    Valid (Γ ⊢ p ⦂ a ≡ b) → 
    Valid (T , Γ ⊢ c ⦂ U) →
    Valid (Γ ⊢ congruence a b c p ⦂ substitute 0 a c ≡ substitute 0 b c)

  ≡-beta : ∀ {Γ} {T a U b} →
    Valid (Γ ⊢ T ⦂ uni) →
    Valid (Γ ⊢ a ⦂ T) → 
    Valid (T , Γ ⊢ b ⦂ U) → 
    Valid (Γ ⊢ beta a b ⦂ app b a ≡ substitute 0 a b)

-- what's wrong with this system?