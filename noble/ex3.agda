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
  eq : Syn → Syn → Syn
  path : Syn → Syn

--------------------------------------------------------------------------------
-- embedding into larger context
--------------------------------------------------------------------------------

embed : Syn → Syn
embed (var x) = var (x + 1)
embed (lam b) = lam (embed b)
embed (app b a) = app (embed b) (embed a)
embed (pi a b) = pi (embed a) (embed b)
embed uni = uni
embed (eq a b) = eq (embed a) (embed b)
embed (path a) = path (embed a)

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
substitute n v (eq a b) = eq (substitute n v a) (substitute n v b)
substitute n v (path a) = path (substitute n v a)

--------------------------------------------------------------------------------
-- typing derivation
--------------------------------------------------------------------------------

data Ctx : Set where
  ∅ : Ctx
  _,_ : Syn → Ctx → Ctx

data Judgment : Set where
  _⊢var_⦂_ : Ctx → ℕ → Syn → Judgment
  _⊢_⦂_ : Ctx → Syn → Syn → Judgment
  _≡_ : Syn → Syn → Judgment

data Valid : Judgment → Set where

  ⊢-this : ∀ {Γ} {T} → 
    Valid (T , Γ ⊢var 0 ⦂ embed T)
  ⊢-that : ∀ {Γ} {n} {T U} → 
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

  ⊢transport : ∀ {Γ} {T U a} →
    Valid (Γ ⊢ T ⦂ uni) → 
    Valid (Γ ⊢ U ⦂ uni) →
    Valid (T ≡ U) → 
    Valid (Γ ⊢ a ⦂ T) → 
    Valid (Γ ⊢ a ⦂ U)

  -- what other rules are required?

  ≡-reflexivity : ∀ {a} →
    Valid (a ≡ a)

  ≡-symmetry : ∀ {a b} →
    Valid (a ≡ b) → 
    Valid (b ≡ a)

  ≡-transitivity : ∀ {a b c} → 
    Valid (a ≡ b) → 
    Valid (b ≡ c) → 
    Valid (a ≡ c)
  
  ≡-congruence : ∀ {a b c} → 
    Valid (a ≡ b) → 
    Valid (substitute 0 c a ≡ substitute 0 c b)

  ≡-beta : ∀ {a b} →
    Valid (app b a ≡ substitute 0 a b)

-- PROBLEM: which this all works for in-place proofs of equivlance, it doesn't
-- let you state properties of equivalence and prove lemmas about it

