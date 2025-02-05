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
infixr 11 _,_

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
embed (app f a) = app (embed f) (embed a)
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
substitute n v (app f a) = app (substitute n v f) (substitute n v a)
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

data _⊢var_⦂_ : Ctx → ℕ → Syn → Set where
  ⊢this : ∀ {Γ} {T} →
    T , Γ ⊢var 0 ⦂ embed T

  ⊢that : ∀ {Γ} {n} {T R} →
    Γ ⊢var n ⦂ T → 
    R , Γ ⊢var (suc n) ⦂ embed T

data _⊢_⦂_ : Ctx → Syn → Syn → Set where

  -- strictly necessary

  ⊢var : ∀ {Γ} {n} {T} →
    Γ ⊢var n ⦂ T →
    Γ ⊢ (var n) ⦂ T
  
  ⊢lam : ∀ {Γ} {T R b} →
    T , Γ ⊢ b ⦂ R →
    Γ ⊢ lam b ⦂ pi T R

  ⊢app : ∀ {Γ} {f T a R} →
    Γ ⊢ f ⦂ pi T R → 
    Γ ⊢ a ⦂ T → 
    Γ ⊢ app f a ⦂ substitute 0 T R

  ⊢pi : ∀ {Γ} {T R} → 
    Γ ⊢ T ⦂ uni →
    T , Γ ⊢ R ⦂ uni → 
    Γ ⊢ pi T R ⦂ uni 

  ⊢uni : ∀ {Γ} →
    Γ ⊢ uni ⦂ uni

  ⊢embed : ∀ {Γ} {S T a} →
    Γ ⊢ a ⦂ T → 
    S , Γ ⊢ embed a ⦂ embed T

  -- accepted as necessary for this experiment

  ⊢transport : ∀ {Γ} {T R p a} →
    Γ ⊢ T ⦂ uni → 
    Γ ⊢ R ⦂ uni →
    Γ ⊢ p ⦂ eq T R → 
    Γ ⊢ a ⦂ T → 
    Γ ⊢ a ⦂ R

  -- what other rules are required?
  -- answer: typed version of equivalence properties as axioms
  -- but actually these don't even need to be derivation rules, they can just be
  -- postulated terms of the appropriate types

  ⊢reflexivity : ∀ {Γ} {T a} → 
    Γ ⊢ T ⦂ uni →
    Γ ⊢ a ⦂ T →
    Γ ⊢ path a ⦂ eq a a

  ⊢symmetry : ∀ {Γ} {T a b p} → 
    Γ ⊢ T ⦂ uni →
    Γ ⊢ a ⦂ T →
    Γ ⊢ b ⦂ T →
    Γ ⊢ p ⦂ eq a b →
    Γ ⊢ p ⦂ eq b a

  ⊢transitivity : ∀ {Γ} {T a b c p1 p2} → 
    Γ ⊢ T ⦂ uni →
    Γ ⊢ a ⦂ T →
    Γ ⊢ b ⦂ T →
    Γ ⊢ c ⦂ T →
    Γ ⊢ p1 ⦂ eq a b →
    Γ ⊢ p2 ⦂ eq b c →
    Γ ⊢ p1 ⦂ eq a c

  ⊢congruence : ∀ {Γ} {T a b R c p} → 
    Γ ⊢ T ⦂ uni →
    Γ ⊢ a ⦂ T → 
    Γ ⊢ b ⦂ T → 
    Γ ⊢ p ⦂ eq a b →
    Γ ⊢ substitute 0 a c ⦂ substitute 0 a R →
    Γ ⊢ substitute 0 b c ⦂ substitute 0 b R

