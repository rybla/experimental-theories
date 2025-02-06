{-

# Ex4

If we accept ⊢that transport must be a typing derivation rule, 
then what are the minimal other rulesthat are required to define equivalence?
Do we really need to postulate all the usual equivalence properties? 
Or, can they be derived all from a simple clever definition or smaller set of 
rules?

## Summary

This model takes the following as axiomatic:
- equivlance type family: equivalent
- transport typing derivation
- beta-equivalence typing derivation
- equivalence properties (reflexivity, symmetry, transitivity, congruence) 
  as typing derivations

## Remarks

This does seem to work, but it has a few weird parts.

One weird part is that 

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
  equivalent : Syn
  reflexivity : Syn
  symmetry : Syn
  transitivity : Syn
  congruence : Syn
  beta : Syn

_≡_ : Syn → Syn → Syn
a ≡ b = equivalent ∙ a ∙ b

--------------------------------------------------------------------------------
-- embedding into larger context
--------------------------------------------------------------------------------

embed : Syn → Syn
embed (var x) = var (x + 1)
embed (lam b) = lam (embed b)
embed (b ∙ a) = embed b ∙ embed a
embed (pi a b) = pi (embed a) (embed b)
embed uni = uni
embed equivalent = equivalent
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
substitute n v equivalent = equivalent
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
  
  ⊢-equivalent :
    Drv (∅ ⊢ equivalent ⦂ pi uni (pi uni uni))

  ⊢-embed : ∀ {Γ} {T U a} →
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (U , Γ ⊢ embed a ⦂ embed T)

  -- accepted as necessary for this experiment.
  -- transport is special:
  -- changes the type of a term, which can't be expressed in the type of a term
  ⊢-transport : ∀ {Γ} {T U p a} →
    Drv (Γ ⊢ T ⦂ uni) → 
    Drv (Γ ⊢ U ⦂ uni) →
    Drv (Γ ⊢ p ⦂ T ≡ U) → 
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (Γ ⊢ a ⦂ U)

  -- beta is special: 
  -- uses substitute, which can't appear in the type of a term
  ≡-beta : ∀ {Γ} {T a U b} →
    Drv (Γ ⊢ T ⦂ uni) →
    Drv (Γ ⊢ a ⦂ T) → 
    Drv (T , Γ ⊢ b ⦂ U) → 
    Drv (Γ ⊢ beta ∙ a ∙ b ⦂ b ∙ a ≡ substitute 0 a b)

  -- the following are not special;
  -- they're just non-computational terms that need to be postulated.

  -- ≡-reflexivity : ∀ T (a : T) → a ≡ a
  ≡-reflexivity : Drv (
      ∅ ⊢ reflexivity ⦂ 
        -- pi (T : uni)
        pi uni (
        -- pi (a : T)
        pi {- a : T -} (var 0) (
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
        pi {- a ≡ b -} (var 2 ≡ var 1) (
          -- c a ≡ c b
          (var 1 ∙ var 4 ≡ var 1 ∙ var 3)
        ))))))
    )
