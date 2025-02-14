open import Data.Nat
open import Relation.Nullary.Decidable using (yes; no)

-- syntax

data Syn : Set where
  var : ℕ → Syn
  lam : Syn → Syn
  app : Syn → Syn → Syn
  pi : Syn → Syn → Syn
  uni : Syn

-- context

data Ctx : Set where
  ∅ : Ctx
  _,_ : Syn → Ctx → Ctx

-- equality

data _≡_ : Syn → Syn → Set where

-- substitution

substitute : ℕ → Syn → Syn → Syn
substitute n α (var x) with n ≟ x
substitute n α (var x) | yes n≡x = α
substitute n α (var x) | no ¬n≡x = var x
substitute n α (lam b) = lam (substitute (n + 1) α b)
substitute n α (app f a) = app (substitute n α f) (substitute n α a)
substitute n α (pi a b) = pi (substitute n α a) (substitute (n + 1) α b)
substitute n α uni = uni

-- typing derivation

data _⊢var_⦂_ : Ctx → ℕ → Syn → Set where
  this : ∀ Γ α →
    (α , Γ) ⊢var 0 ⦂ α

  that : ∀ n Γ α β →
    Γ ⊢var n ⦂ α → 
    (β , Γ) ⊢var (suc n) ⦂ α

data _⊢_⦂_ : Ctx → Syn → Syn → Set where
  var : ∀ Γ n α →
    Γ ⊢var n ⦂ α →
    Γ ⊢ (var n) ⦂ α
  
  lam : ∀ Γ α b β →
    (α , Γ) ⊢ b ⦂ substitute 0 α β →
    Γ ⊢ lam b ⦂ pi α β

  app : ∀ Γ f a α β →
    Γ ⊢ f ⦂ pi α β → 
    Γ ⊢ a ⦂ α → 
    Γ ⊢ app f a ⦂ substitute 0 α β

  pi : ∀ Γ α β → 
    Γ ⊢ α ⦂ uni →
    (α , Γ) ⊢ β ⦂ uni → 
    Γ ⊢ pi α β ⦂ uni 

  uni : ∀ Γ →
    Γ ⊢ uni ⦂ uni
