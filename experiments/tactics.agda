open import Reflection
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (no; yes; does)

maybe : ∀ {A B : Set} → Maybe A → B → (A → B) → B
maybe nothing  b f = b
maybe (just a) b f = f a

arg′ : ∀ {a} {A : Set a} → A → Arg A
arg′ = arg (arg-info visible (modality relevant quantity-ω))

either : ∀ {A B C : Set} → A ⊎ B → (A → C) → (B → C) → C
either e k₁ k₂ = [ k₁ , k₂ ]′ e

uh-oh : ⊤
uh-oh = tt

crush-proof : Term → TC (Term ⊎ Term)
-- ⊥
crush-proof (def (quote ⊥) []) = pure (inj₁ (def (quote ⊥) []))
-- A ≡ B
crush-proof goal@(def (quote _≡_) (arg _ _ ∷ arg _ _ ∷ arg _ x ∷ arg _ y ∷ [])) = 
  if does (x ≟ y) 
    then pure (inj₂ (con (quote refl) []))
    else pure (inj₁ goal)
-- A × B
crush-proof (def (quote _×_) (arg _ _ ∷ arg _ _ ∷ arg _ A ∷ arg _ B ∷ [])) = do
  ma ← crush-proof A
  either ma (λ subgoal → pure (inj₁ subgoal)) λ a → do
    mb ← crush-proof B
    either mb (λ subgoal → pure (inj₁ subgoal)) λ b → do
      pure (inj₂ (con (quote _,_) (arg′ a ∷ arg′ b ∷ [])))
-- A ⊎ B
crush-proof (def (quote _⊎_) (arg _ _ ∷ arg _ _ ∷ arg _ A ∷ arg _ B ∷ [])) = do
  ma ← crush-proof A
  either ma 
    (λ subgoal₁ → do 
      mb ← crush-proof B
      either mb 
        (λ subgoal₂ → pure (inj₁ (con (quote _×_) (arg′ subgoal₁ ∷ arg′ subgoal₂ ∷ [])))) 
        (λ b → do
          pure (inj₂ (con (quote inj₂) (arg′ b ∷ []))))
    )
    (λ a → do
      mb ← crush-proof B
      pure (inj₂ (con (quote inj₁) (arg′ a ∷ []))))
-- A → B
crush-proof (pi _ _) = pure (inj₂ (def (quote uh-oh) []))
-- otherwise
crush-proof goal = pure (inj₁ goal)

macro
  crush : Term → TC ⊤
  crush hole = do
    goal ← inferType hole
    mp ← crush-proof goal
    either mp 
      (λ subgoal → typeError (strErr "uncrushable: " ∷ termErr subgoal ∷ []))
      (λ p → unify hole p)

_ : (1 ≡ 1)
_ = crush

_ : (2 ≡ 2) ⊎ (3 ≡ 3)
_ = crush

_ : ⊥ ⊎ (4 ≡ 4)
_ = crush

_ : (⊥ ⊎ (5 ≡ 5)) × ((6 ≡ 6) ⊎ ⊥)
_ = crush

_ : ⊥ → (0 ≡ 1)
_ = crush

