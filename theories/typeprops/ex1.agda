open import Data.String using (String)
import Data.String as String
open import Data.Bool using (if_then_else_)
open import Relation.Nullary using (does)

infix 10 _⊢_
infix 20 _`＝_ _`⦂_
infixr 21 _◂_
infixl 21 _⊢∙_
infix 22 ⊢λ[_]

-- term
data Term : Set where
  `♯ : String → Term
  `𝒰 : Term

-- proposition
data Prop : Set where
  _`⦂_ : Term → Term → Prop
  _`＝_ : Term → Term → Prop
  `Π : Prop → Prop → Prop

-- context
data Ctx : Set where
  ∅ : Ctx 
  _◂_ : Prop → Ctx → Ctx

substTerm : String → Term → Term → Term
substTerm x a (`♯ y) = if does (x String.≟ y) then a else `♯ y
substTerm x a `𝒰 = `𝒰

substProp : String → Term → Prop → Prop
substProp x a (b `⦂ t) = substTerm x a b `⦂ substTerm x a t
substProp x a (t `＝ u) = substTerm x a t `＝ substTerm x a u
substProp x a (`Π P Q) with P
substProp x a (`Π P Q)    | (`♯ y `⦂ t) = if does (x String.≟ y) then `Π P Q else `Π (substProp x a P) (substProp x a Q)
substProp x a (`Π P Q)    | _ = `Π (substProp x a P) (substProp x a Q)

-- derivation
data _⊢_ : Ctx → Prop → Set where 
  ⊢Z : ∀ {Γ} {P} →

    -------------
      P ◂ Γ ⊢ P

  ⊢S : ∀ {Γ} {P Q} →

      Γ ⊢ P →
    -------------
      Q ◂ Γ ⊢ P
  
  ⊢λ : ∀ {Γ} {P Q} →

      P ◂ Γ ⊢ Q →
    -------------
      Γ ⊢ `Π P Q

  _⊢∙_ : ∀ {Γ} {t x a Q} → 

      Γ ⊢ `Π (`♯ x `⦂ t) Q → 
      Γ ⊢ (a `⦂ t) → 
    -------------------------
      Γ ⊢ substProp x a Q

  _⊢on_ : ∀ {Γ} {P Q} →

      Γ ⊢ `Π P Q → 
      Γ ⊢ P → 
    -------------
      Γ ⊢ Q
  
  ⊢refl : ∀ {Γ} {t} → 

    ---------------
      Γ ⊢ t `＝ t

⊢λ[_] : ∀ {Γ : Ctx} (P : Prop) {Q : Prop} → (P ◂ Γ ⊢ Q) → (Γ ⊢ `Π P Q)
⊢λ[_] {Γ} P {Q} b = ⊢λ {Γ} {P} {Q} b

⊢id : ∅ ⊢ `Π (`♯ "A" `⦂ `𝒰) (`Π (`♯ "x" `⦂ `♯ "A") (`♯ "x" `⦂ `♯ "A"))
⊢id = ⊢λ (⊢λ ⊢Z)

⊢const : ∀ {Γ} → Γ ⊢ `Π (`♯ "A" `⦂ `𝒰) (`Π (`♯ "x" `⦂ `♯ "A") (`Π (`♯ "B" `⦂ `𝒰) (`Π (`♯ "x" `⦂ `♯ "B") ((`♯ "x" `⦂ `♯ "A")))))
⊢const = ⊢λ (⊢λ (⊢λ (⊢λ (⊢S (⊢S ⊢Z)))))

⊢ex1 : 
  (`♯ "z" `⦂ `♯ "C") ◂ (`♯ "C" `⦂ `𝒰) ◂ (`♯ "w" `⦂ `♯ "D") ◂ (`♯ "D" `⦂ `𝒰) ◂ ∅ ⊢
  (`♯ "w" `⦂ `♯ "C") -- uh oh, something went horribly wrong
⊢ex1 = ⊢const ⊢∙ ⊢S ⊢Z ⊢∙ ⊢Z ⊢∙ ⊢S (⊢S (⊢S ⊢Z)) ⊢∙ ⊢S (⊢S ⊢Z)
