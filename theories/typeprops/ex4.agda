open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String)
import Data.String as String
open import Data.Bool using (if_then_else_)
open import Relation.Nullary using (does)

infix  10 _⊢_
infixl 20 _◂_ _◂♯_
infixr 30 _`∨_ _`∧_
infix  31 _`⦂_ -- _`＝_
infixl 40 _`∙_ _⊢∙_

data Term : Set where
  `♯ : String → Term
  `λ : String → Term → Term
  `Π : String → Term → Term → Term
  _`∙_ : Term → Term → Term
  `𝒰 : Term
  `⊤ : Term
  `it : Term

data Prop : Set where
  _`⦂_ : Term → Term → Prop 
  `∀ : String → Prop → Prop
  `∃ : String → Prop → Prop
  _`∨_ : Prop → Prop → Prop
  _`∧_ : Prop → Prop → Prop

data Ctx : Set where
  ∅ : Ctx
  _◂_ : Ctx → Prop → Ctx
  _◂♯_ : Ctx → String → Ctx

substTerm : String → Term → Term → Term
substTerm x a (`♯ y) = if does (x String.≟ y) then a else `♯ y
substTerm x a (`λ y t) = if does (x String.≟ y) then `λ y t else `λ y (substTerm x a t)
substTerm x a (`Π y t u) = `Π y (substTerm x a t) (if does (x String.≟ y) then u else substTerm x a u)
substTerm x a (t `∙ u) = substTerm x a t `∙ substTerm x a u
substTerm x a `𝒰 = `𝒰
substTerm x a `⊤ = `⊤
substTerm x a `it = `it

substProp : String → Term → Prop → Prop
substProp x a (t `⦂ u) = substTerm x a t `⦂ substTerm x a u
substProp x a (`∀ y P) = if does (x String.≟ y) then `∀ y P else `∀ y (substProp x a P)
substProp x a (`∃ y P) = if does (x String.≟ y) then `∃ y P else `∃ y (substProp x a P)
substProp x a (P `∨ Q) = substProp x a P `∨ substProp x a Q
substProp x a (P `∧ Q) = substProp x a P `∨ substProp x a Q

data _⊢_ : Ctx → Prop → Set where
  ⊢asm : ∀ {Γ} {P} →
    Γ ◂ P ⊢ P
  
  ⊢wkn : ∀ {Γ} {P Q} →
    Γ ⊢ P →
    Γ ◂ Q ⊢ P
  
  ⊢wkn♯ : ∀ {Γ} {P x} →
    Γ ⊢ P →
    Γ ◂♯ x ⊢ P

  ⊢λ : ∀ {Γ} {x} {t b u} →
    Γ ◂ (`♯ x `⦂ t) ◂♯ x ⊢ b `⦂ u →
    Γ ⊢ `λ x b `⦂ `Π x t u

  ⊢Π : ∀ {Γ} {x} {t u} →
    Γ ⊢ t `⦂ `𝒰 →
    Γ ◂ (`♯ x `⦂ `𝒰) ◂♯ x ⊢ u `⦂ `𝒰 →
    Γ ⊢ `Π x t u `⦂ `𝒰

  _⊢∙_ : ∀ {Γ} {x} {t u f a} →
    Γ ⊢ f `⦂ `Π x t u → 
    Γ ⊢ a `⦂ t →
    Γ ⊢ f `∙ a `⦂ substTerm x a u

  ⊢𝒰 : ∀ {Γ} →
    Γ ⊢ `𝒰 `⦂ `𝒰

  ⊢⊤ : ∀ {Γ} →
    Γ ⊢ `⊤ `⦂ `𝒰

  ⊢it : ∀ {Γ} → 
    Γ ⊢ `it `⦂ `⊤

  ⊢∀ : ∀ {Γ} {x} {P} →
    Γ ◂♯ x ⊢ P →
    Γ ⊢ `∀ x P

  ⊢∃ : ∀ {Γ} {x} t {P} →
    Γ ⊢ substProp x t P →
    Γ ⊢ `∃ x P

  ⊢∃ind : ∀ {Γ} {x} {P Q} →
    Γ ⊢ `∃ x P →
    Γ ◂♯ x ◂ P ⊢ Q →
    Γ ⊢ Q

  ⊢∨₁ : ∀ {Γ} {P Q} → 
    Γ ⊢ P → 
    Γ ⊢ P `∨ Q

  ⊢∨₂ : ∀ {Γ} {P Q} → 
    Γ ⊢ Q → 
    Γ ⊢ P `∨ Q

  ⊢∧ : ∀ {Γ} {P Q} →
    Γ ⊢ P →
    Γ ⊢ Q →
    Γ ⊢ P `∧ Q  

`let : Term
`let = `λ "A" (`λ "B" (`λ "a" (`λ "f" (`♯ "f" `∙ `♯ "a"))))

`Let : Term
`Let = `Π "A" `𝒰 (`Π "B" `𝒰 (`Π "a" (`♯ "A") (`Π "f" (`Π "x" (`♯ "A") (`♯ "B")) (`♯ "B"))))

⊢let : ∀ {Γ} → Γ ⊢ `let `⦂ `Let
⊢let = (⊢λ (⊢λ (⊢λ (⊢λ (⊢wkn♯ ⊢asm ⊢∙ ⊢wkn♯ (⊢wkn (⊢wkn♯ ⊢asm)))))))

⊢id : ∀ {Γ} → Γ ⊢ `∃ "id" (`♯ "id" `⦂ `Π "A" `𝒰 (`Π "x" (`♯ "A") (`♯ "A")))
⊢id = ⊢∃ 
  (`λ "A" (`λ "x" (`♯ "x")))
  (⊢λ (⊢λ (⊢wkn♯ ⊢asm)))

`ex1 : Term
`ex1 = 
  `let `∙ `Π "x" `⊤ `⊤ `∙ `⊤ `∙
    `λ "x" (`♯ "x") `∙ 
    `λ "x" (`♯ "x" `∙ `it)

⊢ex1 : ∀ {Γ} → Γ ⊢ `ex1 `⦂ `⊤
⊢ex1 =
  ⊢let ⊢∙ ⊢Π ⊢⊤ ⊢⊤ ⊢∙ ⊢⊤ ⊢∙ 
    ⊢λ (⊢wkn♯ ⊢asm) ⊢∙
    ⊢λ (⊢wkn♯ ⊢asm ⊢∙ ⊢it)

