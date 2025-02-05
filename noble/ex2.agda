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

  ⊢congruence : ∀ {Γ} {T a b R c p} → 
    Γ ⊢ T ⦂ uni →
    Γ ⊢ a ⦂ T → 
    Γ ⊢ b ⦂ T → 
    Γ ⊢ p ⦂ eq a b →
    Γ ⊢ substitute 0 a c ⦂ substitute 0 a R →
    Γ ⊢ substitute 0 b c ⦂ substitute 0 b R

--------------------------------------------------------------------------------
-- properties to prove
--------------------------------------------------------------------------------


-- reflexivity : ∀ T (a : T) → a ≡ a
reflexivity' : Syn
reflexivity' = lam (lam (path (var 0)))

postulate
  reflexivity :
    ∅ ⊢ reflexivity' ⦂
    pi {- T : uni -} uni (
    pi {- a : T -} (var 0) (
      eq (var 0) (var 0)
    ))
-- reflexivity = ?

-- trans : ∀ T (a b c : T) → a = b → b = c → a = c
transitivity' : Syn
transitivity' = lam (lam (lam (lam (lam (lam (var 1))))))

postulate
  transitivity : 
    ∅ ⊢  transitivity' ⦂ 
    pi {- T  : uni   -} uni (
    pi {- a  : T     -} (var 0) (
    pi {- b  : T     -} (var 1) (
    pi {- c  : T     -} (var 2) (
    pi {- p1 : a ≡ b -} (eq (var 2) (var 1)) (
    pi {- p2 : b ≡ c -} (eq (var 2) (var 1)) (
      eq (var 4) (var 2)
    ))))))
-- transitivity =
--   ⊢lam (⊢lam (⊢lam (⊢lam (⊢lam (⊢lam
--     -- S   := var 5
--     -- a   := var 4
--     -- b   := var 3
--     -- c   := var 2
--     -- p1 := var 1
--     -- p2 := var 0
--     --------------------------
--     -- p1 : a ≡ b
--     -- p2 : b ≡ c
--     --------------------------
--     -- use congruence to rewrite p2 in p1 to get a ≡ c
--     (⊢congruence {_} {T = var 5} {a = var 3} {b = var 2} {R = eq (var 5) (var 0)} {c = var 2} {p = var 0}
--       -- Γ ⊢ S ⦂ uni
--       (⊢var (⊢that (⊢that (⊢that (⊢that (⊢that ⊢this)))))) 
--       -- Γ ⊢ a ⦂ S 
--       (⊢var (⊢that (⊢that (⊢that ⊢this)))) 
--       -- Γ ⊢ b ⦂ S 
--       (⊢var (⊢that (⊢that ⊢this))) 
--       -- Γ ⊢ p ⦂ eq a b 
--       (⊢var ⊢this) 
--       -- Γ ⊢ substitute 0 a c ⦂ substitute 0 a T
--       (⊢var (⊢that ⊢this))
--     )
--   )))))

-- ⊢this probably possible, but i haven't finished it yet

-- symmetry : ∀ T (a b : T) → a ≡ b → b ≡ a
symmetry' : Syn
symmetry' = lam (lam (lam (lam (var 0))))

postulate
  symmetry :
    ∅ ⊢ symmetry' ⦂
    pi {- T : uni -} uni (
    pi {- a : T -} (var 0) (
    pi {- b : T -} (var 1) (
    pi {- p : a ≡ b -} (eq (var 1) (var 0)) (
      eq (var 1) (var 2)
    ))))
-- symmetry = 
--   ⊢lam (⊢lam (⊢lam (⊢lam
--     -- T : uni   := var 3
--     -- a : T     := var 2
--     -- b : T     := var 1
--     -- p : a ≡ b := var 0
--     (leibniz {_} {T = var 3} {a = var 1} {b = var 2}
--         (var (⊢that (⊢that (⊢that ⊢this)))) 
--         (var (⊢that ⊢this))
--         (var (⊢that (⊢that ⊢this)))
--         (transport {_} 
--           {T = app (var 1) (var 4)}
--           {R = app (var 1) (embed (embed (var 2)))} 
--           {p = app (app reflexivity' uni) (app (var 1) (var 4))}
--           {a = var 0}
--           (app (var (⊢that ⊢this)) (var (⊢that (⊢that (⊢that (⊢that ⊢this))))))
--           (app (var (⊢that ⊢this)) (var (⊢that (⊢that (⊢that (⊢that ⊢this)))))) 
--           -- (reflexivity (app (var 1) (var 4)))
--           -- weaken (weaken (weaken (weaken (weaken (weaken reflexivity))))) 
--           -- (app (app (weaken {S = app (var 0) (var 2)} ?) {!   !}) {!   !})
--           {!   !}
--           {!   !}
--         )
--         --------------------------
--         -- app (var 0) (var 2) , pi (var 3) uni , eq (var 1) (var 0) , var 1 , var 0 , uni , ∅ ⊢
--         -- var 0 ⦂ 
--         -- app (var 1) (var 4)
--     )
--     -- --------------------------
--     -- eq (var 1) (var 0) , var 1 , var 0 , uni , ∅ ⊢ 
--     -- var 0 ⦂ 
--     -- eq (var 2) (var 1)
--   )))
  