{-# OPTIONS --exact-split --prop  #-}
open import PropUniverses
open import Basic using (Rig; wfs; _≻_)

module Context
  {R : 𝒰 ˙} ⦃ r : Rig R ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Syntax using (Var; Term)

open import Data.Nat renaming (_+_ to _+ℕ_) hiding (_⊔_)
open import Structure.Hemiring using (_+_)

-- Definition 6 (precontext, context)

infixl 155 _∥x:_
-- index n denotes how many variables are defined by a (pre-)context
-- by construction no free variables are allowed in contexts
data Precontext : (n : ℕ) → 𝒰 ⁺ ⊔ 𝒱 ˙ where
  · : Precontext 0
  _∥x:_ : {n : ℕ}
    (Γ : Precontext n)
    (S : Term n)
    → ----------------
    Precontext (suc n)

variable
  Γ Γ' Γ″ : Precontext n

infixl 155 _∥_,x:_
data Context : (n : ℕ) → 𝒰 ⁺ ⊔ 𝒱 ˙ where
  · : Context 0
  
  _∥_,x:_ : ∀ {n}
    (Δ : Context n)
    (ρ : R)
    (S : Term n)
    → --------------
    Context (suc n)

variable
  Δ Δ' Δ″ : Context n

precont : (ctx : Context n) → Precontext n
precont · = ·
precont (Δ ∥ _ ,x: S) = precont Δ ∥x: S

ctx : (Γ : Precontext n)(r : R) → Context n
ctx · _ = ·
ctx (Γ ∥x: S) ρ = (ctx Γ ρ) ∥ ρ ,x: S

open import Proposition.Identity using (_==_)
-- open import Proposition.Function using (_$_)
-- open import Operation.Binary using (comm)

-- infixl 153 _++_
-- _++_ : ∀ {m n} (Δ : Context m) (Δ' : Context n) → Context (n +ℕ m)
-- Δ ++ · = Δ
-- _++_ {m} {suc n} Δ (Δ' ∥ ρ ,x: S) = (Δ ++ Δ') ∥ ρ ,x: S'
--   where S' = transport== (ap Term $ comm m n) (shift-by m S)

open import Logic using (⊤; _∧_)

compatible : (Δ Δ' : Context n) → 𝒰 ⁺ ⊔ 𝒱 ᵖ
compatible · · = Lift𝒰ᵖ ⊤
compatible (Δ ∥ _ ,x: S) (Δ' ∥ _ ,x: S') = compatible Δ Δ' ∧ S == S'
  
subcomp = _∧_.left

infixl 154 _pt+_[_]
_pt+_[_] :
  (Δ Δ' : Context n)
  (p : compatible Δ Δ')
  → ----------------------------
  Context n
· pt+ · [ p ] = ·
Δ ∥ ρ₁ ,x: S₁ pt+ Δ' ∥ ρ ,x: S [ p ] = (Δ pt+ Δ' [ subcomp p ]) ∥ ρ + ρ₁ ,x: S

