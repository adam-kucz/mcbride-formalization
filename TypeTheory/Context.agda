{-# OPTIONS --exact-split --safe --prop  #-}
module TypeTheory.Context where

open import TypeTheory.Basic using (Rig; wfs; _≻_)
open import TypeTheory.Syntax using (Var; Term)

open import Foundation.Universes

-- Definition 6 (precontext, context)

infix 19 _∥_∶_
data Precontext
  {R : 𝒰 ˙}
  ⦃ _ : Rig R ⦄
  {S : 𝒱 ˙}
  ⦃ _ : wfs 𝒲 𝒯 S ⦄
  : -----------------
  𝒰 ⁺ ⊔ 𝒱 ˙
  where
  · : Precontext
  _∥_∶_ :
    (Γ : Precontext)
    (x : Var {𝒰})
    (S : Term)
    → ----------------
    Precontext

infix 19 _∥_,_∶_
data Context
  {R : 𝒰 ˙}
  {S : 𝒱 ˙}
  ⦃ _ : Rig R ⦄
  ⦃ _ : wfs 𝒲 𝒯 S ⦄
  : -----------------
  𝒰 ⁺ ⊔ 𝒱 ˙
  where
  · : Context
  
  _∥_,_∶_ :
    (Δ : Context)
    (ρ : R)
    (x : Var {𝒰})
    (S : Term)
    → --------------
    Context

PC : (R : 𝒰 ˙) (S : 𝒱 ˙) ⦃ _ : Rig R ⦄ ⦃ _ : wfs 𝒲 𝒯 S ⦄ → 𝒰 ⁺ ⊔ 𝒱 ˙
PC R S = Precontext {R = R} {S = S}

Ctx : (R : 𝒰 ˙) (S : 𝒱 ˙) ⦃ _ : Rig R ⦄ ⦃ _ : wfs 𝒲 𝒯 S ⦄ → 𝒰 ⁺ ⊔ 𝒱 ˙
Ctx R 𝑆 = Context {R = R} {S = 𝑆}

precont : ⦃ _ : Rig X ⦄ ⦃ _ : wfs 𝒰 𝒱 Y ⦄
  (Δ : Ctx X Y)
  → ------------
  PC X Y
precont · = ·
precont (Δ ∥ _ , x ∶ S) = precont Δ ∥ x ∶ S

ctx :
  ⦃ _ : Rig X ⦄
  ⦃ _ : wfs 𝒰 𝒱 Y ⦄
  (Γ : PC X Y)
  (r : X)
  → ----------------
  Ctx X Y
ctx · _ = ·
ctx (Γ ∥ x ∶ S) ρ = (ctx Γ ρ) ∥ ρ , x ∶ S

infix 18 _++_
_++_ : ⦃ _ : Rig X ⦄ ⦃ _ : wfs 𝒰 𝒱 Y ⦄
  (Δ Δ' : Ctx X Y)
  → -----------------
  Ctx X Y
Δ ++ · = Δ
Δ ++ (Δ' ∥ ρ , x ∶ S) = (Δ ++ Δ') ∥ ρ , x ∶ S

infix 18 _pt+_
_pt+_ : ⦃ _ : Rig X ⦄ ⦃ _ : wfs 𝒰 𝒱 Y ⦄
  (Δ Δ' : Ctx X Y)
  → -----------------
  Ctx X Y
Δ pt+ Δ' = ?

