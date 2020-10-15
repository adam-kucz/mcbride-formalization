{-# OPTIONS --exact-split #-}
open import Basic
open import Universes

module Renaming.Instance
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Renaming.Definition

open import Data.Nat using (ℕ)

instance
  RenameableFun :
    {F : (m : ℕ) → 𝒳 ˙}
    ⦃ r : Renameable F ⦄
    → --------------------
    Renameable (λ n → X → F n)

open import Function using (_∘ₛ_; _∘_)
open import Proof

open import Axiom.FunctionExtensionality

rename ⦃ RenameableFun ⦄ ρ σ = rename ρ ∘ σ
rename-id ⦃ RenameableFun {𝒴}{𝒳} ⦃ r ⦄ ⦄ =
  subrel $
  fun-ext λ σ →
  subrel $
  ap (_∘ σ) rename-id
rename-∘ ⦃ RenameableFun {𝒴}{𝒳} ⦄ π ρ =
  subrel $
  fun-ext λ σ →
  subrel $
  ap (_∘ σ) $ rename-∘ π ρ 
