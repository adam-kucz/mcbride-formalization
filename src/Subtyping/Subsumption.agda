{-# OPTIONS --exact-split --prop #-}
open import Basic
open import PropUniverses

module Subtyping.Subsumption
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Subtyping.Definition

open import Data.Nat hiding (_⊔_)
open import Relation.Binary

open import Syntax.Definition ⦃ rig ⦄ ⦃ wfs ⦄
open import Judgment
open import Context

-- Theorem 22 (subsumption)

_ctx-≼_ : Rel (𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲) (Context n) (Context n)

subsume-check : {ρ : R}{S s T : Term n}
  (p₀ : Δ' ctx-≼ Δ)
  (p₁ : S ≼ T)
  (q : Δ ⊢ ρ , S ∋ s)
  → ----------------------------
  Δ' ⊢ ρ , T ∋ s

open import Relation.Binary
open import Subtyping.Preservation
open import Logic

subsume-check p₀ p₁ (pre p T⇝R) with step-↠-preserves-≼ p₁ (subrel T⇝R)
subsume-check p₀ p₁ (pre {R = R} q T⇝R) | R' , (R≼R' , T↠R') =
  iter-pre (subsume-check p₀ R≼R' q) T↠R'
subsume-check p₀ (≼similar (~sort j)) (sort p j≻i) = {!sort p j≻i!} -- sort p j≻i
subsume-check p₀ (≼sort k≻j) (sort p j≻i) = {!!} -- sort p (trans k≻j j≻i)
subsume-check p₀ p₁ (fun π p Γ⊢₀*ᵢ∋S Γ,x:S⊢₀*ᵢ∋T) = {!!}
  -- {!Γ,x:S⊢₀*ᵢ∋T !}
  -- goal                      : ctx Γ 0 ⊢ 0 , T ∋ [ π x: S₁ ]→ T₁
  -- fun π Γ⊢₀*ᵢ∋S Γ,x:S⊢₀*ᵢ∋T : ctx Γ 0 ⊢ 0 , ⋆ i ∋ [ π x: S₁ ]→ T₁
  -- subsume-check Γ⊢₀*ᵢ∋S q   : ctx Γ 0 ⊢ 0 , T ∋ S₁
subsume-check p₀ p₁ (lam p) = {!!}
subsume-check p₀ p₁ (elim Δ⊢ρe∈S S≼T) = {!!}

-- subsume-infer : {!!}
