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

open import Logic
open import Proof

infixl 30 _ctx-≼_
_ctx-≼_ : Rel (𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲) (Context n) (Context n)
· ctx-≼ · = Lift𝒰ᵖ ⊤
(Γ ∥ ρ₀ ,x: S₀) ctx-≼ (Δ ∥ ρ₁ ,x: S₁) = Γ ctx-≼ Δ ∧ ρ₀ == ρ₁ ∧ S₀ ≼ S₁
-- note: need ρ₀ == ρ₁ to make thm 22 work

subsume-check : {ρ : R}{S s T : Term n}
  (p₀ : Δ' ctx-≼ Δ)
  (p₁ : S ≼ T)
  (q : Δ ⊢ ρ , S ∋ s)
  → ----------------------------
  Δ' ⊢ ρ , T ∋ s
subsume-infer : {ρ : R}{S : Term n}{e : Elim n}
  (p₀ : Δ' ctx-≼ Δ)
  (q : Δ ⊢ ρ , e ∈ S)
  → ----------------------------
  ∃ λ S' → S' ≼ S ∧ Δ' ⊢ ρ , e ∈ S'

open import Relation.Binary
open import Subtyping.Preservation

ctx-≼-ctx₀ : ∀{Γ}
  (Δ' : Precontext n)
  (π : R)
  (p : Γ ctx-≼ ctx Δ' π)
  → ----------------------------------------
  ∃ λ Γ' → Γ == ctx Γ' π
ctx-≼-ctx₀ {Γ = ·} · π p = · , refl ·
ctx-≼-ctx₀ {Γ = Γ ∥ π ,x: S}
  (Δ' ∥x: S') π (Γctx-≼ctxΔ'π , Id.refl π , _)
  with Γ' , Id.refl .(ctx Γ' π) ← ctx-≼-ctx₀ Δ' π Γctx-≼ctxΔ'π =
  Γ' ∥x: S , refl (ctx Γ' π ∥ π ,x: S)

subsume-check p₀ p₁ (pre p T⇝R) with step-↠-preserves-≼ p₁ (subrel T⇝R)
subsume-check p₀ p₁ (pre {R = R} q T⇝R) | R' , (R≼R' , T↠R') =
  iter-pre (subsume-check p₀ R≼R' q) T↠R'
subsume-check p₀ (refl≼ (⋆ i)) (sort p)
  with Δ , Id.refl _ ← ctx-≼-ctx₀ _ _ p₀ = sort p
subsume-check p₀ (sort p₁) (sort q)
  with Δ , Id.refl _ ← ctx-≼-ctx₀ _ _ p₀ = sort $ trans p₁ q
subsume-check p₀ p₁ (fun π Γ⊢₀*ᵢ∋S Γ,x:S⊢₀*ᵢ∋T) = {!!}
  -- {!Γ,x:S⊢₀*ᵢ∋T !}
  -- goal                      : ctx Γ 0 ⊢ 0 , T ∋ [ π x: S₁ ]→ T₁
  -- fun π Γ⊢₀*ᵢ∋S Γ,x:S⊢₀*ᵢ∋T : ctx Γ 0 ⊢ 0 , ⋆ i ∋ [ π x: S₁ ]→ T₁
  -- subsume-check Γ⊢₀*ᵢ∋S q   : ctx Γ 0 ⊢ 0 , T ∋ S₁
subsume-check p₀ p₁ (lam p) = {!!}
subsume-check p₀ p₁ (elim Δ⊢ρe∈S S≼T) = {!!}

open import Proposition.Sum

ctx-≼-pt+ :
  {Δ₀ Δ₁ Δ' : Context n}
  (compat : compatible Δ₀ Δ₁)
  (Δ'≼Δ₀+Δ₁ : Δ' ctx-≼ Δ₀ pt+ Δ₁ [ compat ])
  → ----------------------------------------
  ∃ λ Δ'₀ → ∃ λ Δ'₁ →
  compatible Δ'₀ Δ'₁ ∧ᵈ λ p →
  Δ' == Δ'₀ pt+ Δ'₁ [ p ] ∧
  Δ'₀ ctx-≼ Δ₀ ∧ Δ'₁ ctx-≼ Δ₁
ctx-≼-pt+ {Δ₀ = ·}{·}{·} compat Δ'≼Δ₀+Δ₁ =
  · , (· , (from-instance , (refl · , from-instance , from-instance)))
ctx-≼-pt+ {Δ₀ = Δ₀ ∥ ρ₀ ,x: S} {Δ₁ ∥ ρ₁ ,x: S} {Δ' ∥ .(ρ₁ Rig.+ ρ₀) ,x: S'}
  (compat , Id.refl S) (Δ'≼Δ₀+Δ₁ , Id.refl .(ρ₁ Rig.+ ρ₀) , S'≼S)
  with Δ'₀ , (Δ'₁ , (compat' , (Id.refl _ , Δ'₀≼Δ₀ , Δ'₁≼Δ₁))) ←
       ctx-≼-pt+ compat Δ'≼Δ₀+Δ₁ = 
  Δ'₀ ∥ ρ₀ ,x: S' , (Δ'₁ ∥ ρ₁ ,x: S' , (
  compat' , refl S' , (
  refl _ , (Δ'₀≼Δ₀ , refl ρ₀ , S'≼S) , (Δ'₁≼Δ₁ , refl ρ₁ , S'≼S))))

import Substitution
open Substitution.WithInstanceArgs ⦃ subst = Substitution.SubstitutableExpr ⦄
-- open import Subtyping.Stability

subsume-infer p₀ (post q S⇝R) = {!!}
subsume-infer p₀ (var Γ ρ S) = {!!}
subsume-infer p₀ (weaken q) = {!!}
subsume-infer p₀ (app {Δ₀ = Δ₀}{Δ₁}{T}{S}{s} compat Δ₀⊢ρf∈[πx:S]→T Δ₁⊢ρπS∋s)
  with Δ'₀ , (Δ'₁ , (compat' , (Id.refl _ , Δ'₀≼Δ₀ , Δ'₁≼Δ₁))) ←
       ctx-≼-pt+ compat p₀
  with subsume-infer Δ'₀≼Δ₀ Δ₀⊢ρf∈[πx:S]→T
... | _ , (refl≼ _ , Δ'₀⊢ρf∈e) =
  T [ s ꞉ S /new] , (
  refl (T [ s ꞉ S /new])  ,
  app compat' Δ'₀⊢ρf∈e $ subsume-check Δ'₁≼Δ₁ (refl S) Δ₁⊢ρπS∋s)
... | _ , ([_x:_]→_ π {S₁}{S}{T₁}{T} S≼S₁ T₁≼T , Δ'₀⊢ρf∈e) =
  T₁ [ s ꞉ S₁ /new] , (
  ≼-stable s (z≤ _) T₁≼T S≼S₁ ,
  app compat' Δ'₀⊢ρf∈e $ subsume-check Δ'₁≼Δ₁ S≼S₁ Δ₁⊢ρπS∋s )
            
subsume-infer p₀ (cut ⌊Δ⌋⊢₀*ᵢ∋S Δ⊢₀ρS∋s) = {!!}
