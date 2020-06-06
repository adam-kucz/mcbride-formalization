{-# OPTIONS --exact-split --prop #-}
open import Basic
open import PropUniverses

module TypePreservation
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax
open import Context
open import Computation

open import Relation.Binary
open import Data.Nat

infix 36 _Γ⇝_
data _Γ⇝_ : ∀ {n} → BinRel (𝒰 ⁺ ⊔ 𝒱) (Context n) where
  · : · Γ⇝ ·

  _∥_,x:[_] :  ∀ {n}
    (Δ : Context n)
    (π : R)
    {A A'}
    (p : A ⇝ A')
    → --------------
    Δ ∥ π ,x: A  Γ⇝ Δ ∥ π ,x: A'

  [_]∥_,x:_ :  ∀ {n Δ Δ'}
    (p : Δ Γ⇝ Δ')
    (ρ : R)
    (A : Term (n +2))
    → --------------
    Δ ∥ ρ ,x: A  Γ⇝ Δ' ∥ ρ ,x: A

open import Relation.Binary.ReflexiveTransitiveClosure

infix 36 _Γ↠_
_Γ↠_ : ∀ {n} → BinRel (𝒰 ⁺ ⊔ 𝒱) (Context n)
_Γ↠_ = refl-trans-close _Γ⇝_

-- Theorem 35 (parallel preservation)

open import ParallelReduction
open import Judgment
open import Logic

parallel-∋-preserv : ∀{Δ Δ' : Context n}{T T' t t' π}
  (pΔ : Δ Γ↠ Δ')
  (pT : T ↠ T')
  (pt : t ▷ t')
  (q : Δ ⊢ π , T ∋ t)
  → --------------------------------------
  Δ' ⊢ π , T' ∋ t'
parallel-∈-preserv : ∀{Δ Δ' : Context n}{e e' S π}
  (pΔ : Δ Γ↠ Δ')
  (pe : e ▷ e')
  (q : Δ ⊢ π , e ∈ S)
  → --------------------------------------
  ∃ λ S' → S ↠ S' ∧ Δ' ⊢ π , e' ∈ S'

-- Corollary 36 (preservation)

open import Proof

∋-preserv : ∀{Δ Δ' : Context n}{T T' t t' π}
  (pΔ : Δ Γ↠ Δ')
  (pT : T ↠ T')
  (pt : t ↠ t')
  (q : Δ ⊢ π , T ∋ t)
  → --------------------------------------
  Δ' ⊢ π , T' ∋ t'
∋-preserv pΔ pT (rfl t) = parallel-∋-preserv pΔ pT (refl t)
∋-preserv {Δ = Δ}{T = T} pΔ pT (step t⇝t' t'↠t″) q =
  ∋-preserv pΔ pT t'↠t″ $
  parallel-∋-preserv (refl Δ) (refl T) (subrel t⇝t') q

∈-preserv : ∀{Δ Δ' : Context n}{e e' S π}
  (pΔ : Δ Γ↠ Δ')
  (pe : e ↠ e')
  (q : Δ ⊢ π , e ∈ S)
  → --------------------------------------
  ∃ λ S' → S ↠ S' ∧ Δ' ⊢ π , e' ∈ S'
∈-preserv pΔ (rfl e) = parallel-∈-preserv pΔ (refl e)
∈-preserv {Δ = Δ} pΔ (step e⇝e' e'↠e″) q
  with parallel-∈-preserv (refl Δ) (subrel e⇝e') q
∈-preserv {Δ = Δ} pΔ (step e⇝e' e'↠e″) q | S' , (S↠S' , Δ⊢π,e'∈S')
  with ∈-preserv pΔ e'↠e″ Δ⊢π,e'∈S'
∈-preserv {Δ = Δ} pΔ (step e⇝e' e'↠e″) q
  | S' , (S↠S' , Δ⊢π,e'∈S') | S″ , (S'↠S″ , Δ'⊢π,e″∈S″) =
  S″ , (trans S↠S' S'↠S″ , Δ'⊢π,e″∈S″)
