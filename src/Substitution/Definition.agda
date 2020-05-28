{-# OPTIONS --exact-split --prop #-}
open import Basic using (Rig; wfs)
open import PropUniverses

module Substitution.Definition
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax ⦃ rig ⦄ ⦃ wfs ⦄
open import Renaming

open import Data.Nat hiding (_⊔_)
open import Function hiding (_$_)
open import Proof

open import Substitution.Basic using (Sub; _⍟_; newSub; nthSub) public

record Substitutable (F : (m : ℕ) → 𝒮 ˙) : 𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒮 ˙ where
  field
    sub : (σ : Sub m n)(e : F m) → F n
    ⦃ ren ⦄ : Renameable F
    rename-as-sub : (ρ : Ren m n) → rename ρ == sub (var ∘ ρ)
    sub-id : sub {m} var == id
    sub-∘ :
      (σ : Sub n k)
      (τ : Sub m n)
      → ------------------------------------
      sub σ ∘ sub τ == sub (σ ⍟ τ)

  infix 180 _[_/new] _[_/_[_]]
  _[_/new] : (e : F (n +1))(f : Elim n) → F n
  e [ f /new] = sub (newSub f) e
  
  _[_/_[_]] :
    (e : F (n +1))
    (f : Elim n)
    (m : ℕ)
    (p : m < n +1)
    → -------------------------------------------------------------
    F n
  e [ f / m [ p ]] = sub (nthSub m p f) e

module WithInstanceArgs {F : ℕ → 𝒮 ˙} ⦃ subst : Substitutable F ⦄ where
  open Substitutable subst hiding (ren) public

DirectSubstitutable : 
  {F : (m : ℕ) → 𝒮 ˙}
  (sub : ∀{m n}(σ : Sub m n)(e : F m) → F n)
  (sub-id : ∀{m} → sub {m} var == id)
  (sub-∘ : ∀{m n k} → (σ : Sub n k)(τ : Sub m n) → sub σ ∘ sub τ == sub (σ ⍟ τ))
  → ---------------------------------------------------------------------------
  Substitutable F

open import Axiom.FunctionExtensionality

Substitutable.sub (DirectSubstitutable sub sub-id sub-∘) = sub
Substitutable.sub-id (DirectSubstitutable sub sub-id sub-∘) = sub-id
Substitutable.sub-∘ (DirectSubstitutable sub sub-id sub-∘) = sub-∘
rename ⦃ Substitutable.ren (DirectSubstitutable sub sub-id sub-∘) ⦄ ρ =
  sub (var ∘ ρ)
rename-id ⦃ Substitutable.ren (DirectSubstitutable sub sub-id sub-∘) ⦄ = sub-id
rename-∘ ⦃ Substitutable.ren (DirectSubstitutable sub sub-id sub-∘) ⦄ π ρ =
  proof sub (var ∘ (π ∘ ρ))
    === sub ((var ∘ π) ⍟ (var ∘ ρ))
      :by: ap sub (subrel {_P_ = _==_} $ fun-ext $ λ v →
           Het.refl (var (π (ρ v))))
    === sub (var ∘ π) ∘ sub (var ∘ ρ)
      :by: sym $ sub-∘ (var ∘ π) (var ∘ ρ)
  qed
Substitutable.rename-as-sub (DirectSubstitutable sub sub-id sub-∘) _ = Id-refl _
