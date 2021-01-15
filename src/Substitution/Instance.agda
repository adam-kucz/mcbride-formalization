{-# OPTIONS --exact-split --prop #-}
open import Basic using (Rig; wfs)
open import PropUniverses

module Substitution.Instance
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Substitution.Definition
open WithInstanceArgs
open import Renaming.Instance

open import Data.Nat

instance
  SubstitutableFun :
    {F : (m : ℕ) → 𝒳 ˙}
    ⦃ s : Substitutable F ⦄
    → --------------------
    Substitutable (λ n → X → F n)

open import Syntax

open import Function hiding (_$_)
open import Proof

open import Axiom.FunctionExtensionality

Substitutable.ren (SubstitutableFun ⦃ s = s ⦄) = RenameableFun
sub ⦃ SubstitutableFun ⦄ σ f x = sub σ (f x)
sub-id ⦃ SubstitutableFun ⦃ s = s ⦄ ⦄ =
  proof (λ f x → sub var (f x))
    === (λ f x → f x)
      :by: ap (λ — → λ f x → — (f x)) (sub-id ⦃ subst = s ⦄)
    === id
      :by: Id.refl _
  qed
sub-∘ ⦃ SubstitutableFun ⦃ s = s ⦄ ⦄ σ τ =
  proof (λ f x → sub σ (f x)) ∘ (λ f x → sub τ (f x))
    === (λ f x → (sub σ ∘ sub τ) (f x))
      :by: Id.refl _
    === (λ f x → sub (σ ⍟ τ) (f x))
      :by: ap (λ — → λ f x → — (f x)) (sub-∘ ⦃ subst = s ⦄ σ τ)
  qed
rename-as-sub ⦃ SubstitutableFun ⦃ s = s ⦄ ⦄ ρ =
  subrel {sup = _==_} $ fun-ext λ σ → fun-ext λ x →
  ==→~ (rename-as-sub ⦃ subst = s ⦄ ρ) (σ x)

