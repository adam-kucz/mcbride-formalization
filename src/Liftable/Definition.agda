{-# OPTIONS --exact-split --prop #-}
open import Basic
open import Universes

module Liftable.Definition
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Renaming.Definition
open import Syntax.Definition

open import Type.BinarySum renaming (_+_ to _⊎_)
open import Function

permute : ∀ {m n k k'}
  ⦃ _ : Renameable A ⦄
  (h : Var k → Var m ⊎ A k')
  (g : Ren n k')
  (f : Var m → A n)
  → ------------------
  Var k → A k'
permute h g f = [ rename g ∘ f , id ] ∘ h

open import Data.Nat
open import Proposition.Identity

record Liftable (F : (m : ℕ) → 𝒳 ˙) : 𝒳 ˙ where
  field
    ⦃ ren ⦄ : Renameable F
    default-new : F 1

  default : ∀ {m}(v : Var m) → F m
  default {m +1} new =  extend-by-right m default-new
  default {m +2}(old v) = shift (default v)

  module Selector where
    without_new : ∀ k {m n}(v : Var (k + m)) → Var m ⊎ F (k + n)
    without zero new = inl
    without _ +1 new new = inr (default new)
    without k +1 new (old v) = [ id + shift ] (without k new v)

  open Selector

  lift-by : ∀ {m n} k
    (σ : Var m → F n)
    → ---------------------
    (v : Var (k + m)) → F (k + n)
  lift-by k = permute (without k new) (old× k)
  -- λ σ v → [ rename (old× k) ∘ σ , id ] (without k new v)

  lift : ∀ {m n}
    (σ : Var m → F n)
    → ---------------------
    (v : Var (m +1)) → F (n +1)
  lift = lift-by 1

  Liftable== : ∀ {m m' n n'}
    (p : m == m')
    (q : n == n')
    → ---------------------
    (Var n → F m) == (Var n' → F m')
  Liftable== (refl m) (refl n) = refl (Var n → F m)

open Liftable ⦃ … ⦄ public

{-# DISPLAY Liftable.lift L = lift #-}
{-# DISPLAY Liftable.lift-by L = lift-by #-}
{-# DISPLAY Liftable.Liftable== L = Liftable== #-}

