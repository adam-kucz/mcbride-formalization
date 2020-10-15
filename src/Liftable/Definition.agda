{-# OPTIONS --exact-split --safe #-}
open import Basic
open import Universes

module Liftable.Definition
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Renaming.Definition
open import Syntax.Definition

open import Function

open import Data.Nat
open import Type.Identity

record Liftable (F : (m : ℕ) → 𝒳 ˙) : 𝒳 ˙ where
  field
    ⦃ ren ⦄ : Renameable F
    default-new : F 1

  default : ∀ {m} → F (m +1)
  default {m} = extend-by-right m default-new

  lift-by : ∀ {m n} k
    (σ : Var m → F n)
    → ---------------------
    (v : Var (k + m)) → F (k + n)
  lift-by zero = id
  lift-by (k +1) σ new = default
  lift-by (k +1) σ (old v) = shift $ lift-by k σ v

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

open Liftable ⦃ … ⦄ hiding (ren) public

{-# DISPLAY Liftable.lift L = lift #-}
{-# DISPLAY Liftable.lift-by L = lift-by #-}
{-# DISPLAY Liftable.Liftable== L = Liftable== #-}

