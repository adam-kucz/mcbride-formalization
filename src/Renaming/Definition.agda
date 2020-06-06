{-# OPTIONS --exact-split --prop #-}
open import Basic
open import Universes

module Renaming.Definition
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {𝑆 : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Data.Nat
open import Syntax.Definition using (Var; new; old)

open import Proposition.Identity
open import Function

Ren : (m n : ℕ) → 𝒰₀ ˙
Ren m n = (v : Var m) → Var n

record Renameable (F : (m : ℕ) → 𝒮 ˙): 𝒮 ˙ where
  field
    rename : (ρ : Ren m n)(e : F m) → F n
    rename-id : rename (𝑖𝑑 (Var m)) == 𝑖𝑑 (F m)
    rename-∘ :
      (π : Ren n k)
      (ρ : Ren m n)
      → ------------------------------------
      rename (π ∘ ρ) == rename π ∘ rename ρ

open Renameable ⦃ … ⦄ public

{-# DISPLAY Renameable.rename R ρ = rename ρ #-}
{-# DISPLAY Renameable.rename-id R = rename-id #-}
{-# DISPLAY Renameable.rename-∘ R = rename-∘ #-}

shift :
  {F : (m : ℕ) → 𝒮 ˙}
  ⦃ ren : Renameable F ⦄
  (x : F m)
  → --------------------
  F (m +1)
shift = rename old

old× : (k : ℕ) → Ren m (k + m)
old× zero   v = v
old× (k +1) v = old (old× k v)

open import Proposition.Identity.Coercion
open import Operation.Binary

shift-by :
  {F : (m : ℕ) → 𝒮 ˙}
  ⦃ r : Renameable F ⦄
  (k : ℕ)
  (x : F m)
  → ------------------------------
  F (k + m)
shift-by {m = m} k = rename (old× k)

private
  idRen-right-suc× : ∀ {m} k → Ren m (m + k)
  idRen-left-suc× : ∀ {m} k → Ren m (k + m)

idRen-right-suc× k new = new
idRen-right-suc× {m +1} k (old v) = old (idRen-right-suc× k v)

idRen-left-suc× zero new = new
idRen-left-suc× (k +1) new = new
idRen-left-suc× zero (old v) = old v
idRen-left-suc×    1 (old v) = old (idRen-left-suc× 1 v)
idRen-left-suc× (k +2) (old v) =
  old (idRen-left-suc× (k +1) (idRen-left-suc× 1 v))

extend-by-right : ∀ {m}
  {F : (m : ℕ) → 𝒮 ˙}
  ⦃ _ : Renameable F ⦄
  (k : ℕ)
  (x : F m)
  → ------------------------------
  F (m + k)
extend-by-right k v = rename (idRen-right-suc× k) v

extend-by-left :
  {F : (m : ℕ) → 𝒮 ˙}
  ⦃ _ : Renameable F ⦄
  (k : ℕ)
  (x : F m)
  → ------------------------------
  F (k + m)
extend-by-left {m = m}{F} k v = rename (idRen-left-suc× k) v

extend :
  {F : (m : ℕ) → 𝒮 ˙}
  ⦃ _ : Renameable F ⦄
  (x : F m)
  → --------------------
  F (m +1)
extend = extend-by-left 1

