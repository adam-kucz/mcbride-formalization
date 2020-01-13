{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import Basic
open import Universes

module Renaming.Definition
  {R : 𝒰 ˙} ⦃ r : Rig R ⦄
  {𝑆 : 𝒱 ˙} ⦃ _ : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Data.Nat
open import Syntax using (Var; new; old)

Ren : (m n : ℕ) → 𝒰₀ ˙
Ren m n = (v : Var m) → Var n

open import Liftable

instance
  LiftableRen : Liftable Ren
  lift ⦃ LiftableRen ⦄ _ new = new
  lift ⦃ LiftableRen ⦄ ρ (old v) = old (ρ v)

record Renameable (F : (m : ℕ) → 𝒮 ˙): 𝒮 ˙ where
  field
    rename : ∀ {m n} (ρ : Ren m n) (x : F m) → F n

open Renameable ⦃ … ⦄ public

shift : ∀ {m}
  {F : (m : ℕ) → 𝒮 ˙}
  ⦃ _ : Renameable F ⦄
  (x : F m)
  → --------------------
  F (suc m)
shift = rename old

shift-by : ∀ {m}
  {F : (m : ℕ) → 𝒮 ˙}
  ⦃ _ : Renameable F ⦄
  (k : ℕ)
  (x : F m)
  → ------------------------------
  F (k + m)
shift-by zero x = x
shift-by (suc k) x = shift (shift-by k x)

extend : ∀ {m}
  {F : (m : ℕ) → 𝒮 ˙}
  ⦃ _ : Renameable F ⦄
  (x : F m)
  → --------------------
  F (suc m)
extend = rename idRen-suc
  where idRen-suc : ∀ {m} → Ren m (suc m)
        idRen-suc new = new
        idRen-suc (old v) = old (idRen-suc v)

extend-by : ∀ {m}
  {F : (m : ℕ) → 𝒮 ˙}
  ⦃ _ : Renameable F ⦄
  (k : ℕ)
  (x : F m)
  → ------------------------------
  F (k + m)
extend-by zero x = x
extend-by (suc k) x = extend (extend-by k x)
