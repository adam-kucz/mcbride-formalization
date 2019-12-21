{-# OPTIONS --without-K --exact-split --safe #-}
module Foundation.Type.Sum where

open import Foundation.Universes

infix 55 _,_
record Σ {X : 𝒰 ˙} (A : (x : X) → 𝒱 ˙) : 𝒰 ⊔ 𝒱 ˙ where
  constructor _,_
  field
    pr₁ : X
    pr₂ : A pr₁

infix 50 _×_
_×_ : (X : 𝒰 ˙) (Y : 𝒱 ˙) → 𝒰 ⊔ 𝒱 ˙
X × Y = Σ λ (_ : X) → Y

open Σ public
