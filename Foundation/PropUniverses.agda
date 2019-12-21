{-# OPTIONS --without-K --exact-split --safe --prop #-}
module Foundation.PropUniverses where

open import Foundation.Universes public

infix 1 _ᵖ
_ᵖ : ∀ 𝒰 → Set (𝒰 ⁺)
𝒰 ᵖ = Prop 𝒰

variable
  𝑋 𝑌 𝑍 𝑊 : 𝒰 ᵖ
  

