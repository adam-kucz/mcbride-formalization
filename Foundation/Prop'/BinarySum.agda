{-# OPTIONS --without-K --exact-split --safe --prop #-}
module Foundation.Prop'.BinarySum where

open import Foundation.PropUniverses

infixl 15 _∨_
data _∨_ (𝑋 : 𝒰 ᵖ) (𝑌 : 𝒱 ᵖ) : 𝒰 ⊔ 𝒱 ᵖ where
  left : (p : 𝑋) → 𝑋 ∨ 𝑌
  right : (q : 𝑌) → 𝑋 ∨ 𝑌

∨-contract : (p : 𝑋 ∨ 𝑋) → 𝑋
∨-contract (left p) = p
∨-contract (right q) = q
