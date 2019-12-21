{-# OPTIONS --without-K --exact-split --safe --prop #-}
module Foundation.Prop'.Sum where

open import Foundation.PropUniverses

infix 11 _,_
data Σₚ {X : 𝒰 ˙} (𝐴 : (x : X) → 𝒱 ᵖ) : 𝒰 ⊔ 𝒱 ˙ where
  _,_ : (elem : X) (p : 𝐴 elem) → Σₚ 𝐴

data ∃ {X : 𝒰 ˙} (𝐴 : (x : X) → 𝒱 ᵖ) : 𝒰 ⊔ 𝒱 ᵖ where
  _,_ : (elem : X) (p : 𝐴 elem) → ∃ 𝐴

infixl 17 _∧_
record _∧_ (𝑋 : 𝒰 ᵖ) (𝑌 : 𝒱 ᵖ) : 𝒰 ⊔ 𝒱 ᵖ where
  constructor _,_
  field
    left : 𝑋
    right : 𝑌 

open _∧_ public
