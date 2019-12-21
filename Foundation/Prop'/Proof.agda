{-# OPTIONS --without-K --exact-split --safe --prop #-}
module Foundation.Prop'.Proof where

open import Foundation.PropUniverses

infix 4 have_:from:_
have_:from:_ : (𝑋 : 𝒰 ᵖ) (p : 𝑋) → 𝑋
have _ :from: p = p

infixl 3 _⟶_:by:_
_⟶_:by:_ : (p : 𝑋) (𝑌 : 𝒱 ᵖ) (p→q : 𝑋 → 𝑌) → 𝑌
p ⟶ _ :by: p→q = p→q p

