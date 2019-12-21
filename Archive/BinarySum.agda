{-# OPTIONS --without-K --exact-split --safe #-}
module Foundation.BinarySum where

open import Foundation.Universes
open import Foundation.Function using (type-of)

infix 1 _⊎_
data _⊎_ (A : 𝒰 ˙) (B : 𝒱 ˙) : 𝒰 ⊔ 𝒱 ˙ where
  inl : (x : A) → A ⊎ B
  inr : (x : B) → A ⊎ B

⊎-type : {X Y : 𝒰 ˙} (x : X ⊎ Y) → 𝒰 ˙
⊎-type (inl x) = type-of x
⊎-type (inr y) = type-of y
