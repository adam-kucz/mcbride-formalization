{-# OPTIONS --without-K --exact-split --safe #-}
module Foundation.Type.BinarySum where

open import Foundation.Universes

infix 55 _+_
data _+_ (X : 𝒰 ˙) (Y : 𝒱 ˙) : 𝒰 ⊔ 𝒱 ˙ where
  inl : (x : X) → X + Y
  inr : (y : Y) → X + Y
