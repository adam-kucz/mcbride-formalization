{-# OPTIONS --exact-split --safe #-}
module Foundation.Type.Identity.Definition where

open import Foundation.Universes

data Id (X : 𝒰 ˙) : (Y : 𝒰 ˙) (x : X) (y : Y) → 𝒰 ˙ where
  instance refl : (x : X) → Id X X x x

infix 19 _≡_
_≡_ : {X Y : 𝒰 ˙}
  (x : X)
  (y : Y)
  → -------------
  𝒰 ˙
x ≡ y = Id _ _ x y

transport :
  (p : X ≡ Y)
  (x : X)
  → ----------
  Y
transport (refl _) x = x
