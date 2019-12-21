{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Prop'.Identity.Definition where

open import Foundation.PropUniverses

data Idₚ (X : 𝒰 ˙) : (Y : 𝒰 ˙) (x : X) (y : Y) → 𝒰 ᵖ where
  instance refl : (x : X) → Idₚ X X x x

infix 19 _==_
_==_ : {X Y : 𝒰 ˙}
  (x : X)
  (y : Y)
  → -------------
  𝒰 ᵖ
x == y = Idₚ _ _ x y

lhs : {X Y : 𝒰 ˙} {x : X} {y : Y} (p : x == y) → X
rhs : {X Y : 𝒰 ˙} {x : X} {y : Y} (p : x == y) → Y

lhs {x = x} _ = x
rhs {y = y} _ = y
