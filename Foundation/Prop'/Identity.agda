{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Prop'.Identity where

open import Foundation.PropUniverses
open import Foundation.Logic using (¬_)

open import Foundation.Prop'.Identity.Definition public

ap : {x y : X}
  (f : (x : X) → A x)
  (p : x == y)
  → -----------
  f x == f y
ap f (refl x) = refl (f x)

infix 19 _≠_
_≠_ : {X Y : 𝒰 ˙}
  (x : X)
  (y : Y)
  → -------------
  𝒰 ᵖ
x ≠ y = ¬ x == y

