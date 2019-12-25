{-# OPTIONS --exact-split --prop #-}
module Foundation.Type.Identity.Equivalence where

open import Foundation.Type.Identity.Definition

open import Foundation.Universes
open import Foundation.Prop'.Identity.Definition

≡→== : {x : X} {y : Y}
  (id : x ≡ y)
  → ------------
  x == y
≡→== (refl x) = refl x

postulate
  ==→≡ : {x : X} {y : Y}
    (p : x == y)
    → ------------
    x ≡ y

transport== : (p : X == Y) (x : X) → Y
transport== p x with ==→≡ p
transport== p x | refl X = x
