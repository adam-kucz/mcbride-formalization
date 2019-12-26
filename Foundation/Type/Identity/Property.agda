{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Type.Identity.Property where

open import Foundation.Type.Identity.Definition

open import Foundation.Universes
open import Foundation.Prop'.Identity.Definition

≡→== : {x : X} {y : Y}
  (id : x ≡ y)
  → ------------
  x == y
≡→== (refl x) = refl x

trans : {x : X} {y : Y} {z : Z}
  (p : x ≡ y)
  (q : y ≡ z)
  → --------------
  x ≡ z
trans (refl _) q = q

transport== :
  (x : X)
  (p : X ≡ Y)
  → -----------------
  transport p x == x
transport== x (refl _) = refl x
