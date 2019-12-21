{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Function.Equivalence where

open import Foundation.PropUniverses
open import Foundation.Function
open import Foundation.Prop'.Identity.Definition using (_==_; refl)

infix 19 _~_
_~_ : {X : 𝒰 ˙} {A B : (x : X) → 𝒱 ˙}
  (f : Π A) (g : Π B)
  → -----------------
  (𝒰 ⊔ 𝒱) ᵖ
f ~ g = ∀ x → f x == g x

left-unit : {X : 𝒰 ˙} {A : (x : X) → 𝒱 ˙}
  (f : Π A)
  → -----------------
  id ∘ f == f
left-unit = refl

right-unit : {X : 𝒰 ˙} {A : (x : X) → 𝒱 ˙}
  (f : Π A)
  → -----------------
  f ∘ id == f
right-unit = refl
