{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Function.Property where

open import Foundation.PropUniverses
open import Foundation.Prop'.Identity.Definition using (_==_; refl)
open import Foundation.Function
open import Foundation.Function.Equivalence

involutive : {X : 𝒰 ˙} (f : (x : X) → X) → 𝒰 ᵖ
involutive f = ∀ x → f (f x) == x

record Involutive {X : 𝒰 ˙} (f : (x : X) → X) : 𝒰 ᵖ where
  field
    invol : involutive f

open Involutive ⦃ ... ⦄ public

injective : {X : 𝒰 ˙} {Y : 𝒱 ˙} (f : (x : X) → Y) → 𝒰 ⊔ 𝒱 ᵖ
injective f = ∀ {x y} (p : f x == f y) → x == y

record Injective {X : 𝒰 ˙} {Y : 𝒱 ˙} (f : (x : X) → Y) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    inj : injective f

open Injective ⦃ ... ⦄ public

invertible : {X : 𝒰 ˙} {Y : 𝒱 ˙} (f : (x : X) → Y) → 𝒰 ⊔ 𝒱 ᵖ
invertible f = ∃ λ g → g ∘ f ~ id ∧ f ∘ g ~ id
  where open import Foundation.Prop'.Sum using (∃; _∧_)
