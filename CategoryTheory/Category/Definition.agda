{-# OPTIONS --exact-split --safe --prop #-}
module CategoryTheory.Category.Definition where

open import Foundation.PropUniverses
open import Foundation.Prop'.Identity using (_==_)
open import Foundation.Logic

record Category (𝒰 𝒱 : Universe) : 𝒰 ⁺ ⊔ 𝒱 ⁺ ˙ where
  infixl 25 _∘_
  field
    obj : 𝒰 ˙
    _~>_ : (X Y : obj) → 𝒱 ˙
    id : ∀ X → X ~> X
    _∘_ : ∀ {X Y Z} → (g : Y ~> Z) (f : X ~> Y) → X ~> Z
    left-unit : ∀ {X Y} (f : X ~> Y) → id Y ∘ f == f
    right-unit : ∀ {X Y} (f : X ~> Y) → f ∘ id X == f
    assoc : ∀ {X Y Z W}
      (h : Z ~> W)
      (g : Y ~> Z)
      (f : X ~> Y)
      → -----------------------------
      h ∘ (g ∘ f) == (h ∘ g) ∘ f

open Category ⦃ ... ⦄ public

dom : ⦃ _ : Category 𝒰 𝒱 ⦄ {X Y : obj} (f : X ~> Y) → obj
dom {X = X} _ = X

cod : ⦃ _ : Category 𝒰 𝒱 ⦄ {X Y : obj} (f : X ~> Y) → obj
cod {Y = Y} _ = Y

iso : ⦃ _ : Category 𝒰 𝒱 ⦄ {X Y : obj} (f : X ~> Y) → 𝒱 ᵖ
iso {X = X} {Y = Y} f = ∃ λ (g : Y ~> X) → f ∘ g == id Y ∧ g ∘ f == id X
