{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Operation.Binary where

open import Foundation.PropUniverses

open import Foundation.Prop'.Identity.Definition using (_==_)
open import Foundation.Prop'.Sum using (Σₚ; _,_)
open import Foundation.Logic using (_∧_)

Op : (X : 𝒰 ˙) (Y : 𝒱 ˙) (Z : 𝒲 ˙) → 𝒰 ⊔ 𝒱 ⊔ 𝒲 ˙
Op X Y Z = (x : X) (y : Y) → Z

ClosedOp : (X : 𝒰 ˙) → 𝒰 ˙
ClosedOp X = Op X X X

commutative : {𝒰 𝒱 : Universe} {X : 𝒰 ˙} {Y : 𝒱 ˙} (_∙_ : Op X X Y) → 𝒰 ⊔ 𝒱 ᵖ
commutative _∙_ = ∀ x y → x ∙ y == y ∙ x

associative : {𝒰 : Universe} {X : 𝒰 ˙} (_∙_ : ClosedOp X) → 𝒰 ᵖ
associative _∙_ = ∀ x y z → x ∙ (y ∙ z) == (x ∙ y) ∙ z

_is-left-unit-of_  : {X : 𝒰 ˙} {Y : 𝒱 ˙} (e : X) (_∙_ : Op X Y Y) → 𝒱 ᵖ
e is-left-unit-of _∙_ = ∀ y → e ∙ y == y

_is-right-unit-of_  : {X : 𝒰 ˙} {Y : 𝒱 ˙} (e : Y) (_∙_ : Op X Y X) → 𝒰 ᵖ
e is-right-unit-of _∙_ = ∀ x → x ∙ e == x

_is-unit-of_ : {X : 𝒰 ˙} (e : X) (_∙_ : ClosedOp X) → 𝒰 ᵖ
e is-unit-of op = e is-left-unit-of op ∧ e is-right-unit-of op


