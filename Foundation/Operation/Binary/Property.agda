{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Operation.Binary.Property where

open import Foundation.PropUniverses
open import Foundation.Operation.Binary.Definition

open import Foundation.Prop'.Identity using (_==_)

record Commutative {X : 𝒰 ˙} {Y : 𝒱 ˙} (_∙_ : Op X X Y) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    comm : ∀ x y → x ∙ y == y ∙ x

open Commutative ⦃ ... ⦄ public

record Associative {X : 𝒰 ˙} (_∙_ : ClosedOp X) : 𝒰 ᵖ where
  field
    assoc : ∀ x y z → x ∙ (y ∙ z) == (x ∙ y) ∙ z

open Associative ⦃ ... ⦄ public

swap : {_∙_ : ClosedOp X}
  ⦃ _ : Associative _∙_ ⦄
  ⦃ _ : Commutative _∙_ ⦄
  (x y z : X)
  → ------------------------
  x ∙ (y ∙ z) == y ∙ (x ∙ z)
swap {_∙_ = _∙_} x y z =
  proof x ∙ (y ∙ z)
      〉 _==_ 〉 (x ∙ y) ∙ z :by: assoc x y z
      〉 _==_ 〉 (y ∙ x) ∙ z :by: ap (_∙ z) (comm x y)
      〉 _==_ 〉 y ∙ (x ∙ z) :by: sym (assoc y x z)
  qed
  where open import Foundation.Proof
        open import Foundation.Prop'.Identity using (ap)
        open import Foundation.Relation.Binary.Property using (sym)

record _IsLeftUnitOf_ {X : 𝒰 ˙} {Y : 𝒱 ˙} (e : X) (_∙_ : Op X Y Y) : 𝒱 ᵖ where
  field
    left-unit : ∀ y → e ∙ y == y

open _IsLeftUnitOf_ ⦃ ... ⦄ public

record _IsRightUnitOf_ {X : 𝒰 ˙} {Y : 𝒱 ˙} (e : X) (_∙_ : Op Y X Y) : 𝒱 ᵖ where
  field
    right-unit : ∀ y → y ∙ e == y

open _IsRightUnitOf_ ⦃ ... ⦄ public

open import Foundation.Logic using (⊥)

record _IsUnitOf_ {X : 𝒰 ˙} (e : X) (op : Op X X X) : 𝒰 ᵖ where
  field
    implicit : ⊥ → ⊥
    ⦃ unit-left ⦄ : e IsLeftUnitOf op
    ⦃ unit-right ⦄ : e IsRightUnitOf op

open _IsUnitOf_ ⦃ ... ⦄ public

instance
  DefaultUnit :
    {e : X}
    {op : Op X X X}
    ⦃ _ : e IsLeftUnitOf op ⦄
    ⦃ _ : e IsRightUnitOf op ⦄
    → -------------------------
    e IsUnitOf op
  implicit ⦃ DefaultUnit ⦄ ()

open import Foundation.Proof

right-unit-of-commutative-left-unit :
  {X : 𝒰 ˙} (e : X) (op : Op X X X)
  ⦃ _ : Commutative op ⦄
  ⦃ _ : e IsLeftUnitOf op ⦄
  → --------------------------
  e IsRightUnitOf op
right-unit ⦃ right-unit-of-commutative-left-unit e _∙_ ⦄ a =
  proof a ∙ e
    〉 _==_ 〉 e ∙ a :by: comm a e
    〉 _==_ 〉 a     :by: left-unit a
  qed
     
left-unit-of-commutative-right-unit :
  {X : 𝒰 ˙} (e : X) (op : Op X X X)
  ⦃ _ : Commutative op ⦄
  ⦃ _ : e IsRightUnitOf op ⦄
  → --------------------------
  e IsLeftUnitOf op
left-unit ⦃ left-unit-of-commutative-right-unit e _∙_ ⦄ a =
  proof e ∙ a
    〉 _==_ 〉 a ∙ e :by: comm e a
    〉 _==_ 〉 a     :by: right-unit a
  qed
