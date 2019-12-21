{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Structure.Monoid where

open import Foundation.Universes
open import Foundation.Operation.Binary
  renaming (ClosedOp to Op) hiding (Op)
open import Foundation.Operation.Binary.Instances
  using (Commutative; comm)
open import Foundation.Prop'.Identity using (_==_; ap)
open import Foundation.Prop'.Function using (_$_)
open import Foundation.Structure.Semigroup using (Semigroup; assoc)

record Monoid {X : 𝒰 ˙} (_∙_ : Op X) : 𝒰 ˙ where
  field
    ⦃ semigroup ⦄ : Semigroup _∙_
    e : X
    left-unit : e is-left-unit-of _∙_
    right-unit : e is-right-unit-of _∙_

open Monoid ⦃ ... ⦄ public hiding (semigroup)

swap : {_∙_ : Op X}
  ⦃ _ : Monoid _∙_ ⦄
  ⦃ _ : Commutative _∙_ ⦄
  (x y z : X)
  → ------------------------
  x ∙ (y ∙ z) == y ∙ (x ∙ z)
swap {_∙_ = _∙_} x y z =
  proof x ∙ (y ∙ z)
      〉 _==_ 〉 (x ∙ y) ∙ z :by: assoc x y z
      〉 _==_ 〉 (y ∙ x) ∙ z :by: ap (_∙ z) (comm x y)
      〉 _==_ 〉 y ∙ (x ∙ z) :by: sym $ assoc y x z
  qed
  where open import Foundation.Proof
        open import Foundation.Prop'.Identity.Instances
        open import Foundation.Relation.Binary.Instances

