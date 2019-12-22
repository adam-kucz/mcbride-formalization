{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Structure.Monoid where

open import Foundation.Universes
open import Foundation.Operation.Binary
  renaming (ClosedOp to Op) hiding (Op)
open import Foundation.Operation.Binary.Property
  using (Commutative; comm)
open import Foundation.Prop'.Identity using (_==_; ap)
open import Foundation.Prop'.Function using (_$_)
open import Foundation.Structure.Semigroup using (Semigroup; assoc)

record Monoid {X : 𝒰 ˙} (_∙_ : Op X) : 𝒰 ˙ where
  field
    ⦃ semigroup ⦄ : Semigroup _∙_
    e : X
    ⦃ unit ⦄  : e IsUnitOf _∙_

open Monoid ⦃ ... ⦄ public hiding (semigroup)
