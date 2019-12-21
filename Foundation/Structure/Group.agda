{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Structure.Group where

open import Foundation.Universes

open import Foundation.Operation.Binary
  renaming (ClosedOp to Op) hiding (Op)
open import Foundation.Prop'.Identity using (_==_)
open import Foundation.Logic using (∃; _∧_)
open import Foundation.Structure.Monoid using (Monoid; e)

record Group {X : 𝒰 ˙} (_∙_ : Op X) : 𝒰 ˙ where
  field
    ⦃ monoid ⦄ : Monoid _∙_
    ∃inverse : ∀ x → ∃ λ y → x ∙ y == e ∧ y ∙ x == e

open Group ⦃ ... ⦄ public hiding (monoid)
