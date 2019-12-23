{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Structure.Semiring where

open import Foundation.Structure.Hemiring
open import Foundation.Structure.Monoid

open import Foundation.PropUniverses
open import Foundation.Operation.Binary
  renaming (ClosedOp to Op) hiding (Op)

record FormSemiring {X : 𝒰 ˙} (_+_ _*_ : Op X) (zero one : X) : 𝒰 ᵖ where
  field
    ⦃ hemiring ⦄ : FormHemiring _+_ _*_ zero
    ⦃ unit ⦄ : one IsUnitOf _*_

record Semiring {X : 𝒰 ˙} : 𝒰 ˙ where
  field
    _+_ _*_ : Op X
    zero one : X
    ⦃ def ⦄ : FormSemiring _+_ _*_ zero one

open Semiring ⦃ ... ⦄ public

instance
  DefaultSemiring : {plus times : Op X} {zero one : X}
    ⦃ _ : FormHemiring plus times zero ⦄
    ⦃ _ : one IsLeftUnitOf times ⦄
    ⦃ _ : one IsRightUnitOf times ⦄
    → -------------------
    FormSemiring plus times zero one
  DefaultSemiring = record {}
