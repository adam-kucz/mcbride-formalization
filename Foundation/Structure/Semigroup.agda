{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Structure.Semigroup where

open import Foundation.PropUniverses
open import Foundation.Operation.Binary using (ClosedOp; Associative)

FormSemigroup : {X : 𝒰 ˙} (_∙_ : ClosedOp X) → 𝒰 ᵖ
FormSemigroup = Associative

record Semigroup (X : 𝒰 ˙) : 𝒰 ˙ where
  infixl 130 _∙_
  field
    _∙_ : ClosedOp X
    ⦃ def ⦄ : FormSemigroup _∙_

open Semigroup ⦃ ... ⦄ public
