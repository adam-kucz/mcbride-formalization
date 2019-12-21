{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Structure.Semigroup where

open import Foundation.Universes

open import Foundation.Operation.Binary
  renaming (ClosedOp to Op) hiding (Op)

record Semigroup {X : 𝒰 ˙} (_∙_ : Op X) : 𝒰 ˙ where
  field
    assoc : associative _∙_

open Semigroup ⦃ ... ⦄ public
