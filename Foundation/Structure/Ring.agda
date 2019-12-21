{-# OPTIONS --prop  #-}
module Foundation.Structure.Ring where

open import Foundation.Universes
open import Foundation.Structure.Semiring using (Semiring)
open import Foundation.Structure.Group using (Group)
open import Foundation.Operation.Binary renaming (ClosedOp to Op) using ()

record Ring {X : 𝒰 ˙} (_+_ _*_ : Op X) : 𝒰 ˙ where
  field
    ⦃ semiring ⦄ : Semiring _+_ _*_
    ⦃ group+ ⦄ : Group _+_
