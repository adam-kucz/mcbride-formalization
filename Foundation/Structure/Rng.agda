{-# OPTIONS --prop  #-}
module Foundation.Structure.Rng where

open import Foundation.Universes
open import Foundation.Structure.Hemiring using (Hemiring)
open import Foundation.Structure.Group using (Group)
open import Foundation.Operation.Binary renaming (ClosedOp to Op) using ()

record Rng {X : 𝒰 ˙} (_+_ _*_ : Op X) : 𝒰 ˙ where
  field
    ⦃ hemiring ⦄ : Hemiring _+_ _*_
    {{group+}} : Group _+_
