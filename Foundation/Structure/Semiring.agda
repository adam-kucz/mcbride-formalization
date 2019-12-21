{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Structure.Semiring where

open import Foundation.Universes
open import Foundation.Structure.Hemiring using (Hemiring)
open import Foundation.Structure.Monoid using (Monoid)
open import Foundation.Operation.Binary renaming (ClosedOp to Op) using ()

record Semiring {X : 𝒰 ˙} (_+_ _*_ : Op X) : 𝒰 ˙ where
  field
    {{hemiring}} : Hemiring _+_ _*_
    {{monoid*}} : Monoid _*_

