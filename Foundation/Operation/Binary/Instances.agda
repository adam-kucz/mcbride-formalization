{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Operation.Binary.Instances where

open import Foundation.PropUniverses
open import Foundation.Operation.Binary

record Commutative {X : 𝒰 ˙} {Y : 𝒱 ˙} (op : Op X X Y) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    comm : commutative op

open Commutative ⦃ ... ⦄ public

