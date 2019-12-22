{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Structure.Semigroup where

open import Foundation.PropUniverses

open import Foundation.Operation.Binary as BinOp using (ClosedOp; Associative)
open BinOp using (assoc) public

Semigroup : {X : 𝒰 ˙} (_∙_ : ClosedOp X) → 𝒰 ᵖ
Semigroup = Associative
