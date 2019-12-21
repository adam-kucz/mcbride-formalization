{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Relation.Binary.Instances where

open import Foundation.PropUniverses
open import Foundation.Relation.Binary

private
  module RelProp (property : RelProperty) where
    record Property {X : 𝒱 ˙} (R : Rel 𝒰 X X) : 𝒰 ⊔ 𝒱 ᵖ where
      field
        prop-name : property R

    open Property ⦃ ... ⦄ public

open RelProp transitive renaming (Property to Transitive; prop-name to trans) public
open RelProp reflexive renaming (Property to Reflexive; prop-name to refl) public
open RelProp irreflexive renaming (Property to Irreflexive; prop-name to irrefl) public
open RelProp symmetric renaming (Property to Symmetric; prop-name to sym) public
open RelProp antisymmetric renaming (Property to Antisymmetric; prop-name to antisym) public
open RelProp asymmetric renaming (Property to Asymmetric; prop-name to asym) public
open RelProp connex renaming (Property to Connex; prop-name to total) public

record Equivalence {X : 𝒱 ˙} (R : Rel 𝒰 X X) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    ⦃ equiv-reflexive ⦄ : Reflexive R
    ⦃ equiv-symmetric ⦄ : Symmetric R
    ⦃ equiv-transitive ⦄ : Transitive R

open Equivalence ⦃ ... ⦄ public

