{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Prop'.Identity.Instances where

open import Foundation.PropUniverses
open import Foundation.Relation.Binary.Instances public
open import Foundation.Prop'.Identity.Definition hiding (refl) public

instance
  Transitive== : Transitive {𝒱 = 𝒱} {X = X} _==_
  trans ⦃ Transitive== ⦄ p (Idₚ.refl x) = p

  Reflexive== : Reflexive {𝒱 = 𝒱} {X = X} _==_
  refl ⦃ Reflexive== ⦄ = Idₚ.refl

  Symmetric== : Symmetric {𝒱 = 𝒱} {X = X} _==_
  sym ⦃ Symmetric== ⦄ (Idₚ.refl x) = refl x
  
  Equivalence== : Equivalence {𝒱 = 𝒱} {X = X} _==_
  equiv-reflexive ⦃ Equivalence== ⦄ = Reflexive==
  equiv-symmetric ⦃ Equivalence== ⦄ = Symmetric==
  equiv-transitive ⦃ Equivalence== ⦄ = Transitive==
