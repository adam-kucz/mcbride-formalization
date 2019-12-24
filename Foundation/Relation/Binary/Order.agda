{-# OPTIONS --exact-split --safe --prop #-}
open import Foundation.PropUniverses renaming (_⊔_ to _⨿_)
open import Foundation.Relation.Binary.Definition

module Foundation.Relation.Binary.Order {X : 𝒰 ˙} (_⊑_ : Rel 𝒱 X X) where
  record Bottom (⊥ : X) : 𝒰 ⨿ 𝒱 ˙ where
    field
      bot : ∀ x → ⊥ ⊑ x

  open Bottom ⦃ ... ⦄ public

  
