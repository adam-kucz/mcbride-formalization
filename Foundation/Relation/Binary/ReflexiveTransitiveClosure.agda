{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Relation.Binary.ReflexiveTransitiveClosure where

open import Foundation.PropUniverses
open import Foundation.Relation.Binary using (Rel)
open import Foundation.Relation.Binary.Instances
  using (Reflexive; refl; Transitive; trans)

data refl-trans-close {X : 𝒰 ˙} (R : Rel 𝒱 X X) : (a b : X) → 𝒰 ⊔ 𝒱 ᵖ where
  rfl : ∀ a → refl-trans-close R a a
  step : ∀ {a b c} → (p : refl-trans-close R a b) (s : R b c) → refl-trans-close R a c

instance
  TransitiveRelation-rtc : {R : Rel 𝒰 X X} → Transitive (refl-trans-close R)
  trans ⦃ TransitiveRelation-rtc ⦄ p (rfl a) = p
  trans ⦃ TransitiveRelation-rtc ⦄ p (step q s) = step (trans p q) s

  ReflexiveRelation-rtc : {R : Rel 𝒰 X X} → Reflexive (refl-trans-close R)
  refl ⦃ ReflexiveRelation-rtc ⦄ = rfl

