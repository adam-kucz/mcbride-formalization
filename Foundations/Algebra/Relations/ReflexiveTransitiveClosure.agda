{-# OPTIONS --prop  #-}
module Foundations.Algebra.Relations.ReflexiveTransitiveClosure where

open import Foundations.Algebra.Relations.Classes
  using (Relation; ReflexiveRelation; rflx; TransitiveRelation; trans)
open import Foundations.Univ using (Level; lsuc; _⊔_; 𝑙; 𝑚)

private
  variable
    A : Set 𝑙
    r : A → A → Prop 𝑚
    a b c : A

data refl-trans-close
  {A : Set 𝑙}
  (r : A → A → Prop 𝑚) :
  (a b : A)
  → ----------------------
  Prop (𝑙 ⊔ 𝑚)
  where
  rfl : refl-trans-close r a a
  step : (p : refl-trans-close r a b) (s : r b c) → refl-trans-close r a c

instance
  Relation-rtc : Relation {𝑙 = 𝑚} (refl-trans-close r)
  Relation-rtc = record {}

  TransitiveRelation-rtc : TransitiveRelation (refl-trans-close r)
  trans ⦃ TransitiveRelation-rtc ⦄ p rfl = p
  trans ⦃ TransitiveRelation-rtc ⦄ p (step q s) = step (trans p q) s

  ReflexiveRelation-rtc : ReflexiveRelation (refl-trans-close r)
  rflx ⦃ ReflexiveRelation-rtc ⦄ = rfl

