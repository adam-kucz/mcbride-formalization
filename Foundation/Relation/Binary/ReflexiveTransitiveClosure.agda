{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Relation.Binary.ReflexiveTransitiveClosure where

open import Foundation.PropUniverses
open import Foundation.Relation.Binary.Definition using (Rel)
open import Foundation.Relation.Binary.Property

data refl-trans-close {X : 𝒰 ˙} (R : Rel 𝒱 X X) : (a b : X) → 𝒰 ⊔ 𝒱 ᵖ where
  rfl : ∀ a → refl-trans-close R a a
  step : ∀ {a b c}
    (aRb : R a b)
    (bR*c : refl-trans-close R b c)
    → -------------------------------
    refl-trans-close R a c

instance
  TransitiveRelation-rtc : {R : Rel 𝒰 X X} → Transitive (refl-trans-close R)
  trans ⦃ TransitiveRelation-rtc ⦄ (rfl _) q = q
  trans ⦃ TransitiveRelation-rtc ⦄ (step s p) q = step s (trans p q)

  ReflexiveRelation-rtc : {R : Rel 𝒰 X X} → Reflexive (refl-trans-close R)
  refl ⦃ ReflexiveRelation-rtc ⦄ = rfl

  Subrelation-rtc : {R : Rel 𝒰 X X} → R ⊆ refl-trans-close R
  subrel ⦃ Subrelation-rtc {R = _R_} ⦄ {x} {y} xRy = step xRy (refl y)

  Subrelation-2-Subrelation-rtc :
    {R : Rel 𝒰 X X} {P : Rel 𝒱 X X}
    ⦃ R⊆P : R ⊆ P ⦄
    →
    refl-trans-close R ⊆ refl-trans-close P
  subrel ⦃ Subrelation-2-Subrelation-rtc ⦄ {x} {x} (rfl x) = refl x
  subrel ⦃ Subrelation-2-Subrelation-rtc ⦄ {x} {y} (step aRb bR*y) =
    step (subrel aRb) (subrel bR*y)

subrel-rtc-to-rtc-subrel-rtc :
  {R : Rel 𝒰 X X} {P : Rel 𝒱 X X}
  ⦃ s : P ⊆ refl-trans-close R ⦄
  → -----------------------------------------
  refl-trans-close P ⊆ refl-trans-close R
subrel-rtc-to-rtc-subrel-rtc {R = _R_} {P = _P_} = go
  where go : refl-trans-close _P_ ⊆ refl-trans-close _R_
        subrel ⦃ go ⦄ (rfl a) = refl a
        subrel ⦃ go ⦄ (step {x} {b} {y} xPb bP*y) =
          trans (subrel xPb) (subrel ⦃ go ⦄ bP*y)

open import Foundation.Proof
open Composable
open import Foundation.Function.Proof

instance
  RTCRelating :
    {P : Rel 𝒰 X X}
    {R : Rel 𝒱 Y Y}
    {f : (x : X) → Y}
    ⦃ _ : Relating f P R ⦄
    → ----------------------
    Relating f (refl-trans-close P) (refl-trans-close R)
  rel-preserv ⦃ RTCRelating {f = f} ⦄ (rfl a) = refl (f a)
  rel-preserv ⦃ RTCRelating ⦄ (step aRb aR*b) =
    step (rel-preserv aRb) (rel-preserv aR*b)

  Composable-R-R* : {X : 𝒰 ˙}
    {R : Rel 𝒱 X X}
    → -----------------
    Composable (𝒰 ⊔ 𝒱) R (refl-trans-close R)
  rel (Composable-R-R* {R = R}) = refl-trans-close R
  compose Composable-R-R* = step

  Composable-R*-R : {X : 𝒰 ˙}
    {R : Rel 𝒱 X X}
    → -----------------
    Composable (𝒰 ⊔ 𝒱) (refl-trans-close R) R
  rel (Composable-R*-R {R = R}) = refl-trans-close R
  compose Composable-R*-R {x} {x} {y} (rfl x) q =
    step q (refl y)
  compose Composable-R*-R (step aRb p) q = step aRb (compose Composable-R*-R p q)

