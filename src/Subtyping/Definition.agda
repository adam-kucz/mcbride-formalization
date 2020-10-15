{-# OPTIONS --exact-split #-}
open import Basic
open import Universes

module Subtyping.Definition
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

-- Definition 17 (subtyping)

open import Data.Nat hiding (_⊔_)
open import Proof

open import Syntax
open import Computation

open import Relation.Binary
  hiding (_~_; Reflexive~; Transitive~; Symmetric~)

open import Subtyping.Similarity

data _≼_ : RelOnExpr (𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲) where
  similar : {S T : expr-of-type tag n}
    (p : S ~ T)
    → ----------
    S ≼ T

  sort : ∀{i j}
    (p : j ≻ i)
    → ------------
     _≼_ {n}{term} (⋆ i) (⋆ j)

  [_x:_]→_ : ∀ π {S S' T T'}
    (p : S' ≼ S)
    (q : T ≼ T')
    → ---------------------
    _≼_ {n}{term} ([ π x: S ]→ T)([ π x: S' ]→ T')

-- Lemma 18 (subtyping transitivity)

instance
  Reflexive≼ : Reflexive (_≼_ {n = n}{tag})
  Transitive≼ : Transitive (_≼_ {n = n}{tag})

refl ⦃ Reflexive≼ ⦄ t = similar (refl t)

trans ⦃ Transitive≼ ⦄ (similar p)(similar q) = similar $ trans p q
trans ⦃ Transitive≼ ⦄ (similar (⋆ i))(sort q) = sort q
trans ⦃ Transitive≼ ⦄ (similar ([ π x: p₀ ]→ p₁))([ π x: q₀ ]→ q₁) =
  [ π x: trans q₀ (similar (sym p₀)) ]→ trans (similar p₁) q₁
trans ⦃ Transitive≼ ⦄ (sort p)(similar (⋆ i)) = sort p
trans ⦃ Transitive≼ ⦄ (sort p)(sort q) = sort (trans q p)
trans ⦃ Transitive≼ ⦄ ([ π x: p₀ ]→ p₁)(similar ([ π x: q₀ ]→ q₁)) =
  [ π x: trans (similar (sym q₀)) p₀ ]→ trans p₁ (similar q₁)
trans ⦃ Transitive≼ ⦄ ([ π x: p₀ ]→ p₁)([ π x: q₀ ]→ q₁) =
  [ π x: trans q₀ p₀ ]→ trans p₁ q₁
