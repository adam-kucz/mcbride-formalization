{-# OPTIONS --exact-split --prop #-}
open import Basic
open import PropUniverses

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

infixl 30 _≼_
data _≼_ : RelOnExpr (𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲) where
  refl≼ : (e : expr-of-type tag n) → e ≼ e

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

refl ⦃ Reflexive≼ ⦄ = refl≼

trans ⦃ Transitive≼ ⦄ (refl≼ _) q = q
trans ⦃ Transitive≼ ⦄ (sort p)(refl≼ _) = sort p
trans ⦃ Transitive≼ ⦄ (sort p)(sort q) = sort (trans q p)
trans ⦃ Transitive≼ ⦄ ([ π x: p₀ ]→ p₁)(refl≼ _) = [ π x: p₀ ]→ p₁
trans ⦃ Transitive≼ ⦄ ([ π x: p₀ ]→ p₁)([ π x: q₀ ]→ q₁) =
  [ π x: trans q₀ p₀ ]→ trans p₁ q₁
