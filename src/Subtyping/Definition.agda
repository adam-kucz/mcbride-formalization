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

data _≼_ : RelOnExpr (𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲) where
  reflexive : (S : expr-of-type tag n)
    → -------------------------------
    S ≼ S

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

refl ⦃ Reflexive≼ ⦄ = reflexive

trans ⦃ Transitive≼ ⦄ = go
  where go : {S T U : expr-of-type tag n}(S≼T : S ≼ T)(T≼U : T ≼ U) → S ≼ U
        go (reflexive S) S≼U = S≼U
        go S≼T@(sort _)(reflexive _) = S≼T
        go (sort p₀) (sort p₁) = sort $ trans p₁ p₀
        go S≼T@([ _ x: _ ]→ _)(reflexive _) = S≼T
        go ([ π x: S₀≼T₀ ]→ S₁≼T₁) ([ π x: T₀≼U₀ ]→ T₁≼U₁) =
          [ π x: go T₀≼U₀ S₀≼T₀ ]→ go S₁≼T₁ T₁≼U₁
