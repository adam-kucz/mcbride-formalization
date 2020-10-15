{-# OPTIONS --exact-split  #-}
open import Basic
open import Universes

module Syntax.Function
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax.Definition
open import Logic

is-pi-type : ∀{n}(S : Term n) → 𝒰₀ ˙
is-pi-type (⋆ _) = ⊥
is-pi-type ([ _ x: _ ]→ _) = ⊤
is-pi-type (λx, _) = ⊥
is-pi-type ⌊ _ ⌋ = ⊥
