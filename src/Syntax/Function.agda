{-# OPTIONS --exact-split --prop --safe  #-}
open import Basic
open import PropUniverses

module Syntax.Function
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax.Definition
open import Logic

is-pi-type : ∀{n}(S : Term n) → 𝒰₀ ᵖ
is-pi-type (⋆ _) = ⊥
is-pi-type ([ _ x: _ ]→ _) = ⊤
is-pi-type (λx, _) = ⊥
is-pi-type ⌊ _ ⌋ = ⊥
