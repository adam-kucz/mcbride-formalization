{-# OPTIONS --without-K --exact-split --safe --prop #-}
module Foundation.Prop'.Unit where

open import Foundation.PropUniverses

data ⊤ : 𝒰₀ ᵖ where
  instance ⋆ₚ : ⊤

open ⊤ public
