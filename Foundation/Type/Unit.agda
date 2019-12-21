{-# OPTIONS --without-K --exact-split --safe #-}
module Foundation.Type.Unit where

open import Foundation.Universes

data 𝟙 : 𝒰₀ ˙ where
  instance ⋆ : 𝟙

