{-# OPTIONS --without-K --exact-split --safe #-}
module Foundation.Data.Maybe where

open import Foundation.Universes

data Maybe (X : 𝒰 ˙) : 𝒰 ˙ where
  nothing : Maybe X
  just : (x : X) → Maybe X
