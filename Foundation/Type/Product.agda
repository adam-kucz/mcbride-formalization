{-# OPTIONS --without-K --exact-split --safe #-}
module Foundation.Type.Product where

open import Foundation.Universes

Π : {X : 𝒰 ˙} (A : (x : X) → 𝒱 ˙) → (𝒰 ⊔ 𝒱) ˙
Π {X = X} A = (x : X) → A x
