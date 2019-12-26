{-# OPTIONS --without-K --exact-split --safe #-}
module Foundation.Type.Transport.Definition where

open import Foundation.Universes
open import Foundation.Function renaming (_∘_ to _o_) using ()

infix 50 _⟺_ _,_
record _⟺_ (X : 𝒰 ˙) (Y : 𝒱 ˙) : 𝒰 ⊔ 𝒱 ˙ where
  constructor _,_
  field
    ⟹ : (x : X) → Y
    ⟸ : (y : Y) → X

open _⟺_ public

infix 150 _∘_
_∘_ :
  (p : X ⟺ Y)
  (q : Y ⟺ Z)
  → --------------
  X ⟺ Z
⟹ (p ∘ q) = ⟹ q o ⟹ p
⟸ (p ∘ q) = ⟸ p o ⟸ q
