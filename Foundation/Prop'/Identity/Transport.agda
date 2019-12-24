{-# OPTIONS --exact-split --prop --rewriting #-}
module Foundation.Prop'.Identity.Transport where

open import Foundation.Prop'.Identity.Definition using (_==_; refl)

open import Foundation.Universes

postulate
  transport : {X Y : 𝒰 ˙} (p : X == Y) (x : X) → Y
  transport-refl : {X : 𝒰 ˙} {x : X} → transport (refl X) x == x

{-# BUILTIN REWRITE _==_ #-}
{-# REWRITE transport-refl #-}
