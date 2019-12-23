{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Structure.Hemiring where

open import Foundation.Structure.Semigroup
open import Foundation.Structure.Monoid
open import Foundation.Operation.Binary.Property using (Commutative)

open import Foundation.PropUniverses
open import Foundation.Prop'.Identity using (_==_)
open import Foundation.Operation.Binary
  renaming (ClosedOp to Op) hiding (Op)

open Monoid renaming (e to zero) using ()

record FormHemiring {X : 𝒰 ˙} (_+_ _*_ : Op X) (zero : X) : 𝒰 ᵖ where
  -- TODO: figure out why this has no effect
  -- infixl 160 _⁻¹
  -- infixl 130 _∙_
  field
    ⦃ monoid+ ⦄ : FormMonoid _+_ zero
    ⦃ commutative+ ⦄ : Commutative _+_
    ⦃ semigroup* ⦄ : FormSemigroup _*_
    0* : ∀ a → zero * a == zero
    *0 : ∀ a → a * zero == zero
    *[+]==*+* : ∀ a b c → a * (b + c) == (a * b) + (a * c)
    [+]*==*+* : ∀ a b c → (a + b) * c  == (a * c) + (b * c)

open FormHemiring ⦃ ... ⦄ public

record Hemiring (X : 𝒰 ˙) : 𝒰 ˙  where
  field
    _+_ _*_ : Op X
    zero : X
    ⦃ def ⦄ : FormHemiring _+_ _*_ zero

open Hemiring ⦃ ... ⦄ public
