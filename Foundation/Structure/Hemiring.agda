{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Structure.Hemiring where

open import Foundation.Universes
open import Foundation.Prop'.Identity using (_==_)
open import Foundation.Structure.Semigroup using (Semigroup)
open import Foundation.Structure.Monoid using (Monoid)
open import Foundation.Operation.Binary renaming (ClosedOp to Op) using ()
open import Foundation.Operation.Binary.Property using (Commutative)

open Monoid renaming (e to zero) using ()

record Hemiring {X : 𝒰 ˙} (_+_ _*_ : Op X) : 𝒰 ˙  where
  -- TODO: figure out why these seem to have no effect
  -- infixl 20 _+_
  -- infixl 21 _*_
  field
    ⦃ monoid+ ⦄ : Monoid _+_
    ⦃ commutative+ ⦄ : Commutative _+_
    ⦃ semigroup* ⦄ : Semigroup _*_
    0* : ∀ a → zero monoid+ * a == zero monoid+
    *0 : ∀ a → a * zero monoid+ == zero monoid+
    *[+]==*+* : ∀ a b c → a * (b + c) == (a * b) + (a * c)
    [+]*==*+* : ∀ a b c → (a + b) * c  == (a * c) + (b * c)

open Hemiring {{...}} public

