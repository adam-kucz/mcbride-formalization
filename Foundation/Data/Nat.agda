{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Data.Nat where

open import Foundation.PropUniverses
open import Foundation.Prop'.Identity
open import Foundation.Logic as Logic
open Logic using (⋆ₚ) public
open import Foundation.Prop'.Decidable
open import Foundation.Function using (_$_)

open import Foundation.Function.Properties using (injective)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

private
  variable
    m n : ℕ

instance
  injective-suc : injective suc
  injective-suc (refl (suc m)) = refl m

{-# BUILTIN NATURAL ℕ #-}

record Nat (X : 𝒰 ˙) : 𝒰 ⁺ ˙ where
  field
    Constraint : (n : ℕ) → 𝒰 ᵖ
    fromℕ : (n : ℕ) ⦃ p : Constraint n ⦄ → X

open Nat {{...}} public using (fromℕ)

{-# BUILTIN FROMNAT fromℕ #-}

instance
  Natℕ : Nat ℕ
  Nat.Constraint Natℕ _ = ⊤
  Nat.fromℕ Natℕ n = n

  ==ℕDecidable : Decidable (n == m)
  ==ℕDecidable {zero} {zero} = true (refl zero)
  ==ℕDecidable {zero} {suc n} = false λ ()
  ==ℕDecidable {suc m} {zero} = false λ ()
  ==ℕDecidable {suc m} {suc n} with decide (m == n)
  ==ℕDecidable {suc m} {suc n} | true n==m = true (ap suc n==m)
  ==ℕDecidable {suc m} {suc n} | false ¬n==m =
    false λ { (refl (suc m)) → ¬n==m (refl m) }
