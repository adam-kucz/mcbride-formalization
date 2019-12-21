{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Data.Nat where

open import Foundation.PropUniverses
open import Foundation.Data.Nat.Definition public
open import Foundation.Prop'.Identity
open import Foundation.Prop'.Decidable
open import Foundation.Function using (_$_)

open import Foundation.Function.Properties using (Injective; inj)
open import Foundation.Data.Nat.Proof

private
  variable
    m n : ℕ

instance
  Injective-suc : Injective suc
  inj ⦃ Injective-suc ⦄ (refl (suc m)) = refl m

pred : (m : ℕ) → ℕ
pred zero    = zero
pred (suc m) = m

instance
  ==ℕDecidable : Decidable (n == m)
  ==ℕDecidable {zero} {zero} = true (refl zero)
  ==ℕDecidable {zero} {suc n} = false λ ()
  ==ℕDecidable {suc m} {zero} = false λ ()
  ==ℕDecidable {suc m} {suc n} with decide (m == n)
  ==ℕDecidable {suc m} {suc n} | true n==m = true (ap suc n==m)
  ==ℕDecidable {suc m} {suc n} | false ¬n==m =
    false λ { (refl (suc m)) → ¬n==m (refl m) }
