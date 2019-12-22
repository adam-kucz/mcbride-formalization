{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Data.FinNat.Definition where

open import Foundation.Universes
open import Foundation.Data.Nat.Definition
open import Foundation.Data.Nat.Order
open import Foundation.Function using (_$_)
open import Foundation.Logic

-- types of natural numbers less than index
data Finℕ : (n : ℕ) → 𝒰₀ ˙ where
  zero : ∀ {n} → Finℕ (suc n)
  suc : ∀ {n} → (x : Finℕ n) → Finℕ (suc n)

instance
  NatFinℕ : ∀ {n} → Nat (Finℕ n)
  Nat.Constraint (NatFinℕ {n}) m = m <ₜ n
  Nat.fromℕ (NatFinℕ {suc n}) zero = zero
  Nat.fromℕ (NatFinℕ {suc n}) (suc m) = suc $ Nat.fromℕ (NatFinℕ {n}) m

toℕ : ∀ {n} → Finℕ n → ℕ
toℕ zero = 0
toℕ (suc x) = suc (toℕ x)

maxFinℕ : ∀ {n} → Finℕ (suc n)
maxFinℕ {zero} = zero
maxFinℕ {suc n} = suc maxFinℕ

toFinℕ : ∀ {m} n (n<m : n < m) → Finℕ m
toFinℕ {suc m} zero _ = zero
toFinℕ {suc m} (suc n) n<m = suc $ toFinℕ n (s<s→-<- n<m)

