{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Data.FinNat where

open import Foundation.Data.Nat as Nat hiding (injective-suc)
open import Foundation.Data.Nat.Order
open import Foundation.Prop'.Decidable
open import Foundation.Prop'.Identity using (_==_; refl; ap)
open import Foundation.Function using (_$_; _∘_)
open import Foundation.Prop'.Function renaming (_$_ to _$'_) using ()
open import Foundation.Function.Properties using (injective)
open import Foundation.Logic

private
  variable
    n m : ℕ

-- types of natural numbers less than index
data Finℕ : (n : ℕ) → Set where
  zero : Finℕ (suc n)
  suc : (x : Finℕ n) → Finℕ (suc n)

private
  variable
    a b c : Finℕ n

data _<ₛ_ : Finℕ n → Finℕ m → Prop where
  z<ₛs : zero {n} <ₛ suc a
  s<ₛs : (a<ₛb : a <ₛ b) → suc a <ₛ suc b

instance
  NatFinℕ : Nat (Finℕ n)
  Nat.Constraint (NatFinℕ {n}) m = m <ₜ n
  Nat.fromℕ (NatFinℕ {suc n}) zero = zero
  Nat.fromℕ (NatFinℕ {suc n}) (suc m) = suc $ Nat.fromℕ (NatFinℕ {n}) m

  injective-suc : injective (Finℕ.suc {n})
  injective-suc (refl (suc x)) = refl x

  Decidable==Finℕ : {a b : Finℕ n} → Decidable (a == b)
  Decidable==Finℕ {a = zero} {zero} = true (refl 0)
  Decidable==Finℕ {a = zero} {suc b} = false λ ()
  Decidable==Finℕ {a = suc a} {zero} = false λ ()
  Decidable==Finℕ {a = suc a} {suc b} with decide (a == b)
  Decidable==Finℕ {suc a} {suc b} | true a==b = true (ap Finℕ.suc a==b)
  Decidable==Finℕ {suc a} {suc b} | false ¬a==b =
    false λ { (refl _) → ¬a==b $' refl b }

toℕ : Finℕ n → ℕ
toℕ zero = 0
toℕ (suc x) = suc (toℕ x)

toℕ< : {a : Finℕ n} → toℕ a < n
toℕ< {a = zero} = z<s
toℕ< {a = suc a} = s<s (toℕ< {a = a})

instance
  injective-toℕ : injective (toℕ {n})
  injective-toℕ {x = zero} {zero} _ = refl zero
  injective-toℕ {x = suc x} {suc y} fx==fy = 
    ap Finℕ.suc $' injective-toℕ $' Nat.injective-suc fx==fy

maxFinℕ : Finℕ (suc n)
maxFinℕ {zero} = zero
maxFinℕ {suc n} = suc maxFinℕ

toℕ-maxFinℕ : toℕ (maxFinℕ {n}) == n
toℕ-maxFinℕ {zero} = refl 0
toℕ-maxFinℕ {suc n} = ap ℕ.suc toℕ-maxFinℕ

toFinℕ : ∀ n (n<m : n < m) → Finℕ m
toFinℕ {suc m} zero _ = zero
toFinℕ {suc m} (suc n) n<m = suc $ toFinℕ n (s<s→-<- n<m)

toℕ-toFinℕ : (n<m : n < m) → toℕ (toFinℕ n n<m) == n
toℕ-toFinℕ {m = suc m} z<s = refl 0
toℕ-toFinℕ {m = suc m} (s<s n<m) = ap suc $' toℕ-toFinℕ n<m

