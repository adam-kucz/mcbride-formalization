{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Data.FinNat.Property where

open import Foundation.Data.FinNat.Definition
open import Foundation.Data.Nat using (ℕ; suc; zero; _<_; s<s; z<s)

open import Foundation.Prop'.Decidable
open import Foundation.Prop'.Identity using (_==_; refl; ap; ap')
open import Foundation.Function using (_$_; _∘_)
open import Foundation.Prop'.Function renaming (_$_ to _$'_) using ()
open import Foundation.Logic
open import Foundation.Function.Property using (Injective; inj)

instance
  Injective-suc : ∀ {n} → Injective (Finℕ.suc {n})
  inj ⦃ Injective-suc ⦄ (refl (suc x)) = refl x

  Decidable==Finℕ : ∀ {n} {a b : Finℕ n} → Decidable (a == b)
  Decidable==Finℕ {a = zero} {zero} = true (refl 0)
  Decidable==Finℕ {a = zero} {suc b} = false λ ()
  Decidable==Finℕ {a = suc a} {zero} = false λ ()
  Decidable==Finℕ {a = suc a} {suc b} with decide (a == b)
  Decidable==Finℕ {suc a} {suc b} | true a==b = true (ap' Finℕ suc a==b)
  Decidable==Finℕ {suc a} {suc b} | false ¬a==b =
    false λ { (refl _) → ¬a==b $' refl b }

  Injective-toℕ : ∀ {n} → Injective (toℕ {n})
  inj ⦃ Injective-toℕ ⦄ {x = zero} {zero} _ = refl zero
  inj ⦃ Injective-toℕ ⦄ {x = suc x} {suc y} fx==fy = 
    ap' Finℕ suc $' inj ⦃ Injective-toℕ ⦄ $' inj fx==fy

toℕ< : ∀ {n} {a : Finℕ n} → toℕ a < n
toℕ< {a = zero} = z<s
toℕ< {a = suc a} = s<s (toℕ< {a = a})

toℕ-maxFinℕ : ∀ {n} → toℕ (maxFinℕ {n}) == n
toℕ-maxFinℕ {zero} = refl 0
toℕ-maxFinℕ {suc n} = ap ℕ.suc toℕ-maxFinℕ

toℕ-toFinℕ : ∀ {m n} (n<m : n < m) → toℕ (toFinℕ n n<m) == n
toℕ-toFinℕ {m = suc m} z<s = refl 0
toℕ-toFinℕ {m = suc m} (s<s n<m) = ap suc $' toℕ-toFinℕ n<m

