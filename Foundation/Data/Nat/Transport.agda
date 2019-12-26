{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Data.Nat.Transport where

open import Foundation.Type.Identity
open import Foundation.Data.Nat.Definition
open import Foundation.Data.Nat.Arithmetic

open import Foundation.Universes

+-0-transport : ∀ m
  (A : (n : ℕ) → 𝒰 ˙)
  → ------------------
  A (m + zero) ≡ A m
+-0-transport    zero A = refl (A zero)
+-0-transport (suc m) A = +-0-transport m (λ n → A (suc n))

+-suc-transport : ∀ m n
  (A : (n : ℕ) → 𝒰 ˙)
  → ------------------------------
  A (m + suc n) ≡ A (suc (m + n))
+-suc-transport    zero n A = refl (A (suc n))
+-suc-transport (suc m) n A = +-suc-transport m n (λ n → A (suc n))

comm-transport : ∀ m n
  (A : (n : ℕ) → 𝒰 ˙)
  → --------------------
  A (m + n) ≡ A (n + m)
comm-transport m    zero A = +-0-transport m A
comm-transport m (suc n) A =
  trans (+-suc-transport m n A)
        (comm-transport m n (λ k → A (suc k)))
