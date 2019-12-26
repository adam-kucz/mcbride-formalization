{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Data.Nat.Arithmetic.Definition where

open import Foundation.Data.Nat.Definition public

infixl 130 _+_
_+_ : (m n : ℕ) → ℕ
zero + n = n
suc m + n = suc (m + n)

infixl 140 _*_
_*_ : (m n : ℕ) → ℕ
zero  * n = zero
suc m * n = n + m * n
