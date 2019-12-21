{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Data.Nat.Arithmetic.Definition where

open import Foundation.Data.Nat.Definition public

infixl 130 _+_
_+_ : ℕ → ℕ → ℕ
zero  + b = b
suc a + b = suc (a + b)

infixl 140 _*_
_*_ : ℕ → ℕ → ℕ
zero  * b = 0
suc a * b = b + a * b
