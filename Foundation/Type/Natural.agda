-- {-# OPTIONS --exact-split --safe --prop #-}
-- module Foundation.Type.Natural where

-- open import Foundation.Universes
-- open import Foundation.Type.Empty
-- open import Foundation.Type.Unit
-- open import Foundation.Type.BinarySum
-- open import Foundation.Data.Nat.Arithmetic.Definition
--   renaming (ℕ to N; _+_ to _⊹_) using ()

-- data ℕ : (n : N) → 𝒰₀ ˙ where
--   base : (z : 𝟘) → ℕ 0
--   step : {n : N} (X : 𝟙 + ℕ n) → ℕ (N.suc n)

-- 𝟚 𝟛 𝟜 𝟝 𝟞 𝟟 𝟠 : 𝒰₀ ˙
-- 𝟚 = ℕ 2
-- 𝟛 = ℕ 3
-- 𝟜 = ℕ 4
-- 𝟝 = ℕ 5
-- 𝟞 = ℕ 6
-- 𝟟 = ℕ 7
-- 𝟠 = ℕ 8
-- 𝟡 = ℕ 9

-- pattern suc x = step (inr x)

-- pattern ₀ = step (inl ⋆)
-- pattern ₁ = suc ₀
-- pattern ₂ = suc ₁
-- pattern ₃ = suc ₂
-- pattern ₄ = suc ₃
-- pattern ₅ = suc ₄
-- pattern ₆ = suc ₅
-- pattern ₇ = suc ₆
-- pattern ₈ = suc ₇
-- pattern ₉ = suc ₈

-- pattern ₀fin = base ()
-- pattern ₁fin = suc ₀fin
-- pattern ₂fin = suc ₁fin
-- pattern ₃fin = suc ₂fin
-- pattern ₄fin = suc ₃fin
-- pattern ₅fin = suc ₄fin
-- pattern ₆fin = suc ₅fin
-- pattern ₇fin = suc ₆fin
-- pattern ₈fin = suc ₇fin
-- pattern ₉fin = suc ₈fin

-- pattern ₀₊ x = step (inl x)
-- pattern ₁₊ x = suc (₀₊ x)
-- pattern ₂₊ x = suc (₁₊ x)
-- pattern ₃₊ x = suc (₂₊ x)
-- pattern ₄₊ x = suc (₃₊ x)
-- pattern ₅₊ x = suc (₄₊ x)
-- pattern ₆₊ x = suc (₅₊ x)
-- pattern ₇₊ x = suc (₆₊ x)
-- pattern ₈₊ x = suc (₇₊ x)
-- pattern ₉₊ x = suc (₈₊ x)

-- promote : {n : N} (m : N) (X : ℕ n) → ℕ (n ⊹ m)
-- promote m (suc x) = suc (promote m x)
-- promote 0 ₀ = ₀
-- promote (N.suc m) ₀ = suc (+step induct)
--   where induct : {n : N} → ℕ (N.suc n ⊹ m)
--         induct = promote m ₀
--         +step : {m n : N} (X : ℕ (N.suc m ⊹ n)) → ℕ (m ⊹ N.suc n)
--         +step {0} {n} X = X
--         +step {N.suc m} {n} ₀ = ₀
--         +step {N.suc m} {n} (suc x) = suc (+step x)
