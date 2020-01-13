{-# OPTIONS --exact-split --prop --safe #-}
module Liftable where

open import Universes
open import Data.Nat

-- types that take and return variable-indexed objects
-- which can be lifted to operate on more variables
-- while being identity on the newly introduced ones
record Liftable (f : (m n : ℕ) → 𝒰 ˙) : 𝒰 ˙ where
  field
    lift : ∀ {m n} (ρ : f m n) → f (suc m) (suc n)

  lift-by : ∀ {m n}
    (k : ℕ)
    (e : f m n)
    → -----------------------
    f (k + m) (k + n)
  lift-by zero e = e
  lift-by (suc k) e = lift (lift-by k e)

  open import Function using (_~_; _∘_; _$_)
  open import Proposition.Identity

  lift-inner : ∀ {m n k} →
    lift-by {m}{n}(suc k) ~ lift-by k ∘ lift
  lift-inner {k = zero} x = refl (lift x)
  lift-inner {k = k +1} x = {!lift-inner {k = k} x!}
    where aux : ∀ {m n}{x y : f m n} (p : x == y) → lift x == lift y
          aux (refl x) = refl (lift x)

open Liftable ⦃ … ⦄ public

{-# DISPLAY Liftable.lift L = lift #-}

