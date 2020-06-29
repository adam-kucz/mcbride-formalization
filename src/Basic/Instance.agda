{-# OPTIONS --exact-split --prop --safe #-}
module Basic.Instance where

open import Universes
open import Data.Nat
open import Basic

instance
  WellFoundedSortsℕ : WellFoundedSorts 𝒰₀ 𝒰₀ ℕ

open import Relation.Binary
open import Logic
open import Proof
open import Data.Nat.Proof
open import Function.Proof

_≻_ ⦃ WellFoundedSortsℕ ⦄ = _>_
trans ⦃ Transitive≻ ⦃ WellFoundedSortsℕ ⦄ ⦄ p q = trans q p
wf ⦃ WellFoundedSortsℕ ⦄ {P} p k = go (k +1) k $ postfix suc k
  where P0 = p λ {i} i<0 → ⊥-recursion _ $ ¬-<0 i i<0
        go : ∀ j i (q : i < j) → P i
        go zero zero _ = P0
        go (j +1) zero _ = P0
        go (j +1) (i +1) i+1<j+1 =
          p {i +1} λ {m} m<i+1 → go j m (
            proof m
              〉 _≤_ 〉 i :by: ap pred $ ⟶ -<-↔s≤- m<i+1 [: _≤_ ]
              〉 _<_ 〉 j :by: s<s→-<- i+1<j+1
            qed)
