{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Data.FinNat.Order where

open import Foundation.PropUniverses
open import Foundation.Data.Nat using (ℕ)
open import Foundation.Data.FinNat using (Finℕ; zero; suc)
open import Foundation.Prop'.Identity using (_==_)
open import Foundation.Logic using (¬_; _∨_)

open import Foundation.Relation.Binary

private
  variable
    n m : ℕ
    a b : Finℕ n

infix 35 _<ₛ_
data _<ₛ_ : Finℕ n → Finℕ m → 𝒰₀ ᵖ where
  z<ₛs : zero {n} <ₛ suc a
  s<ₛs : (a<ₛb : a <ₛ b) → suc a <ₛ suc b

infix 35 _≤ₛ_
_≤ₛ_ : Finℕ n → Finℕ n → 𝒰₀ ᵖ
a ≤ₛ b = a == b ∨ a <ₛ b

s<s→-<- : (p : suc a <ₛ suc b) → a <ₛ b
s<s→-<- (s<ₛs p) = p

<irrefl : irreflexive (_<ₛ_ {n} {n})
<irrefl zero ()
<irrefl (suc n) sn<sn = <irrefl n (s<s→-<- sn<sn)

<asym : asymmetric (_<ₛ_ {n} {n})
<asym z<ₛs ()
<asym (s<ₛs a<b) (s<ₛs b<a) = <asym b<a a<b

<transitive : transitive (_<ₛ_ {n} {n})
<transitive z<ₛs (s<ₛs _) = z<ₛs
<transitive (s<ₛs a<b) (s<ₛs b<c) = s<ₛs (<transitive a<b b<c)

-- instance
--   Relating-maxFinℕ : Relating (λ n → maxFinℕ {n}) _<_ _<ₛ_
--   rel-preserv ⦃ Relating-maxFinℕ ⦄ z<s = z<ₛs
--   rel-preserv ⦃ Relating-maxFinℕ ⦄ (s<s rab) = s<ₛs (rel-preserv rab)

  -- Relating-suc : Relating (suc {n}) _<ₛ_ _<ₛ_
  -- rel-preserv ⦃ Relating-suc ⦄ = s<ₛs

  -- Relating-toℕ : Relating (toℕ {n}) _<ₛ_ _<_
  -- rel-preserv ⦃ Relating-toℕ ⦄ z<ₛs = z<s
  -- rel-preserv ⦃ Relating-toℕ ⦄ (s<ₛs rab) = s<s (rel-preserv rab)

-- instance
--   Relating-cap : Relating (λ m → toℕ $ cap m n) _≤_ _≤_
--   rel-preserv ⦃ Relating-cap {n} ⦄ {m} {m'} m≤m' = 
--     proof toℕ $ cap m n
--       〉 _==_ 〉 toℕ $ toFinℕ (min m n) min<s :by: refl
--       〉 _==_ 〉 min m n :by: toℕ-toFinℕ min<s
--       〉 _≤_ 〉 min m' n :by: rel-preserv m≤m'
--       〉 _==_ 〉 toℕ $ toFinℕ (min m' n) min<s :by: ← toℕ-toFinℕ min<s
--       〉 _==_ 〉 toℕ $ cap m' n :by: refl
--     qed
