{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Data.Nat.Order where

open import Foundation.PropUniverses
open import Foundation.Data.Nat

open import Foundation.Prop'.Identity using (_==_; refl; ap)
open import Foundation.Prop'.Decidable
open import Foundation.Relation.Binary
open import Foundation.Operation.Binary
open import Foundation.Logic

open import Foundation.Prop'.Function using (_$_; _∘_)
open import Foundation.Prop'.Identity.Instances renaming (refl to rflx)

private
  variable
    a b c m n : ℕ

infix 35 _<_
data _<_ : ℕ → ℕ → Prop where
  z<s : 0 < suc n
  s<s : n < m → suc n < suc m

self<s : n < suc n
self<s {0} = z<s
self<s {suc _} = s<s self<s

-<s : (n<m : n < m) → n < suc m
-<s z<s = z<s
-<s (s<s n<m) = s<s (-<s n<m)

s<s→-<- : (p : suc n < suc m) → n < m
s<s→-<- (s<s p) = p

<irrefl : ∀ n → ¬ n < n
<irrefl 0 = λ ()
<irrefl (suc n) sn<sn = <irrefl n (s<s→-<- sn<sn)

<asym : a < b → ¬ b < a
<asym z<s = λ ()
<asym (s<s a<b) = λ where (s<s b<a) → <asym b<a a<b

infix 35 _≤_
_≤_ : ℕ → ℕ → Prop
a ≤ b = a == b ∨ a < b

-≤-↔s≤s : a ≤ b ↔ suc a ≤ suc b
⟶ -≤-↔s≤s (∨left (refl a)) = ∨left $ refl (suc a)
⟶ -≤-↔s≤s (∨right a<b) = ∨right $ s<s a<b
⟵ -≤-↔s≤s (∨left (refl (suc a))) = ∨left $ refl a
⟵ -≤-↔s≤s (∨right sa<sb) = ∨right $ s<s→-<- sa<sb

<transitive : transitive _<_
<transitive z<s (s<s _) = z<s
<transitive (s<s a<b) (s<s b<c) = s<s (<transitive a<b b<c)

instance
  <Decidable : Decidable (m < n)
  <Decidable {zero} {zero} = false (λ ())
  <Decidable {zero} {suc n} = true z<s
  <Decidable {suc m} {zero} = false (λ ())
  <Decidable {suc m} {suc n} with decide (m < n)
  <Decidable {suc m} {suc n} | true n<m = true (s<s n<m)
  <Decidable {suc m} {suc n} | false ¬n<m = false λ m<n → ¬n<m (s<s→-<- m<n)
  
≤reflexive : reflexive _≤_
≤reflexive a = ∨left (refl a)

≤transitive : transitive _≤_
≤transitive (∨left (refl a)) b≤c = b≤c
≤transitive (∨right a<b) (∨left (refl b)) = ∨right a<b
≤transitive (∨right a<b) (∨right b<c) = ∨right $ <transitive a<b b<c

≤antisym : antisymmetric _≤_
≤antisym (∨left a==b) _ = a==b
≤antisym (∨right _) (∨left b==a) = sym $ b==a
≤antisym (∨right a<b) (∨right b<a) = ⊥-recursion _ (<asym a<b b<a)

<∨≤ : ∀ a b → a < b ∨ b ≤ a
<∨≤ 0 0 = ∨right $ ∨left $ refl 0
<∨≤ 0 (suc b) = ∨left z<s
<∨≤ (suc a) 0 = ∨right $ ∨right z<s
<∨≤ (suc a) (suc b) with <∨≤ a b
<∨≤ (suc a) (suc b) | ∨left a<b = ∨left $ s<s a<b
<∨≤ (suc a) (suc b) | ∨right (∨right b<a) = ∨right $ ∨right $ s<s b<a
<∨≤ (suc a) (suc b) | ∨right (∨left b==a) = ∨right $ ∨left $ ap suc b==a

<→== :
  ∀ n m →
  (p : n < suc m)
  (q : ¬ n < m)
  → ---------------
  n == m
<→== n m n<sm ¬n<m with <∨≤ n m
<→== n m n<sm ¬n<m | ∨left n<m = ⊥-recursion (n == m) (¬n<m n<m)
<→== _ _ _ _ | ∨right (∨left m==n) = sym $ m==n
<→== (suc n) m n<sm _ | ∨right (∨right m<n) with s<s→-<- n<sm
<→== (suc n) (suc m) _ ¬sn<sm | ∨right (∨right m<n) | n<sm =
  ap suc $ <→== n m n<sm (¬sn<sm ∘ s<s)

≤↔¬< : a ≤ b ↔ ¬ b < a
⟶ ≤↔¬< (∨right a<b) b<a = <asym a<b b<a
⟶ ≤↔¬< (∨left (refl a)) b<a = <irrefl a b<a
⟵ (≤↔¬< {a} {b}) ¬b<a with <∨≤ a b
⟵ (≤↔¬< {a} {b}) ¬b<a | ∨left a<b = ∨right a<b
⟵ (≤↔¬< {a} {b}) ¬b<a | ∨right (∨right b<a) = ⊥-recursion (a ≤ b) (¬b<a b<a)
⟵ (≤↔¬< {a} {b}) ¬b<a | ∨right (∨left b==a) = ∨left $ sym $ b==a

s≤-↔-<- : suc a ≤ b ↔ a < b
⟶ s≤-↔-<- (∨left (refl _)) = self<s
⟶ s≤-↔-<- (∨right (s<s a<b)) = -<s a<b
⟵ s≤-↔-<- (z<s {zero}) = ≤reflexive 1
⟵ s≤-↔-<- (z<s {suc n}) = ⟶ -≤-↔s≤s (∨right {𝑋 = 0 == suc n} (z<s {n}))
⟵ s≤-↔-<- (s<s a<b) = ⟶ -≤-↔s≤s (⟵ s≤-↔-<- a<b)

-≤-↔-<s : a ≤ b ↔ a < suc b
⟶ -≤-↔-<s (∨left (refl _)) = self<s
⟶ -≤-↔-<s (∨right a<b) = -<s a<b
⟵ -≤-↔-<s (s<s a'<b) = ⟵ s≤-↔-<- a'<b
⟵ (-≤-↔-<s {b = zero}) z<s = ≤reflexive 0
⟵ (-≤-↔-<s {b = suc b}) z<s = ∨right z<s

infix 15 _<ₜ_
_<ₜ_ : (n m : ℕ) → 𝒰₀ ᵖ
_ <ₜ 0 = ⊥
0 <ₜ suc _ = ⊤
suc n <ₜ suc m = n <ₜ m

min : ℕ → ℕ → ℕ
min zero _ = zero
min (suc _) zero = zero
min (suc x) (suc y) = suc (min x y)

commutative-min : commutative min
commutative-min zero zero = refl 0
commutative-min zero (suc b) = refl 0
commutative-min (suc a) zero = refl 0
commutative-min (suc a) (suc b) = ap suc $ commutative-min a b

-- instance
--   Relating-min-right : Relating (min n) _≤_ _≤_
--   rel-preserv ⦃ Relating-min-right ⦄ (refl ∨∅) = rflx
--   rel-preserv ⦃ Relating-min-right {zero} ⦄ (∅∨ _) = rflx
--   rel-preserv ⦃ Relating-min-right {suc n} ⦄ (∅∨ z<s) = ∅∨ z<s
--   rel-preserv ⦃ Relating-min-right {suc n} ⦄ {suc m} {suc m'} (∅∨ s<s m<m') =
--     have
--       min n m ≤ min n m' :from: rel-preserv ⦃ Relating-min-right {n} ⦄ (∅∨ m<m')
--     -→ suc (min n m) ≤ suc (min n m') :by: _↔_.-→ -≤-↔s≤s

--   Relating-min-left : Relating (λ m → min m n) _≤_ _≤_
--   rel-preserv ⦃ Relating-min-left {n} ⦄ {a} {b} a≤b =
--     proof min a n
--       〉 _==_ 〉 min n a :by: +comm {a = a}
--       〉 _≤_ 〉 min n b :by: rel-preserv a≤b
--       〉 _==_ 〉 min b n :by: +comm {a = n}
--     qed

min<s : min m n < suc m
min<s {zero} = self<s
min<s {suc m} {zero} = z<s
min<s {suc m} {suc n} = s<s (min<s {m} {n})

min== : ∀ m n → min m n == m ∨ min m n == n
min== zero n = ∨left (refl 0)
min== (suc _) zero = ∨right (refl 0)
min== (suc m) (suc n) with min== m n
min== (suc m) (suc n) | ∨left min-m-n==m = ∨left $ ap suc min-m-n==m
min== (suc m) (suc n) | ∨right min-m-n==n = ∨right $ ap suc min-m-n==n

≤→min== : (p : n ≤ m) → min n m == n
≤→min== (∨left (refl n)) = ∨-contract (min== n n)
≤→min== (∨right z<s) = refl 0
≤→min== (∨right (s<s n<m)) = ap suc $ ≤→min== $ ∨right n<m

