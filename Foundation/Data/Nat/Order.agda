{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Data.Nat.Order where

open import Foundation.PropUniverses
open import Foundation.Data.Nat.Definition

open import Foundation.Prop'.Identity renaming (Idₚ to Id) using (_==_; ap)
open import Foundation.Prop'.Decidable
open import Foundation.Relation.Binary.Property
open import Foundation.Operation.Binary
open import Foundation.Logic
open import Foundation.Function.Proof

open import Foundation.Prop'.Function using (_$_; _∘_)

infix 35 _<_ _>_
data _<_ : (m n : ℕ) → 𝒰₀ ᵖ where
  z<s : ∀ {n} → 0 < suc n
  s<s : ∀ {m n} → n < m → suc n < suc m

_>_ : (m n : ℕ) → 𝒰₀ ᵖ
a > b = b < a

-<s : ∀ {m n} → (n<m : n < m) → n < suc m
-<s z<s = z<s
-<s (s<s n<m) = s<s (-<s n<m)

s<s→-<- : ∀ {m n} → (p : suc n < suc m) → n < m
s<s→-<- (s<s p) = p

instance
  Irreflexive< : Irreflexive _<_
  irrefl ⦃ Irreflexive< ⦄ 0 ()
  irrefl ⦃ Irreflexive< ⦄ (suc n) sn<sn = irrefl n (s<s→-<- sn<sn)

  Asym< : Asymmetric _<_
  asym ⦃ Asym< ⦄ z<s ()
  asym ⦃ Asym< ⦄ (s<s a<b) (s<s b<a) = asym b<a a<b

  Transitive< : Transitive _<_
  trans ⦃ Transitive< ⦄ z<s (s<s _) = z<s
  trans ⦃ Transitive< ⦄ (s<s a<b) (s<s b<c) = s<s (trans a<b b<c)

  Decidable< : ∀ {m n} → Decidable (m < n)
  Decidable< {zero} {zero} = false (λ ())
  Decidable< {zero} {suc n} = true z<s
  Decidable< {suc m} {zero} = false (λ ())
  Decidable< {suc m} {suc n} with decide (m < n)
  Decidable< {suc m} {suc n} | true n<m = true (s<s n<m)
  Decidable< {suc m} {suc n} | false ¬n<m = false λ m<n → ¬n<m (s<s→-<- m<n)
  
  Relating-suc-< : Relating suc _<_ _<_
  rel-preserv ⦃ Relating-suc-< ⦄ = s<s

  Postfix-suc-< : UniversalPostfix suc _<_
  UniversalPostfix.postfix Postfix-suc-< zero = z<s
  UniversalPostfix.postfix Postfix-suc-< (suc x) = s<s $ postfix suc x

infix 35 _≤_ _≥_
_≤_ _≥_ : (m n : ℕ) → 𝒰₀ ᵖ
a ≤ b = a == b ∨ a < b
a ≥ b = b ≤ a

instance
  Reflexive≤ : Reflexive _≤_
  refl ⦃ Reflexive≤ ⦄ a = ∨left (refl a)
  
  Transitive≤ : Transitive _≤_
  trans ⦃ Transitive≤ ⦄ (∨left (Id.refl a)) a≤b = a≤b
  trans ⦃ Transitive≤ ⦄ (∨right a<b) (∨left (Id.refl b)) = ∨right a<b
  trans ⦃ Transitive≤ ⦄ (∨right a<b) (∨right b<c) = ∨right $ trans a<b b<c
  
  Antisym≤ : Antisymmetric _≤_
  antisym ⦃ Antisym≤ ⦄ (∨left a==b) _ = a==b
  antisym ⦃ Antisym≤ ⦄ (∨right _) (∨left b==a) = sym b==a
  antisym ⦃ Antisym≤ ⦄ (∨right a<b) (∨right b<a) = ⊥-recursion _ (asym a<b b<a)

  Relating-suc-≤ : Relating suc _≤_ _≤_
  rel-preserv ⦃ Relating-suc-≤ ⦄ (∨left (Id.refl x)) = refl (suc x)
  rel-preserv ⦃ Relating-suc-≤ ⦄ (∨right a<b) = ∨right (ap suc a<b)

  Relating-pred-≤ : Relating pred _≤_ _≤_
  rel-preserv ⦃ Relating-pred-≤ ⦄ (∨left (Id.refl x)) = refl (pred x)
  rel-preserv ⦃ Relating-pred-≤ ⦄ (∨right (z<s {0})) = ∨left (refl 0)
  rel-preserv ⦃ Relating-pred-≤ ⦄ (∨right (z<s {suc n})) = ∨right z<s
  rel-preserv ⦃ Relating-pred-≤ ⦄ (∨right (s<s q)) = ∨right q

  Postfix-suc-≤ : UniversalPostfix suc _≤_
  UniversalPostfix.postfix Postfix-suc-≤ x = ∨right $ postfix suc x

  Prefix-pred-≤ : UniversalPrefix pred _≤_
  UniversalPrefix.prefix Prefix-pred-≤ 0 = ∨left (refl 0)
  UniversalPrefix.prefix Prefix-pred-≤ (suc x) = postfix suc x

-≤-↔-<s : ∀ {a b} → a ≤ b ↔ a < suc b
⟶ -≤-↔-<s (∨left (Id.refl x)) = postfix suc x
⟶ -≤-↔-<s (∨right a<b) = -<s a<b
-- ⟵ -≤-↔-<s (s<s (z<s {0})) = refl 1
-- ⟵ -≤-↔-<s (s<s (z<s {suc n})) = ap suc $ ∨right z<s
⟵ -≤-↔-<s (s<s (s<s a<b)) = ap suc $ ⟵ -≤-↔-<s $ s<s a<b
⟵ -≤-↔-<s (s<s (z<s {0})) = ap suc $ refl 0
⟵ -≤-↔-<s (s<s (z<s {suc n})) = ap suc $ ∨right z<s
⟵ -≤-↔-<s (z<s {0}) = refl 0
⟵ -≤-↔-<s (z<s {suc n}) = ∨right z<s

-<s∨->- : ∀ a b → a < b ∨ b < suc a
-<s∨->- a zero = ∨right z<s
-<s∨->- zero (suc b) = ∨left z<s
-<s∨->- (suc a) (suc b) with -<s∨->- a b
-<s∨->- (suc a) (suc b) | ∨left a<b = ∨left $ ap suc a<b
-<s∨->- (suc a) (suc b) | ∨right b<sa = ∨right $ ap suc b<sa

<→== : ∀ {n m}
  (p : n < suc m)
  (q : ¬ n < m)
  → ---------------
  n == m
<→== {n} {m} p q with -<s∨->- n m
<→== {n} {m} p q | ∨left n<m = ⊥-recursion (n == m) (q n<m)
<→== {0} {0} p q | ∨right z<s = refl zero
<→== {suc n} {suc m} (s<s p) q | ∨right m<sn = ap suc $ <→== p (λ n<m → q $ s<s n<m)

-<s↔¬->- : ∀ {a b} → a < suc b ↔ ¬ a > b
⟶ (-<s↔¬->- {suc a} {zero}) (s<s ())
⟶ -<s↔¬->- (s<s a<sb) (s<s b<a) = ⟶ -<s↔¬->- a<sb b<a
⟵ (-<s↔¬->- {zero}) q = z<s
⟵ (-<s↔¬->- {suc a} {zero}) q = ⊥-recursion (suc a < 1) (q z<s)
⟵ (-<s↔¬->- {suc a} {suc b}) q = ap suc $ ⟵ -<s↔¬->- $ λ a>b → q (s<s a>b )

infix 15 _<ₜ_
_<ₜ_ : (n m : ℕ) → 𝒰₀ ᵖ
_ <ₜ 0 = ⊥
0 <ₜ suc _ = ⊤
suc n <ₜ suc m = n <ₜ m

min : (x y : ℕ) → ℕ
min zero _ = zero
min (suc _) zero = zero
min (suc x) (suc y) = suc (min x y)

instance
  Commutative-min : Commutative min
  comm ⦃ Commutative-min ⦄ zero zero = refl 0
  comm ⦃ Commutative-min ⦄ zero (suc b) = refl 0
  comm ⦃ Commutative-min ⦄ (suc a) zero = refl 0
  comm ⦃ Commutative-min ⦄ (suc a) (suc b) = ap suc $ comm a b

min<s : ∀ m n → min m n < suc m
min<s 0 _ = postfix suc 0
min<s (suc m) 0 = z<s
min<s (suc m) (suc n) = s<s $ min<s m n

min== : ∀ m n → min m n == m ∨ min m n == n
min== zero n = ∨left (refl 0)
min== (suc _) zero = ∨right (refl 0)
min== (suc m) (suc n) with min== m n
min== (suc m) (suc n) | ∨left min-m-n==m = ∨left $ ap suc min-m-n==m
min== (suc m) (suc n) | ∨right min-m-n==n = ∨right $ ap suc min-m-n==n

≤→min== : ∀ {m n} → (p : n ≤ m) → min n m == n
≤→min== (∨left (Id.refl n)) = ∨-contract (min== n n)
≤→min== (∨right z<s) = refl 0
≤→min== (∨right (s<s n<m)) = ap suc $ ≤→min== $ ∨right n<m
