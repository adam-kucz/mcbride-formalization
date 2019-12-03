{-# OPTIONS --prop  #-}
module Foundations.Data.Nat where

open import Foundations.Algebra.GroupLike hiding (zero; _+_)
open import Foundations.Algebra.Relations.Classes
open import Foundations.Algebra.RingLike
open import Foundations.Decidable
open import Foundations.Equality.Core
open import Foundations.Functions.Classes
open import Foundations.Functions.Core
open import Foundations.Logic as Logic 
open Logic public using (tt)
open import Foundations.Univ using (Level; lzero; lsuc; _⊔_; 𝑙)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

private
  variable
    m n : ℕ

instance
  Injective-suc : Injective suc
  inj ⦃ Injective-suc ⦄ refl = refl

{-# BUILTIN NATURAL ℕ #-}

record Nat (A : Set 𝑙) : Set (lsuc 𝑙) where
  field
    Constraint : (n : ℕ) → Prop 𝑙
    fromℕ : (n : ℕ) {{p : Constraint n}} → A

open Nat {{...}} public using (fromℕ)

{-# BUILTIN FROMNAT fromℕ #-}

instance
  Natℕ : Nat ℕ
  Nat.Constraint Natℕ _ = ⊤
  Nat.fromℕ Natℕ n = n

  ==ℕDecidable : Decidable (n == m)
  decide ⦃ ==ℕDecidable {zero} {zero} ⦄ = true refl
  decide ⦃ ==ℕDecidable {zero} {suc n} ⦄ = false λ ()
  decide ⦃ ==ℕDecidable {suc m} {zero} ⦄ = false λ ()
  decide ⦃ ==ℕDecidable {suc m} {suc n} ⦄ with decide {P = m == n}
  decide ⦃ ==ℕDecidable {suc m} {suc n} ⦄ | true n==m = true (suc ` n==m)
  decide ⦃ ==ℕDecidable {suc m} {suc n} ⦄ | false ¬n==m = false λ where refl → ¬n==m refl

infixl 20 _+_
_+_ : ℕ → ℕ → ℕ
zero  + b = b
suc a + b = suc $ a + b

infixl 21 _*_
_*_ : ℕ → ℕ → ℕ
zero  * b = zero
suc a * b = b + a * b

private
  variable
    a b c : ℕ

+suc : a + suc b == suc (a + b)
+suc {zero} = refl
+suc {suc a} {b} = suc ` +suc

instance
  Magmaℕ+ : Magma ℕ _+_
  Magmaℕ+ = record {}

  Semigroupℕ+ : Semigroup ℕ _+_
  +assoc ⦃ Semigroupℕ+ ⦄ {ℕ.zero} = refl
  +assoc ⦃ Semigroupℕ+ ⦄ {suc a} = suc ` +assoc {a = a}

  Monoidℕ+ : Monoid ℕ _+_
  Monoid.zero Monoidℕ+ = ℕ.zero
  +zero ⦃ Monoidℕ+ ⦄ {ℕ.zero} = refl
  +zero ⦃ Monoidℕ+ ⦄ {suc a} = suc ` +zero
  zero+ {{Monoidℕ+}} = refl

  Commutativeℕ+ : Commutative ℕ _+_
  +comm ⦃ Commutativeℕ+ ⦄ {ℕ.zero} = ← +zero
  +comm ⦃ Commutativeℕ+ ⦄ {suc a} {b} = 
    proof
      suc a + b
      〈 _==_ 〉-[ suc ` +comm {a = a} {b} ]
      suc (b + a)
      〈 _==_ 〉-[ ← +suc ]
      b + suc a
    qed

*-suc : a * suc b == a + a * b
*-suc {zero} = refl
*-suc {suc a} {b} = suc `
  proof
    b + a * suc b
    〈 _==_ 〉-[ b +_ ` *-suc {a} ]
    b + (a + a * b)
    〈 _==_ 〉-[ +swap {a = b} {a} ]
    a + (b + a * b)
  qed

private
  *-0 : a * 0 == 0
  *-0 {ℕ.zero} = refl
  *-0 {suc a} = *-0 {a}

  *-+-distrib : a * (b + c) == a * b + a * c
  *-+-distrib {zero} = refl
  *-+-distrib {suc a} {b} {c} =
    proof
      b + c + a * (b + c)
      〈 _==_ 〉-[ b + c +_ ` *-+-distrib {a} {b} ]
      (b + c) + (a * b + a * c)
      〈 _==_ 〉-[ ← +assoc {a = b} ]
      b + (c + (a * b + a * c))
      〈 _==_ 〉-[ b +_ ` +swap {a = c} {a * b} ]
      b + (a * b + (c + a * c))
      〈 _==_ 〉-[ +assoc {a = b} ]
      b + a * b + (c + a * c)
    qed

instance
  Magmaℕ* : Magma ℕ _*_
  Magmaℕ* = record {}

  Commutativeℕ* : Commutative ℕ _*_
  +comm ⦃ Commutativeℕ* ⦄ {ℕ.zero} {b} = ← *-0 {a = b}
  +comm ⦃ Commutativeℕ* ⦄ {suc a} {b} = 
    proof
      b + a * b
      〈 _==_ 〉-[ b +_ ` +comm {a = a} ]
      b + b * a
      〈 _==_ 〉-[ ← *-suc {b} ]
      b * suc a
    qed

  Semigroupℕ* : Semigroup ℕ _*_
  +assoc {{Semigroupℕ*}} {ℕ.zero} = refl
  +assoc {{Semigroupℕ*}} {suc a} {b} {c} = ←
    proof
      (b + a * b) * c
      〈 _==_ 〉-[ +comm {b = c} ]
      c * (b + a * b)
      〈 _==_ 〉-[ *-+-distrib {c} {b} ]
      c * b + c * (a * b)
      〈 _==_ 〉-[ _+ c * (a * b) ` +comm {a = c} ]
      b * c + c * (a * b)
      〈 _==_ 〉-[ b * c +_ ` +comm {a = c}  ]
      b * c + (a * b) * c
      〈 _==_ 〉-[ b * c +_ ` ← +assoc {a = a}  ]
      b * c + a * (b * c)
    qed

  Monoidℕ* : Monoid ℕ _*_
  Monoid.zero Monoidℕ* = 1
  +zero ⦃ Monoidℕ* ⦄ {ℕ.zero} = refl
  +zero ⦃ Monoidℕ* ⦄ {suc a} = suc ` +zero
  zero+ {{Monoidℕ*}} = +zero

  Hemiringℕ+* : Hemiring ℕ _+_ _*_
  Hemiring.monoid+ Hemiringℕ+* = Monoidℕ+
  0* {{Hemiringℕ+*}} = refl
  *0 ⦃ Hemiringℕ+* ⦄ {a} = *-0 {a}
  *[+]==*+* {{Hemiringℕ+*}} {a} = *-+-distrib {a}
  [+]*==*+* {{Hemiringℕ+*}} {a} {b} {c} =
    proof
      (a + b) * c
      〈 _==_ 〉-[ +comm {a = a + b} ]
      c * (a + b)
      〈 _==_ 〉-[ *[+]==*+* {a = c} {a} {b} ]
      c * a + c * b
      〈 _==_ 〉-[ c * a +_ ` +comm {a = c} ]
      c * a + b * c
      〈 _==_ 〉-[ _+ b * c ` +comm {a = c} ]
      a * c + b * c
    qed

infix 15 _<_
data _<_ : ℕ → ℕ → Prop where
  z<s : 0 < suc n
  s<s : n < m → suc n < suc m

instance
  comp-<-== : Composable _<_ _==_
  comp-<-== = composable-r-== _<_

  comp-==-< : Composable _==_ _<_
  comp-==-< = composable-==-r _<_

  Relating-suc-< : Relating suc _<_ _<_
  rel-preserv ⦃ Relating-suc-< ⦄ = s<s

self<s : n < suc n
self<s {0} = z<s
self<s {suc _} = s<s self<s

-<s : (n<m : n < m) → n < suc m
-<s z<s = z<s
-<s (s<s n<m) = s<s (-<s n<m)

s<s→-<- : (p : suc n < suc m) → n < m
s<s→-<- (s<s p) = p

<irrefl : ¬ n < n
<irrefl {ℕ.zero} = λ ()
<irrefl {suc n} sn<sn = <irrefl (s<s→-<- sn<sn)

<asym : a < b → ¬ b < a
<asym z<s = λ ()
<asym (s<s a<b) = λ where (s<s b<a) → <asym b<a a<b

instance
  Relation< : Relation {A = ℕ} _<_
  Relation< = record {}
  
  TransitiveRelation< : TransitiveRelation {A = ℕ} _<_
  trans ⦃ TransitiveRelation< ⦄ z<s (s<s _) = z<s
  trans ⦃ TransitiveRelation< ⦄ (s<s a<b) (s<s b<c) = s<s (trans a<b b<c)

  <Decidable : Decidable (m < n)
  decide ⦃ <Decidable {zero} {zero} ⦄ = false (λ ())
  decide ⦃ <Decidable {zero} {suc n} ⦄ = true z<s
  decide ⦃ <Decidable {suc m} {zero} ⦄ = false (λ ())
  decide ⦃ <Decidable {suc m} {suc n} ⦄ with decide {P = m < n}
  decide ⦃ <Decidable {suc m} {suc n} ⦄ | true n<m = true (s<s n<m)
  decide ⦃ <Decidable {suc m} {suc n} ⦄ | false ¬n<m = false (¬n<m ∘ₚ s<s→-<-)

infix 15 _≤_
_≤_ : ℕ → ℕ → Prop
a ≤ b = a == b ∨ a < b

s≤s : a ≤ b → suc a ≤ suc b
s≤s (refl ∨∅) = refl ∨∅
s≤s (∅∨ a<b) = ∅∨ s<s a<b

instance
  Relation≤ : Relation {A = ℕ} _≤_
  Relation≤ = record {}
  
  ReflexiveRelation≤ : ReflexiveRelation {A = ℕ} _≤_
  rflx ⦃ ReflexiveRelation≤ ⦄ = refl ∨∅

  TransitiveRelation≤ : TransitiveRelation {A = ℕ} _≤_
  trans ⦃ TransitiveRelation≤ ⦄ (refl ∨∅) b≤c = b≤c
  trans ⦃ TransitiveRelation≤ ⦄ (∅∨ a<b) (refl ∨∅) = ∅∨ a<b
  trans ⦃ TransitiveRelation≤ ⦄ (∅∨ a<b) (∅∨ b<c) = ∅∨ trans a<b b<c

  comp-≤-== : Composable _≤_ _==_
  comp-≤-== = composable-r-== _≤_

  comp-==-≤ : Composable _==_ _≤_
  comp-==-≤ = composable-==-r _≤_

  comp-<-≤ : Composable {𝑚₂ = lzero} _<_ _≤_
  rel ⦃ comp-<-≤ ⦄ = _<_
  compose ⦃ comp-<-≤ ⦄ a<b (refl ∨∅) = a<b
  compose ⦃ comp-<-≤ ⦄ a<b (∅∨ b<c) = trans a<b b<c

  comp-≤-< : Composable {𝑚₂ = lzero} _≤_ _<_
  rel ⦃ comp-≤-< ⦄ = _<_
  compose ⦃ comp-≤-< ⦄ (∅∨ a<b) b<c = trans a<b b<c
  compose ⦃ comp-≤-< ⦄ (refl ∨∅) b<c = b<c

≤antisym :
  (a≤b : a ≤ b)
  (b≤a : b ≤ a)
  → ------------
  a == b
≤antisym (a==b ∨∅) _ = a==b
≤antisym (∅∨ a<b) (∅∨ b<a) = ⊥elim (<asym a<b b<a)
≤antisym (∅∨ _) (b==a ∨∅) = ← b==a

<∨≤ : a < b ∨ b ≤ a
<∨≤ {ℕ.zero} {ℕ.zero} = ∅∨ (refl ∨∅)
<∨≤ {ℕ.zero} {suc b} = z<s ∨∅
<∨≤ {suc a} {ℕ.zero} = ∅∨ (∅∨ z<s)
<∨≤ {suc a} {suc b} with <∨≤ {a} {b}
<∨≤ {suc a} {suc b} | a<b ∨∅ = s<s a<b ∨∅
<∨≤ {suc a} {suc b} | ∅∨ (∅∨ b<a) = ∅∨ (∅∨ s<s b<a)
<∨≤ {suc a} {suc b} | ∅∨ (b==a ∨∅) = ∅∨ ((suc ` b==a) ∨∅)

<→== :
  (p : n < suc m)
  (q : ¬ n < m)
  → ---------------
  n == m
<→== {n} {m} n<sm ¬n<m with <∨≤ {n} {m}
<→== {n} {m} n<sm ¬n<m | n<m ∨∅ = ⊥elim (¬n<m n<m)
<→== _ _ | ∅∨ (m==n ∨∅) = ← m==n
<→== {suc n} {m} n<sm _ | ∅∨ (∅∨ m<n) with s<s→-<- n<sm
<→== {suc n} {suc m} _ ¬sn<sm | ∅∨ (∅∨ m<n) | n<sm = suc ` <→== n<sm (¬sn<sm ∘ₚ s<s)

≤↔¬< : a ≤ b ↔ ¬ b < a
_↔_.-→ ≤↔¬< (∅∨ a<b) b<a = <asym a<b b<a
_↔_.-→ ≤↔¬< (refl ∨∅) b<a = <irrefl b<a
_↔_.←- (≤↔¬< {a} {b}) ¬b<a with <∨≤ {a} {b}
_↔_.←- (≤↔¬< {a} {b}) ¬b<a | a<b ∨∅ = ∅∨ a<b
_↔_.←- (≤↔¬< {a} {b}) ¬b<a | ∅∨ (∅∨ b<a) = ⊥elim (¬b<a b<a)
_↔_.←- (≤↔¬< {a} {b}) ¬b<a | ∅∨ (b==a ∨∅) = (← b==a) ∨∅

s≤-↔-<- : suc a ≤ b ↔ a < b
_↔_.-→ s≤-↔-<- (refl ∨∅) = self<s
_↔_.-→ s≤-↔-<- (∅∨ s<s a<b) = -<s a<b
_↔_.←- s≤-↔-<- (z<s {zero}) = rflx
_↔_.←- s≤-↔-<- (z<s {suc n}) = s≤s (∅∨_ {P = 0 == suc n} (z<s {n}))
_↔_.←- s≤-↔-<- (s<s a<b) = s≤s (_↔_.←- s≤-↔-<- a<b)

infix 15 _<ₜ_
_<ₜ_ : ℕ → ℕ → Prop
_ <ₜ 0 = ⊥
0 <ₜ suc _ = ⊤
suc n <ₜ suc m = n <ₜ m
