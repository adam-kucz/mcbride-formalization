{-# OPTIONS --prop #-}   --show-implicit
module Foundations.Data.FinNat where

open import Foundations.Algebra.GroupLike hiding (zero; _+_)
open import Foundations.Algebra.Relations.Classes
open import Foundations.Data.Nat as Nat hiding (Injective-suc)
open import Foundations.Decidable
open import Foundations.Equality.Core
open import Foundations.Functions.Core using (_$_; _∘_)
open import Foundations.Functions.Classes
open import Foundations.Logic

private
  variable
    n m : ℕ

-- types of natural numbers less than index
data Finℕ : (n : ℕ) → Set where
  zero : Finℕ (suc n)
  suc : (x : Finℕ n) → Finℕ (suc n)

private
  variable
    a b c : Finℕ n

data _<ₛ_ : Finℕ n → Finℕ m → Prop where
  z<ₛs : zero {n} <ₛ suc a
  s<ₛs : (a<ₛb : a <ₛ b) → suc a <ₛ suc b

_≤ₛ_ : Finℕ n → Finℕ n → Prop
a ≤ₛ b = a == b ∨ a <ₛ b

instance
  NatFinℕ : Nat (Finℕ n)
  Nat.Constraint (NatFinℕ {n}) m = m <ₜ n
  Nat.fromℕ (NatFinℕ {suc n}) zero = zero
  Nat.fromℕ (NatFinℕ {suc n}) (suc m) = suc $ Nat.fromℕ (NatFinℕ {n}) m

  Injective-suc : Injective (Finℕ.suc {n})
  inj ⦃ Injective-suc ⦄ refl = refl

  Relating-suc : Relating (suc {n}) _<ₛ_ _<ₛ_
  rel-preserv ⦃ Relating-suc ⦄ = s<ₛs

  Decidable==Finℕ : {a b : Finℕ n} → Decidable (a == b)
  decide ⦃ Decidable==Finℕ {a = zero} {zero} ⦄ = true refl
  decide ⦃ Decidable==Finℕ {a = zero} {suc b} ⦄ = false λ ()
  decide ⦃ Decidable==Finℕ {a = suc a} {zero} ⦄ = false λ ()
  decide ⦃ Decidable==Finℕ {a = suc a} {suc b} ⦄
    with decide ⦃ Decidable==Finℕ {a = a} {b} ⦄
  decide (Decidable==Finℕ {suc a} {suc b}) | true a==b = true (Finℕ.suc ` a==b)
  decide (Decidable==Finℕ {suc a} {suc b}) | false ¬a==b = false λ where refl → ¬a==b refl

toℕ : Finℕ n → ℕ
toℕ zero = 0
toℕ (suc x) = suc (toℕ x)

instance
  Injective-toℕ : Injective (toℕ {n})
  inj ⦃ Injective-toℕ ⦄ {zero} {zero} _ = refl
  inj ⦃ Injective-toℕ ⦄ {suc a} {suc b} fx==fy =
    suc ` inj (inj ⦃ Nat.Injective-suc ⦄ fx==fy)

  Relating-toℕ : Relating (toℕ {n}) _<ₛ_ _<_
  rel-preserv ⦃ Relating-toℕ ⦄ z<ₛs = z<s
  rel-preserv ⦃ Relating-toℕ ⦄ (s<ₛs rab) = s<s (rel-preserv rab)

maxFinℕ : Finℕ (suc n)
maxFinℕ {zero} = zero
maxFinℕ {suc n} = suc maxFinℕ

instance
  Relating-maxFinℕ : Relating (λ n → maxFinℕ {n}) _<_ _<ₛ_
  rel-preserv ⦃ Relating-maxFinℕ ⦄ z<s = z<ₛs
  rel-preserv ⦃ Relating-maxFinℕ ⦄ (s<s rab) = s<ₛs (rel-preserv rab)

toℕ-maxFinℕ : toℕ (maxFinℕ {n}) == n
toℕ-maxFinℕ {zero} = refl
toℕ-maxFinℕ {suc n} = suc ` toℕ-maxFinℕ

-- return n if n fits in Finℕ (m + 1) [i.e. when n < m+1]
-- otherwise return the largest element of Finℕ (m + x1)
cap : (n : ℕ) → Finℕ (suc m)
cap {m} n with decide {P = n < m}
cap {m} n | false ¬n<sm = maxFinℕ
cap {suc _} zero | true n<sm = zero
cap {zero} (suc _) | true n<sm = zero
cap {suc m} (suc n) | true n<sm = suc $ cap {m} n

-- instance
  -- Relating-cap : Relating (cap {m}) _≤_ _≤ₛ_

toℕ-cap-fit : (n<sm : n < suc m) → toℕ (cap {m} n) == n
toℕ-cap-fit {n} {m} n<sm with decide ⦃ <Decidable {n} {m} ⦄
-- TODO: figure out why this gives different results
-- toℕ-cap-fit {n} {m} n<sm with decide {P = n < m}
toℕ-cap-fit {zero} {suc _} n<sm | true n<m = refl
toℕ-cap-fit {suc n} {suc m} n<sm | true n<m = suc ` (toℕ-cap-fit (s<s→-<- n<sm))
toℕ-cap-fit {n} {m} n<sm | false ¬n<m with <→== n<sm ¬n<m
toℕ-cap-fit {n} {.n} n<sm | false ¬n<m | refl = toℕ-maxFinℕ

toℕ-cap-overflow : (sm≤n : suc m ≤ n) → toℕ (cap {m} n) == m
toℕ-cap-overflow {m} {n} _ with decide ⦃ <Decidable {n} {m} ⦄
toℕ-cap-overflow {m} {n} sm≤n | false ¬n<m = toℕ-maxFinℕ
toℕ-cap-overflow {m} {zero} (() ∨∅) | true n<m
toℕ-cap-overflow {m} {zero} (∅∨ ()) | true n<m
toℕ-cap-overflow {m} {suc n} sm≤n | true n<m = ⊥elim (¬sn<sm (-<s n<m))
  where ¬sn<sm : ¬ suc n < suc m
        ¬sn<sm = _↔_.-→ ≤↔¬< sm≤n

cap-thm :
  (f : ℕ → ℕ)
  (p : ∀ {x} → x ≤ f x)
  → --------------------------------
  cap {m} (f (toℕ (cap {m} n))) == cap {m} (f n)
cap-thm {m} {n} _ _ with decide ⦃ <Decidable {n} {m} ⦄
cap-thm {suc m} {zero} f p | true n<m = refl
cap-thm {suc m} {suc n} f p | true (s<s n<m) = cap {suc m} ∘ f ∘ suc ` toℕ-cap-fit (-<s n<m)
cap-thm {m} {n} f p | false ¬n<m with decide {P = n < suc m}
cap-thm {m} {n} f p | false ¬n<m | true n<sm with <→== n<sm ¬n<m
cap-thm {m} {.m} f p | false ¬n<m | true n<sm | refl = cap ∘ f ` toℕ-maxFinℕ {m}
cap-thm {m} {n} f p | false _ | false ¬n<sm = 
  proof
    cap {m} ∘ f $ toℕ $ maxFinℕ {m}
    〈 _==_ 〉-[ cap {m} ∘ f ` toℕ-maxFinℕ ]
    cap {m} $ f m
    〈 _==_ 〉-[ inj (proof
        toℕ $ cap {m} $ f m
        〈 _==_ 〉-[ toℕ-cap-fm==m ]
        m
        〈 _==_ 〉-[ ← toℕ-cap-overflow sm≤fn ]
        toℕ $ cap {m} $ f n
      qed
      )]
    cap {m} $ f $ n
  qed
  where sm≤fn = proof
            suc m
            〈 _≤_ 〉-[ _↔_.←- ≤↔¬< ¬n<sm ]
            n
            〈 _≤_ 〉-[ p ]
            f n
          qed
        toℕ-cap-fm==m : toℕ $ cap {m} $ f m == m
        toℕ-cap-fm==m with p {m}
        toℕ-cap-fm==m | m==fm ∨∅ = proof
            toℕ $ cap {m} $ f m
            〈 _==_ 〉-[ toℕ ∘ cap ` ← m==fm ]
            toℕ $ cap {m} m
            〈 _==_ 〉-[ toℕ-cap-fit (self<s {m}) ]
            m
          qed
        toℕ-cap-fm==m | ∅∨ m<fm = {! <∨≤!}
         -- {! toℕ-cap-overflow (_↔_.←- ≤↔¬< (<irrefl {suc m})) !}
        cap-fm-eq : (eq : m == f m) → toℕ $ cap {m} $ f m == m
        cap-fm-eq m==fm = proof
            toℕ $ cap {m} $ f m
            〈 _==_ 〉-[ toℕ ∘ cap {m} ` ← m==fm ]
            toℕ $ cap {m} m
            〈 _==_ 〉-[ toℕ-cap-fit self<s ]
            m
          qed

  -- proof
  --   cap (f (toℕ (cap {m} n)))
  --   〈 _==_ 〉-[ cap ∘ f ` {!!} ]
  --   cap (f n)
  -- qed

infixl 20 _+ₛ_
_+ₛ_ : (x : Finℕ n) (y : Finℕ n) → Finℕ n
_+ₛ_ {suc n} x y = cap $ toℕ x + toℕ y

infixl 21 _*ₛ_
_*ₛ_ : (x : Finℕ n) (y : Finℕ n) → Finℕ n
_*ₛ_ {suc n} x y = cap $ toℕ x * toℕ y

instance
  MagmaFinℕ+ : Magma (Finℕ n) _+ₛ_
  MagmaFinℕ+ = record {}

  SemigroupFinℕ+ : Semigroup (Finℕ n) _+ₛ_
  +assoc ⦃ SemigroupFinℕ+ {suc n} ⦄ {a} = {!!}
  
  MonoidFinℕ+ : Monoid (Finℕ (suc n)) _+ₛ_
  Monoid.zero MonoidFinℕ+ = 0
  +zero ⦃ MonoidFinℕ+ ⦄ = {!!}
  zero+ ⦃ MonoidFinℕ+ ⦄ = {!!}

  CommutativeFinℕ+ : Commutative (Finℕ n) _+ₛ_
  +comm ⦃ CommutativeFinℕ+ ⦄ {a} = {!!}


{-
-- saturating suc
ssuc : (x : Finℕ n) → Finℕ n
ssuc {1}              zero = zero
ssuc {suc (suc n)}    zero = 1
ssuc               (suc x) = suc $ ssuc x

ssuc-suc-comm : ssuc (Finℕ.suc a) == Finℕ.suc (ssuc a)
ssuc-suc-comm {zero} = refl
ssuc-suc-comm {suc n} = refl

-- saturating +
infixl 20 _+ₛ_
_+ₛ_ : (x : Finℕ n) (y : Finℕ n) → Finℕ n
zero +ₛ y = y
suc x +ₛ zero = suc x
suc x +ₛ suc y = suc ∘ ssuc $ x +ₛ y

+ₛ-0 : {a : Finℕ (suc n)} → a +ₛ 0 == a
+ₛ-0 {a = zero} = refl
+ₛ-0 {a = suc a} = refl

+ₛ-comm : a +ₛ b == b +ₛ a
+ₛ-comm {a = zero} = ← +ₛ-0
+ₛ-comm {a = suc a} {zero} = refl
+ₛ-comm {a = suc a} {suc b} = suc ∘ ssuc ` +ₛ-comm {a = a} {b}

ssuc-+ₛ : ssuc a +ₛ b == ssuc $ a +ₛ b
ssuc-+ₛ {1} {zero} {zero} = refl
ssuc-+ₛ {suc (suc n)} {zero} {zero} = refl
ssuc-+ₛ {suc (suc n)} {zero} {suc b} = refl
ssuc-+ₛ {a = suc a} {zero} =
  proof
    ssuc (suc a) +ₛ 0
    〈 _==_ 〉-[ _+ₛ 0 ` ssuc-suc-comm ]
    suc (ssuc a) +ₛ 0
    〈 _==_ 〉-[ ← ssuc-suc-comm ]
    ssuc (suc a)
  qed
ssuc-+ₛ {a = suc a} {suc b} =
  proof
    ssuc (suc a) +ₛ suc b
    〈 _==_ 〉-[ _+ₛ suc b ` ssuc-suc-comm ]
    suc (ssuc a) +ₛ suc b
    〈 _==_ 〉-[ refl ]
    suc ∘ ssuc $ (ssuc a) +ₛ b
    〈 _==_ 〉-[ suc ∘ ssuc ` ssuc-+ₛ {a = a} ]
    suc ∘ ssuc $ ssuc $ a +ₛ b
    〈 _==_ 〉-[ ← ssuc-suc-comm ]
    ssuc ∘ suc $ ssuc $ a +ₛ b
  qed

+ₛ-ssuc : a +ₛ ssuc b == ssuc $ a +ₛ b
+ₛ-ssuc {a = a} {b} = proof
  a +ₛ ssuc b
  〈 _==_ 〉-[ +ₛ-comm {a = a} ]
  ssuc b +ₛ a
  〈 _==_ 〉-[ ssuc-+ₛ ]
  ssuc $ b +ₛ a
  〈 _==_ 〉-[ ssuc ` ← +ₛ-comm {a = a} ]
  ssuc $ a +ₛ b
  qed

+ₛ-assoc : (a +ₛ b) +ₛ c == a +ₛ (b +ₛ c)
+ₛ-assoc {a = zero} = refl
+ₛ-assoc {a = suc a} {zero} = refl
+ₛ-assoc {a = suc a} {suc b} {zero} = +ₛ-0
+ₛ-assoc {a = suc a} {suc b} {suc c} =
  proof
    suc a +ₛ suc b +ₛ suc c
    〈 _==_ 〉-[ refl ]
    suc ∘ ssuc $ (ssuc $ a +ₛ b) +ₛ c
    〈 _==_ 〉-[ suc ∘ ssuc ` ssuc-+ₛ {b = c} ]
    suc ∘ ssuc $ ssuc $ (a +ₛ b) +ₛ c
    〈 _==_ 〉-[ suc ∘ ssuc ∘ ssuc ` +ₛ-assoc {a = a} ]
    suc ∘ ssuc $ ssuc $ a +ₛ (b +ₛ c)
    〈 _==_ 〉-[ suc ∘ ssuc ` ← +ₛ-ssuc {a = a} ]
    suc ∘ ssuc $ a +ₛ ssuc (b +ₛ c)
    〈 _==_ 〉-[ refl ]
    suc a +ₛ (suc b +ₛ suc c)
  qed

infixl 21 _*ₛ_
_*ₛ_ : (x : Finℕ n) (y : Finℕ n) → Finℕ n
zero *ₛ _ = 0
suc x *ₛ zero = 0
suc x *ₛ suc y = suc $ x +ₛ y +ₛ x *ₛ y

*ₛ-0 : {a : Finℕ (suc n)} → a *ₛ zero == Finℕ.zero {n}
*ₛ-0 {a = zero} = refl
*ₛ-0 {a = suc a} = refl

*ₛ-comm : a *ₛ b == b *ₛ a
*ₛ-comm {a = zero} {b} = ← *ₛ-0 {a = b}
*ₛ-comm {a = suc a} {zero} = refl
*ₛ-comm {a = suc a} {suc b} =
  proof
    suc $ (a +ₛ b) +ₛ a *ₛ b
    〈 _==_ 〉-[ suc ` _+ₛ a *ₛ b ` +ₛ-comm {a = a} ]
    suc $ (b +ₛ a) +ₛ a *ₛ b
    〈 _==_ 〉-[ suc ` (b +ₛ a) +ₛ_ ` *ₛ-comm {a = a} ]
    suc $ b +ₛ a +ₛ b *ₛ a
  qed

*ₛ-ssuc : a *ₛ ssuc b == a +ₛ a *ₛ b
*ₛ-ssuc {a = zero} = refl
*ₛ-ssuc {suc (suc _)} {suc a} {zero} = suc `
  proof
    a +ₛ zero +ₛ a *ₛ zero
    〈 _==_ 〉-[ (a +ₛ zero) +ₛ_ ` *ₛ-0 {a = a} ]
    a +ₛ zero +ₛ zero
    〈 _==_ 〉-[ +ₛ-0 ]
    a +ₛ zero
    〈 _==_ 〉-[ +ₛ-0 ]
    a
  qed
*ₛ-ssuc {suc (suc _)} {suc a} {suc b} =
  proof
    suc a *ₛ ssuc (suc b)
    〈 _==_ 〉-[ suc a *ₛ_ ` ssuc-suc-comm ]
    suc a *ₛ suc (ssuc b)
    〈 _==_ 〉-[ refl ]
    suc $ a +ₛ ssuc b +ₛ a *ₛ ssuc b
    〈 _==_ 〉-[ {!!} ]
    suc ∘ ssuc $ a +ₛ (a +ₛ b +ₛ a *ₛ b)
  qed

*ₛ-+ₛ-distrib : a *ₛ (b +ₛ c) == a *ₛ b +ₛ a *ₛ c
*ₛ-+ₛ-distrib {a = zero} = refl
*ₛ-+ₛ-distrib {a = suc a} {zero} = refl
*ₛ-+ₛ-distrib {a = suc a} {suc b} {zero} = refl
*ₛ-+ₛ-distrib {a = suc a} {suc b} {suc c} = suc `
  proof
    (a +ₛ ssuc (b +ₛ c)) +ₛ a *ₛ ssuc (b +ₛ c)
    〈 _==_ 〉-[ _+ₛ a *ₛ ssuc (b +ₛ c) ` +ₛ-ssuc {a = a} ]
    (ssuc $ a +ₛ (b +ₛ c)) +ₛ a *ₛ ssuc (b +ₛ c)
    〈 _==_ 〉-[ ssuc-+ₛ ]
    ssuc $ a +ₛ (b +ₛ c) +ₛ a *ₛ ssuc (b +ₛ c)
    〈 _==_ 〉-[ ssuc ` {!!} ]
    ssuc $ a +ₛ b +ₛ a *ₛ b +ₛ (a +ₛ c +ₛ a *ₛ c)
  qed

*ₛ-assoc : a *ₛ b *ₛ c == a *ₛ (b *ₛ c)
*ₛ-assoc {a = zero} = refl
*ₛ-assoc {a = suc a} {zero} = refl
*ₛ-assoc {a = suc a} {suc b} {zero} = refl
*ₛ-assoc {a = suc a} {suc b} {suc c} = suc ` p
  where p : a +ₛ b +ₛ (a *ₛ b) +ₛ c +ₛ (a +ₛ b +ₛ a *ₛ b) *ₛ c ==
            a +ₛ (b +ₛ c +ₛ b *ₛ c) +ₛ a *ₛ (b +ₛ c +ₛ b *ₛ c)
{-        p = proof
          b +ₛ (a *ₛ b) +ₛ c +ₛ (a +ₛ b +ₛ a *ₛ b) *ₛ c
          〈 _==_ 〉-[ ? ]
          ?
          〈 _==_ 〉-[ ? ]
          (b +ₛ c +ₛ b *ₛ c) +ₛ a *ₛ (b +ₛ c +ₛ b *ₛ c)
        qed
-}
-}
