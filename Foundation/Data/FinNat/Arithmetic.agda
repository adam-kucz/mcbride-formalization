{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Data.FinNat.Arithmetic where

open import Foundation.Data.Nat as Nat hiding (Injective-suc)
open import Foundation.Data.Nat.Arithmetic
open import Foundation.Data.Nat.Order
open import Foundation.Data.FinNat
open import Foundation.Prop'.Identity using (_==_; refl; ap)
open import Foundation.Prop'.Function renaming (_$_ to _$'_) using ()
open import Foundation.Function using (_∘_; _$_)
open import Foundation.Logic

open import Foundation.Operation.Binary.Instances using (Commutative; comm)
open import Foundation.Structure.Semigroup using (Semigroup; assoc)
open import Foundation.Structure.Monoid using (Monoid; e; right-unit; left-unit; swap)
open import Foundation.Structure.Hemiring
  using (Hemiring; *0; 0*; *[+]==*+*; [+]*==*+*)

open import Foundation.Proof
open import Foundation.Data.Nat.Proof
open import Foundation.Prop'.Decidable using (decide; true; false)
open import Foundation.Prop'.Identity.Instances renaming (refl to rflx)

private
  variable
    n m : ℕ

-- return n if n fits in Finℕ (m + 1) [i.e. when n ≤ m]
-- otherwise return the largest element of Finℕ (m + 1)
cap : (m n : ℕ) → Finℕ (suc m)
cap m n = toFinℕ {suc m} (min m n) min<s

-- _≤ₛ_ : Finℕ n → Finℕ n → Prop
-- a ≤ₛ b = a == b ∨ a <ₛ b

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

cap== : ∀ {l m n} → m == n → cap l m == cap l n
cap== {l} (refl m) = refl (cap l m)

cap-n-zero==zero : ∀ {n} → cap n zero == Finℕ.zero
cap-n-zero==zero {n} = 
  proof cap n zero
    〉 _==_ 〉 toFinℕ (min n zero) min<s :by: refl (cap n zero)
    〉 _==_ 〉 toFinℕ zero z<s
      :by: {!!} -- congₚ {b' = z<s} toFinℕ min-zero (ap (_< suc n) min-zero)
    〉 _==_ 〉 zero :by: refl zero
  qed
  where min-zero : ∀ {n} → min n 0 == 0
        min-zero {zero} = refl 0
        min-zero {suc n} = refl 0

cap-suc== :
  ∀ {l m n} →
  (eq : cap (suc l) m == cap (suc l) n)
  → ------------------------------------
  cap l m == cap l n
cap-suc== {l} {zero} {zero} eq = refl (cap l 0)
cap-suc== {zero} {suc m} {suc n} eq = refl zero
cap-suc== {suc l} {suc m} {suc n} eq = ap suc $' cap-suc== {l} {m} {n} {!!} -- (inj eq)
  
cap-toℕ : {a : Finℕ (suc n)} → cap n (toℕ a) == a
cap-toℕ {zero} {zero} = refl 0
cap-toℕ {suc n} {zero} = refl 0
cap-toℕ {suc n} {suc a} = ap suc $' cap-toℕ {n} {a}

toℕ-cap-fit : (n<sm : n < suc m) → toℕ (cap m n) == n
toℕ-cap-fit {zero} {zero} _ = refl 0
toℕ-cap-fit {zero} {suc _} _ = refl 0
toℕ-cap-fit {suc _} {zero} (s<s ())
toℕ-cap-fit {suc n} {suc m} (s<s n<sm) = ap suc $' toℕ-cap-fit n<sm

toℕ-cap-overflow : (¬n<sm : ¬ n < suc m) → toℕ (cap m n) == m
toℕ-cap-overflow {zero} ¬n<sm = ⊥-recursion _ (¬n<sm z<s)
toℕ-cap-overflow {suc _} {zero} _ = refl 0
toℕ-cap-overflow {suc n} {suc m} ¬n<sm =
  ap suc $' toℕ-cap-overflow λ n<sm → ¬n<sm (s<s n<sm)

cap-thm :
  (f : ℕ → ℕ)
  (x<fx : ∀ {x} → x ≤ f x)
  → --------------------------------
  cap m (f (toℕ (cap m n))) == cap m (f n)
cap-thm {zero} {zero} _ _ = refl 0
cap-thm {suc m} {zero} f _ = refl (cap (suc m) (f 0))
cap-thm {zero} {suc _} _ _ = refl 0
cap-thm {suc m} {suc n} _ _ with decide (n < suc m)
cap-thm {suc m} {suc n} f _ | true n<sm = ap (cap (suc m) ∘ f ∘ suc) $' toℕ-cap-fit n<sm
cap-thm {suc m} {suc n} f x≤fx | false ¬n<sm =
  proof cap (suc m) ∘ f ∘ suc $ toℕ $ cap m n
    〉 _==_ 〉 cap (suc m) ∘ f ∘ suc $ m
      :by: ap (cap (suc m) ∘ f ∘ suc) $' toℕ-cap-overflow ¬n<sm
    〉 _==_ 〉 toFinℕ (min (suc m) (f $ suc m)) min<s
      :by: refl _
    〉 _==_ 〉 toFinℕ (min (suc m) (f $ suc n)) min<s
      :by: {!!} -- congₚ
--             {b' = min<s}
--             toFinℕ
--             min-sm-fsn==min-sm-fsm
--             (_< 2 + m ` min-sm-fsn==min-sm-fsm)
    〉 _==_ 〉 cap (suc m) $ f $ suc $ n  :by: refl (cap (suc m) (f $ suc n))
  qed
  where sm<fsn : suc m < f (suc n)
        min-sm-fsn==min-sm-fsm : min (suc m) (f $ suc m) == min (suc m) (f $ suc n)
        min-sm-fsn==min-sm-fsm =
          proof min (suc m) (f $ suc m)
            〉 _==_ 〉 suc m                   :by: ≤→min== x≤fx
            〉 _==_ 〉 min (suc m) (f $ suc n) :by: sym $' ≤→min== (∨right sm<fsn)
          qed
        sm<fsn with ⟵ ≤↔¬< ¬n<sm
        sm<fsn | (∨left (refl _)) =
          proof suc m
            〉 _<_ 〉 2 + m     :by: self<s
            〉 _≤_ 〉 f (2 + m) :by: x≤fx
          qed
        sm<fsn | (∨right sm<n) =
          proof suc m
            〉 _<_ 〉 n         :by: sm<n
            〉 _<_ 〉 suc n     :by: self<s
            〉 _≤_ 〉 f (suc n) :by: x≤fx
          qed

infixl 20 _+ₛ_
_+ₛ_ : (x : Finℕ n) (y : Finℕ n) → Finℕ n
_+ₛ_ {suc n} x y = cap n $ toℕ x + toℕ y

infixl 21 _*ₛ_
_*ₛ_ : (x : Finℕ n) (y : Finℕ n) → Finℕ n
_*ₛ_ {suc n} x y = cap n $ toℕ x * toℕ y

instance
  CommutativeFinℕ+ : Commutative (_+ₛ_ {n})
  comm ⦃ CommutativeFinℕ+ {suc n} ⦄ a b = ap (cap n) $' comm (toℕ a) (toℕ b)

  SemigroupFinℕ+ : Semigroup (_+ₛ_ {n})
  assoc ⦃ SemigroupFinℕ+ {suc n} ⦄ a b c = 
    proof a +ₛ (b +ₛ c)
      〉 _==_ 〉 cap n $ toℕ a + toℕ (cap n $ toℕ b + toℕ c) :by: refl (a +ₛ (b +ₛ c))
      〉 _==_ 〉 cap n $ toℕ a + (toℕ b + toℕ c)
        :by: cap-thm (toℕ a +_) {!!} -- postfix
      〉 _==_ 〉 cap n $ (toℕ a + toℕ b) + toℕ c
        :by: ap (cap n) $' assoc (toℕ a) (toℕ b) (toℕ c)
      〉 _==_ 〉 cap n $ toℕ (cap n $ toℕ a + toℕ b) + toℕ c
        :by: sym $' cap-thm (_+ toℕ c) {!!} -- postfix 
      〉 _==_ 〉 a +ₛ b +ₛ c :by: refl (a +ₛ b +ₛ c)
    qed
  
  MonoidFinℕ+ : Monoid (_+ₛ_ {suc n})
  e ⦃ MonoidFinℕ+ ⦄ = 0
  right-unit ⦃ MonoidFinℕ+ {n} ⦄ a = proof
    cap n (toℕ a + 0)
      〉 _==_ 〉 cap n (toℕ a) :by: ap (cap n) $' right-unit (toℕ a)
      〉 _==_ 〉 a             :by: cap-toℕ
  left-unit ⦃ MonoidFinℕ+ ⦄ a = cap-toℕ

  CommutativeFinℕ* : Commutative (_*ₛ_ {n})
  comm ⦃ CommutativeFinℕ* {suc n} ⦄ a b = ap (cap n) $' comm (toℕ a) (toℕ b)

  SemigroupFinℕ* : Semigroup (_*ₛ_ {n})
  assoc ⦃ SemigroupFinℕ* {suc n} ⦄ zero b c =
    proof cap n zero
      〉 _==_ 〉 cap n (toℕ (Finℕ.zero {n}) * toℕ c) :by: refl (cap n zero)
      〉 _==_ 〉 cap n (toℕ (cap n zero) * toℕ c)
        :by: ap (λ – → cap n (toℕ – * toℕ c)) $' sym $' cap-n-zero==zero {n}
    qed
    where 
  assoc ⦃ SemigroupFinℕ* {suc n} ⦄ (suc a) b zero = ap (cap n) $'
    (proof toℕ (suc a) * toℕ (cap n (toℕ b * 0))
      〉 _==_ 〉 toℕ (suc a) * toℕ (cap n 0)
        :by: ap (λ – → toℕ (suc a) * toℕ (cap n –)) $' *0 (toℕ b)
      〉 _==_ 〉 toℕ (suc a) * 0
        :by: ap (λ – → toℕ (suc a) * toℕ –) $' cap-n-zero==zero {n}
      〉 _==_ 〉 0                    :by: *0 (toℕ $ suc a)
      〉 _==_ 〉 toℕ (suc a *ₛ b) * 0 :by: sym $' *0 (toℕ $ suc a *ₛ b)
    qed)
  assoc ⦃ SemigroupFinℕ* {suc n} ⦄ (suc a) b (suc c) =
    proof suc a *ₛ (b *ₛ suc c)
      〉 _==_ 〉 cap n $ suc (toℕ a) * toℕ (cap n $ toℕ b * suc (toℕ c))
        :by: refl (suc a *ₛ (b *ₛ suc c))
      〉 _==_ 〉 cap n $ suc (toℕ a) * (toℕ b * suc (toℕ c))
        :by: cap-thm (suc (toℕ a) *_) {!!} -- (postfix ⦃ Postfix*- {toℕ a} ⦄)
      〉 _==_ 〉 cap n $ (suc (toℕ a) * toℕ b) * suc (toℕ c)
        :by: ap (cap n) $' assoc (suc $ toℕ a) (toℕ b) (suc $ toℕ c)
      〉 _==_ 〉 cap n $ toℕ (cap n $ suc (toℕ a) * toℕ b) * suc (toℕ c)
        :by: sym $' cap-thm (_* suc (toℕ c)) {!!} -- postfix
      〉 _==_ 〉 suc a *ₛ b *ₛ suc c
        :by: refl (suc a *ₛ b *ₛ suc c)
    qed
  
  MonoidFinℕ* : Monoid (_*ₛ_ {suc n})
  e ⦃ MonoidFinℕ* {zero} ⦄ = 0
  e ⦃ MonoidFinℕ* {suc n} ⦄ = 1
  right-unit ⦃ MonoidFinℕ* {zero} ⦄ zero = refl 0
  right-unit ⦃ MonoidFinℕ* {suc n} ⦄ a =
    proof cap (suc n) (toℕ a * 1)
      〉 _==_ 〉 cap (suc n) (toℕ a) :by: ap (cap (suc n)) $' right-unit (toℕ a)
      〉 _==_ 〉 a                   :by: cap-toℕ
    qed
  left-unit ⦃ MonoidFinℕ* ⦄ a =
    proof e *ₛ a
      〉 _==_ 〉 a *ₛ e :by: comm e a
      〉 _==_ 〉 a :by: right-unit a
    qed

  HemiringFinℕ+* : Hemiring (_+ₛ_ {suc n}) _*ₛ_
  Hemiring.monoid+ HemiringFinℕ+* = MonoidFinℕ+
  0* ⦃ HemiringFinℕ+* ⦄ _ = cap-n-zero==zero
  *0 ⦃ HemiringFinℕ+* ⦄ a =
    proof a *ₛ 0
      〉 _==_ 〉 0 *ₛ a :by: comm a 0
      〉 _==_ 〉 0     :by: 0* a
    qed
  *[+]==*+* ⦃ HemiringFinℕ+* {n} ⦄ zero b c = ap (cap n) $' sym $'
    (proof toℕ (cap n zero) + toℕ (cap n zero)
      〉 _==_ 〉 toℕ (cap n zero)
        :by: ap (λ – → toℕ – + toℕ (cap n zero)) $' cap-n-zero==zero {n}
      〉 _==_ 〉 zero :by: ap toℕ $' cap-n-zero==zero {n}
    qed)
  *[+]==*+* ⦃ HemiringFinℕ+* {n} ⦄ (suc a) b c =
    proof suc a *ₛ (b +ₛ c)
      〉 _==_ 〉 cap n (suc (toℕ a) * toℕ (cap n $ toℕ b + toℕ c))
        :by: refl (suc a *ₛ (b +ₛ c))
      〉 _==_ 〉 cap n (suc (toℕ a) * (toℕ b + toℕ c))
        :by: cap-thm (suc (toℕ a) *_) {!!} -- (postfix ⦃ Postfix*- {b = toℕ a} ⦄)
      〉 _==_ 〉 cap n (suc (toℕ a) * toℕ b + suc (toℕ a) * toℕ c)
        :by: ap (cap n) $' *[+]==*+* (suc $ toℕ a) (toℕ b) (toℕ c)
      〉 _==_ 〉 cap n (toℕ (cap n $ suc (toℕ a) * toℕ b) + suc (toℕ a) * toℕ c)
        :by: sym $' cap-thm (_+ suc (toℕ a) * toℕ c) {!!} -- postfix
      〉 _==_ 〉 cap n (toℕ (suc a *ₛ b) + toℕ (cap n $ suc (toℕ a) * toℕ c))
        :by: sym $' cap-thm (toℕ (suc a *ₛ b) +_) {!!} -- postfix
      〉 _==_ 〉 suc a *ₛ b +ₛ suc a *ₛ c :by: refl (suc a *ₛ b +ₛ suc a *ₛ c)
    qed
  [+]*==*+* ⦃ HemiringFinℕ+* ⦄ a b c =
    proof
      (a +ₛ b) *ₛ c
        〉 _==_ 〉 c *ₛ (a +ₛ b) :by: comm (a +ₛ b) c
        〉 _==_ 〉 c *ₛ a +ₛ c *ₛ b :by: *[+]==*+* c a b
        〉 _==_ 〉 c *ₛ a +ₛ b *ₛ c :by: ap (c *ₛ a +ₛ_) $' comm c b
        〉 _==_ 〉 a *ₛ c +ₛ b *ₛ c :by: ap (_+ₛ b *ₛ c) $' comm c a
    qed
