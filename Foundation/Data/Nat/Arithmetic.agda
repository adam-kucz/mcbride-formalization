{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Data.Nat.Arithmetic where

open import Foundation.PropUniverses
open import Foundation.Data.Nat.Arithmetic.Definition public
open import Foundation.Data.Nat
open import Foundation.Prop'.Function using (_$_)

open import Foundation.Operation.Binary.Instances using (Commutative; comm)
open import Foundation.Structure.Semigroup using (Semigroup; assoc)
open import Foundation.Structure.Monoid using (Monoid; e; right-unit; left-unit; swap)
open import Foundation.Structure.Hemiring

open import Foundation.Prop'.Identity hiding (refl)
open import Foundation.Prop'.Identity.Instances
open import Foundation.Proof

private
  variable
    a b c : ℕ

+suc : a + suc b == suc (a + b)
+suc {zero} {b} = refl (suc b)
+suc {suc a} {b} = ap suc +suc

instance
  Semigroupℕ+ : Semigroup _+_
  assoc ⦃ Semigroupℕ+ ⦄ zero b c = refl (b + c)
  assoc ⦃ Semigroupℕ+ ⦄ (suc a) b c = ap suc $ assoc a b c

  Monoidℕ+ : Monoid _+_
  e ⦃ Monoidℕ+ ⦄ = 0
  left-unit ⦃ Monoidℕ+ ⦄ = refl
  right-unit ⦃ Monoidℕ+ ⦄ zero = refl zero
  right-unit ⦃ Monoidℕ+ ⦄ (suc a) = ap suc $ right-unit a

  Commutativeℕ+ : Commutative _+_
  comm ⦃ Commutativeℕ+ ⦄ 0 b = sym $ right-unit b
  comm ⦃ Commutativeℕ+ ⦄ (suc a) b = 
    proof
      suc a + b
        〉 _==_ 〉 suc (b + a) :by: ap suc (comm a b)
        〉 _==_ 〉 b + suc a :by: sym +suc
    qed

*-suc : (a b : ℕ) → a * suc b == a + a * b
*-suc zero _ = refl zero
*-suc (suc a) b = ap suc
  (proof
    b + a * suc b
      〉 _==_ 〉 b + (a + a * b) :by: ap (b +_) $ *-suc a b
      〉 _==_ 〉 a + (b + a * b) :by: swap b a (a * b)
  qed)

private
  *-0 : (a : ℕ) → a * zero == zero
  *-0 zero = refl zero
  *-0 (suc a) = *-0 a

  *-+-distrib : (a b c : ℕ) → a * (b + c) == a * b + a * c
  *-+-distrib zero _ _ = refl zero
  *-+-distrib (suc a) b c =
    proof b + c + a * (b + c)
      〉 _==_ 〉 (b + c) + (a * b + a * c)
        :by: ap (b + c +_) $ *-+-distrib a b c
      〉 _==_ 〉 b + (c + (a * b + a * c))
        :by: sym $ assoc b c _
      〉 _==_ 〉 b + (a * b + (c + a * c))
        :by: ap (b +_) $ swap c (a * b) _
      〉 _==_ 〉 b + a * b + (c + a * c)
        :by: assoc b _ _
    qed

instance
  Commutativeℕ* : Commutative _*_
  comm ⦃ Commutativeℕ* ⦄ zero b = sym $ *-0 b
  comm ⦃ Commutativeℕ* ⦄ (suc a) b = 
    proof b + a * b
      〉 _==_ 〉 b + b * a :by: ap (b +_) $ comm a b
      〉 _==_ 〉 b * suc a :by: sym $ *-suc b a
    qed

  Semigroupℕ* : Semigroup _*_
  assoc ⦃ Semigroupℕ* ⦄ zero _ _ = refl zero
  assoc ⦃ Semigroupℕ* ⦄ (suc a) b c = 
    proof
      b * c + a * (b * c)
        〉 _==_ 〉 b * c + (a * b) * c :by: ap (b * c +_) $ assoc a b c
        〉 _==_ 〉 b * c + c * (a * b) :by: ap (b * c +_) $ comm (a * b) c
        〉 _==_ 〉 c * b + c * (a * b) :by: ap (_+ c * (a * b)) $ comm b c
        〉 _==_ 〉 c * (b + a * b)     :by: sym $ *-+-distrib c b (a * b)
        〉 _==_ 〉 (b + a * b) * c     :by: comm c _
    qed

  Monoidℕ* : Monoid _*_
  e ⦃ Monoidℕ* ⦄ = 1
  right-unit ⦃ Monoidℕ* ⦄ 0 = refl 0
  right-unit ⦃ Monoidℕ* ⦄ (suc a) = ap suc $ right-unit a
  left-unit ⦃ Monoidℕ* ⦄ = right-unit {_∙_ = _+_}

  Hemiringℕ+* : Hemiring _+_ _*_
  monoid+ ⦃ Hemiringℕ+* ⦄ = Monoidℕ+
  0* ⦃ Hemiringℕ+* ⦄ _ = refl 0
  *0 ⦃ Hemiringℕ+* ⦄ = *-0
  *[+]==*+* ⦃ Hemiringℕ+* ⦄ = *-+-distrib
  [+]*==*+* ⦃ Hemiringℕ+* ⦄ a b c = 
    proof
      (a + b) * c
        〉 _==_ 〉 c * (a + b)   :by: comm (a + b) c
        〉 _==_ 〉 c * a + c * b :by: *[+]==*+* c a b
        〉 _==_ 〉 c * a + b * c :by: ap (c * a +_) $ comm c b
        〉 _==_ 〉 a * c + b * c :by: ap (_+ b * c) $ comm c a
    qed