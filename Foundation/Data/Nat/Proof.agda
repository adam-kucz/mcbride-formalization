{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Data.Nat.Proof where

open import Foundation.Data.Nat.Order

open import Foundation.PropUniverses
open import Foundation.Prop'.Identity hiding (refl)
open import Foundation.Logic

open import Foundation.Data.Nat.Definition

open import Foundation.Prop'.Identity.Property
open import Foundation.Relation.Binary.Property
open import Foundation.Operation.Binary.Property

open import Foundation.Proof
open import Foundation.Prop'.Proof
open import Foundation.Function.Proof

open Composable ⦃ ... ⦄ public

instance
  comp-<-== : Composable 𝒰₀ _<_ _==_
  comp-<-== = composable-R-== _<_

  comp-==-< : Composable 𝒰₀ _==_ _<_
  comp-==-< = composable-==-R _<_

  comp-≤-== : Composable 𝒰₀ _≤_ _==_
  comp-≤-== = composable-R-== _≤_

  comp-==-≤ : Composable 𝒰₀ _==_ _≤_
  comp-==-≤ = composable-==-R _≤_

  comp-<-≤ : Composable 𝒰₀ _<_ _≤_
  rel ⦃ comp-<-≤ ⦄ = _<_
  compose ⦃ comp-<-≤ ⦄ a<b (∨left (Idₚ.refl _)) = a<b
  compose ⦃ comp-<-≤ ⦄ a<b (∨right b<c) = trans a<b b<c

  comp-≤-< : Composable 𝒰₀ _≤_ _<_
  rel ⦃ comp-≤-< ⦄ = _<_
  compose ⦃ comp-≤-< ⦄ (∨right a<b) b<c = trans a<b b<c
  compose ⦃ comp-≤-< ⦄ (∨left (Idₚ.refl _)) b<c = b<c

  Relating-min-right : ∀ {n} → Relating (min n) _≤_ _≤_
  rel-preserv ⦃ Relating-min-right {n} ⦄ (∨left (Idₚ.refl x)) = refl (min n x)
  rel-preserv ⦃ Relating-min-right {zero} ⦄ (∨right x) = refl 0
  rel-preserv ⦃ Relating-min-right {suc n} ⦄ (∨right z<s) = ∨right z<s
  rel-preserv ⦃ Relating-min-right {suc n} ⦄ {suc m} {suc m'} (∨right (s<s m<m')) =
    have
      min n m ≤ min n m' :from: rel-preserv (∨right m<m')
      ⟶ suc (min n m) ≤ suc (min n m') :by: ap suc

  Relating-min-left : ∀ {n} → Relating (λ m → min m n) _≤_ _≤_
  rel-preserv ⦃ Relating-min-left {n} ⦄ {a} {b} a≤b =
    proof min a n
      〉 _==_ 〉 min n a :by: comm a n
      〉 _≤_ 〉 min n b :by: rel-preserv a≤b
      〉 _==_ 〉 min b n :by: comm n b
    qed

--   Postfix+- : Postfix (b +_) _≤_
--   postfix ⦃ Postfix+- {zero} ⦄ = rflx
--   postfix ⦃ Postfix+- {suc b} ⦄ {a} =
--     proof a
--       〉 _≤_ 〉 suc a     :by: ∨right self<s
--       〉 _≤_ 〉 b + suc a :by: postfix
--       〉 _==_ 〉 suc b + a :by: +suc
--     qed

--   Postfix-+ : Postfix (_+ b) _≤_
--   postfix ⦃ Postfix-+ {b} ⦄ {a} =
--     proof a
--       〉 _≤_ 〉 b + a :by: postfix
--       〉 _==_ 〉 a + b :by: +comm {a = b}
--     qed

--   Postfix*- : Postfix (suc b *_) _≤_
--   postfix ⦃ Postfix*- {b} ⦄ {a} =
--     proof a
--       〉 _≤_ 〉 a + b * a :by: postfix ⦃ Postfix-+ ⦄
--       〉 _==_ 〉 suc b * a :by: refl
--     qed

--   Postfix-* : Postfix (_* suc b) _≤_
--   postfix ⦃ Postfix-* {b} ⦄ {a} =
--     proof a
--       〉 _≤_ 〉 suc b * a :by: postfix ⦃ Postfix*- {b} ⦄
--       〉 _==_ 〉 a * suc b :by: +comm {a = suc b}
--     qed

