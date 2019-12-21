{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Data.Nat.Proof where

open import Foundation.PropUniverses
open import Foundation.Prop'.Identity hiding (refl)
open import Foundation.Data.Nat.Order
open import Foundation.Logic

open import Foundation.Data.Nat.Defintion

open import Foundation.Prop'.Identity.Instances
open import Foundation.Relation.Binary.Instances
open import Foundation.Operation.Binary.Instances

open import Foundation.Proof
open import Foundation.Prop'.Proof
open import Foundation.Function.Proof

open Composable ⦃ ... ⦄ public

instance
  Transitive< : Transitive _<_
  trans ⦃ Transitive< ⦄ = <transitive

  Irreflexive< : Irreflexive _<_
  irrefl ⦃ Irreflexive< ⦄ = <irrefl

  Asym< : Asymmetric _<_
  asym ⦃ Asym< ⦄ = <asym

  comp-<-== : Composable 𝒰₀ _<_ _==_
  comp-<-== = composable-R-== _<_

  comp-==-< : Composable 𝒰₀ _==_ _<_
  comp-==-< = composable-==-R _<_

  Reflexive≤ : Reflexive _≤_
  refl ⦃ Reflexive≤ ⦄ = ≤reflexive
  
  Transitive≤ : Transitive _≤_
  trans ⦃ Transitive≤ ⦄ = ≤transitive
  
  Antisym≤ : Antisymmetric _≤_
  antisym ⦃ Antisym≤ ⦄ = ≤antisym

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

  Commutative-min : Commutative min
  comm ⦃ Commutative-min ⦄ = commutative-min

  Relating-min-right : ∀ {n} → Relating (min n) _≤_ _≤_
  rel-preserv ⦃ Relating-min-right {n} ⦄ (∨left (Idₚ.refl x)) = refl (min n x)
  rel-preserv ⦃ Relating-min-right {zero} ⦄ (∨right x) = refl 0
  rel-preserv ⦃ Relating-min-right {suc n} ⦄ (∨right z<s) = ∨right z<s
  rel-preserv ⦃ Relating-min-right {suc n} ⦄ {suc m} {suc m'} (∨right (s<s m<m')) =
    have
      min n m ≤ min n m' :from: rel-preserv ⦃ Relating-min-right {n} ⦄ (∨right m<m')
      ⟶ suc (min n m) ≤ suc (min n m') :by: ⟶ -≤-↔s≤s

  Relating-min-left : ∀ {n} → Relating (λ m → min m n) _≤_ _≤_
  rel-preserv ⦃ Relating-min-left {n} ⦄ {a} {b} a≤b =
    proof min a n
      〉 _==_ 〉 min n a :by: comm a n
      〉 _≤_ 〉 min n b :by: rel-preserv a≤b
      〉 _==_ 〉 min b n :by: comm n b
    qed

  Relating-pred-≤ : Relating pred _≤_ _≤_
  rel-preserv ⦃ Relating-pred-≤ ⦄ (∨left (Idₚ.refl x)) = refl (pred x)
  rel-preserv ⦃ Relating-pred-≤ ⦄ (∨right (z<s {0})) = ∨left (refl 0)
  rel-preserv ⦃ Relating-pred-≤ ⦄ (∨right (z<s {suc n})) = ∨right z<s
  rel-preserv ⦃ Relating-pred-≤ ⦄ (∨right (s<s q)) = ∨right q

  Relating-suc-≤ : Relating suc _≤_ _≤_
  rel-preserv ⦃ Relating-suc-≤ ⦄ (∨left (Idₚ.refl x)) = ?
  rel-preserv ⦃ Relating-suc-≤ ⦄ (∨right a<b) = ∨right (ap suc a<b)

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
