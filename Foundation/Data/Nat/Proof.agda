{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Data.Nat.Proof where

open import Foundation.PropUniverses
open import Foundation.Prop'.Identity hiding (refl)
open import Foundation.Data.Nat
open import Foundation.Data.Nat.Order
open import Foundation.Logic
open import Foundation.Relation.Binary.Instances
open import Foundation.Proof

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

-- Relating-suc-≤ : Relating suc _≤_ _≤_
-- rel-preserv ⦃ Relating-suc-≤ ⦄ (refl ∨∅) = rflx
-- rel-preserv ⦃ Relating-suc-≤ ⦄ (∅∨ a<b) = ∅∨ (suc ` a<b)

--   Postfix+- : Postfix (b +_) _≤_
--   postfix ⦃ Postfix+- {zero} ⦄ = rflx
--   postfix ⦃ Postfix+- {suc b} ⦄ {a} =
--     proof a
--       〉 _≤_ 〉 suc a     :by: ∅∨ self<s
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

