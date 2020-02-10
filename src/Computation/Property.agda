{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic

module Computation.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Computation.Basic

open import Proposition.Identity hiding (refl)
open import Data.Nat
open import Syntax

sorts-don't-reduce : {i : S}{e e' : Term n}
  (p : e ⇝ e')
  → --------------------------------
  e ≠ ⋆ {n = n} i
sorts-don't-reduce (v-exact (v _ _)) ()
sorts-don't-reduce (hole — p) = sorts-don't-reduce p

open import Logic
open import Proof

pi-reduct-forms : ∀ {π : R}
  {e e' S : Term n}{T}
  (p : e ⇝ e')
  (q : e == [ π x: S ]→ T)
  → --------------------------------
  (∃ λ S' → S ⇝ S' ∧ e' == [ π x: S' ]→ T)
  ∨
  (∃ λ T' → T ⇝ T' ∧ e' == [ π x: S ]→ T')
pi-reduct-forms (v-exact (v _ _)) ()
pi-reduct-forms (hole — p) q = pi-reduct-forms p q
pi-reduct-forms (hole {s = s}{t} [ ρ x: S ]→ C[—] ↓ p)
  (Id.refl ([ ρ x: S ]→ .(C[—] [ s /—]))) =
  ∨right (C[—] [ t /—] , (hole C[—] p , Id.refl _))
pi-reduct-forms (hole {s = s} {t} ([ ρ x: C[—] ↓]→ T) p)
  (Id.refl ([ ρ x: .(C[—] [ s /—]) ]→ T)) =
  ∨left (C[—] [ t /—] , (hole C[—] p , Id.refl _))

open import Type.Sum hiding (_,_)
open import Relation.Binary.ReflexiveTransitiveClosure
open import Proof

pi-compute-forms : ∀ {π : R}
  {S : Term n}{T}{e'}
  (p : [ π x: S ]→ T ↠ e')
  → --------------------------------
  ∃ {X = Term n × Term (n +1)}
    (λ {(S' Σ., T') → S ↠ S' ∧ T ↠ T' ∧ e' == [ π x: S' ]→ T'})
pi-compute-forms (rfl ([ π x: S ]→ T)) =
  (S Σ., T) , (refl S , refl T , refl ([ π x: S ]→ T))
pi-compute-forms (step [πx:S]→T⇝e″ p)
  with pi-reduct-forms [πx:S]→T⇝e″ (Id.refl _)
pi-compute-forms (step [πx:S]→T⇝e″ p)
  | ∨left (S″ , (S⇝S″ , Id.refl _)) with pi-compute-forms p
pi-compute-forms (step [πx:S]→T⇝e″ p)
  | ∨left (S″ , (S⇝S″ , Id.refl _))
  | (S' Σ., T') , (S″↠S' , T↠T' , Id.refl _) =
  (S' Σ., T') , (step S⇝S″ S″↠S' , T↠T' , Id.refl _)
pi-compute-forms (step [πx:S]→T⇝e″ p)
  | ∨right (T″ , (T⇝T″ , Id.refl _)) with pi-compute-forms p
pi-compute-forms (step [πx:S]→T⇝e″ p)
  | ∨right (T″ , (T⇝T″ , Id.refl _))
  | (S' Σ., T') , (S↠S' , T″↠T' , Id.refl _) =
  (S' Σ., T') , (S↠S' , step T⇝T″ T″↠T' , Id.refl _)

mk-pi-compute : ∀ (π : R){S S' : Term n}{T T'}
  (p : S ↠ S')
  (q : T ↠ T')
  → ----------------
  [ π x: S ]→ T ↠ [ π x: S' ]→ T'
mk-pi-compute π (rfl S) q = ctx-closed q ([ π x: S ]→ — ↓)
mk-pi-compute π {T = T} (step S⇝S″ S″↠S') q =
  step (hole ([ π x: — ↓]→ T) S⇝S″) (mk-pi-compute π S″↠S' q)
