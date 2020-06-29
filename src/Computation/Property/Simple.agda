{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic

module Computation.Property.Simple
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Computation.Definition

open import Data.Nat
open import Syntax ⦃ rig ⦄ ⦃ wfs ⦄
open import Syntax.Context ⦃ rig ⦄ ⦃ wfs ⦄
open import Proof

sorts-don't-reduce : {i : S}{e e' : Term n}
  (p : e ⇝ e')
  → --------------------------------
  e ≠ ⋆ {n = n} i
sorts-don't-reduce (v _ _) ()
sorts-don't-reduce (hole — p) (Id.refl (⋆ i)) =
  sorts-don't-reduce p $ Id.refl (⋆ i)
sorts-don't-reduce (hole [ π x: S ]→ C ↓ p) ()
sorts-don't-reduce (hole ([ π x: C ↓]→ T) p) ()
sorts-don't-reduce (hole (λx, C) p) ()
sorts-don't-reduce (hole ⌊ C ⌋ p) ()

open import Logic

pi-reduct-forms : ∀ {π : R}
  {e e' S : Term n}{T}
  (p : e ⇝ e')
  (q : e == [ π x: S ]→ T)
  → --------------------------------
  (∃ λ S' → S ⇝ S' ∧ e' == [ π x: S' ]→ T)
  ∨
  (∃ λ T' → T ⇝ T' ∧ e' == [ π x: S ]→ T')
pi-reduct-forms (hole — p) q = pi-reduct-forms p q
pi-reduct-forms (hole {t = t} [ π x: S ]→ C[—] ↓ p)(Id.refl _) =
  ∨right (C[—] [ t /—] , (hole C[—] p , Id.refl _))
pi-reduct-forms (hole {t = t} ([ π x: C[—] ↓]→ T) p)(Id.refl _) =
  ∨left (C[—] [ t /—] , (hole C[—] p , Id.refl _))

open import Type.Sum renaming (_,_ to _Σ,_; _×_ to _χ_)

pi-compute-forms : ∀ {π : R}
  {S : Term n}{T : Term (n +1)}{e' : Term n}
  (p : [ π x: S ]→ T ↠ e')
  → --------------------------------
  ∃ {X = Term n χ Term (n +1)}
    (λ {(S' Σ, T') → S ↠ S' ∧ T ↠ T' ∧ e' == [ π x: S' ]→ T'})
pi-compute-forms (rfl ([ π x: S ]→ T)) =
  (S Σ, T) , (refl S , refl T , refl ([ π x: S ]→ T))
pi-compute-forms (step [πx:S]→T⇝e″ p)
  with pi-reduct-forms [πx:S]→T⇝e″ (Id.refl _)
pi-compute-forms (step [πx:S]→T⇝e″ p)
  | ∨left (S″ , (S⇝S″ , Id.refl _)) with pi-compute-forms p
pi-compute-forms (step [πx:S]→T⇝e″ p)
  | ∨left (S″ , (S⇝S″ , Id.refl _))
  | (S' Σ, T') , (S″↠S' , T↠T' , Id.refl _) =
  (S' Σ, T') , (step S⇝S″ S″↠S' , T↠T' , Id.refl _)
pi-compute-forms (step [πx:S]→T⇝e″ p)
  | ∨right (T″ , (T⇝T″ , Id.refl _)) with pi-compute-forms p
pi-compute-forms (step [πx:S]→T⇝e″ p)
  | ∨right (T″ , (T⇝T″ , Id.refl _))
  | (S' Σ, T') , (S↠S' , T″↠T' , Id.refl _) =
  (S' Σ, T') , (S↠S' , step T⇝T″ T″↠T' , Id.refl _)

annot-reduct-forms : ∀
  {e e' : Elim n}{t T}
  (p : e ⇝ e')
  (q : e == t ꞉ T)
  → --------------------------------
  (∃ λ t' → t ⇝ t' ∧ e' == t' ꞉ T)
  ∨
  (∃ λ T' → T ⇝ T' ∧ e' == t ꞉ T')
annot-reduct-forms (hole — p) (Id.refl (t ꞉ T)) =
  annot-reduct-forms p (Id.refl _)
annot-reduct-forms (hole {t = T'}(t ꞉ C[—] ↓) p)(Id.refl _) =
  ∨right (C[—] [ T' /—] , (hole C[—] p , Id.refl _))
annot-reduct-forms (hole {t = t'} (C[—] ↓꞉ T) p)(Id.refl _) =
  ∨left (C[—] [ t' /—] , (hole C[—] p , Id.refl _))

annot-compute-forms :
  {t T : Term n}{e' : Elim n}
  (p : t ꞉ T ↠ e')
  → --------------------------------
  ∃ {X = Term n χ Term n}
    (λ {(t' Σ, T') → t ↠ t' ∧ T ↠ T' ∧ e' == t' ꞉ T'})
annot-compute-forms (rfl (t ꞉ T)) = t Σ, T , (refl t , refl T , Id.refl _)
annot-compute-forms (step t꞉T⇝e' p)
  with annot-reduct-forms t꞉T⇝e' (Id.refl _)
... | ∨left (t' , (t⇝t' , Idₚ.refl (t' ꞉ T))) with annot-compute-forms p
... | t″ Σ, T″ , (t'↠t″ , T↠T″ , Idₚ.refl _) =
  t″ Σ, T″ , (step t⇝t' t'↠t″ , T↠T″ , Id.refl _)
annot-compute-forms (step t꞉T⇝e' p)
  | ∨right (T' , (T⇝T' , Idₚ.refl (t ꞉ T'))) with annot-compute-forms p
... | t″ Σ, T″ , (t↠t″ , T'↠T″ , Idₚ.refl _) =
  t″ Σ, T″ , (t↠t″ , step T⇝T' T'↠T″ , Id.refl _)
