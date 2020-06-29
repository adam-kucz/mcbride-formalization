{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Computation.Property.Equivalence
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Computation.Definition

open import Data.Nat hiding (_⊔_)
open import Relation.Binary
  renaming (refl-trans-close to rtc)
open import Proof

open import Syntax
open import Syntax.Context
open import Substitution
open import ParallelReduction
open import Computation.Property.General
open import Computation.Proof

instance
  ↠-expl⊆↠ : (_↠-expl_ {n = n}{tag}) ⊆ _↠_
  ↠⊆↠-expl : (_↠_ {n = n}{tag}) ⊆ _↠-expl_

open import Logic

subrel ⦃ ↠-expl⊆↠ ⦄ = go
  where go : {x y : expr-of-type tag n}(p : x ↠-expl y) → x ↠ y
        go (β π {s = s}{s'}{S}{S'}{t}{t'}{T}{T'} t↠t' S↠S' T↠T' s↠s') =
          step (β π s S t T) $
          liftSub-to-↠ (newSub (s ꞉ S))(newSub (s' ꞉ S'))
            (ctx-closed (— ꞉ —)(go t↠t' , go T↠T')) $
          ap newSub $
          ctx-closed (— ꞉ —)(go s↠s' , go S↠S')
        go (v {t = t}{t'} T p) = step (v t T) $ go p
        go (⋆ i) = refl (⋆ i)
        go ([ π x: p₀ ]→ p₁) = ctx-closed ([ π x: — ]→ —)(go p₀ , go p₁)
        go (λx, p) = ctx-closed (λx, —) $ go p
        go ⌊ p ⌋ = ctx-closed ⌊ — ⌋ $ go p
        go (p₀ ` p₁) = ctx-closed (— ` —)(go p₀ , go p₁)
        go (p₀ ꞉ p₁) = ctx-closed (— ꞉ —)(go p₀ , go p₁)
subrel ⦃ ↠⊆↠-expl ⦄ = go
  where go : {x y : expr-of-type tag n}(p : x ↠ y) → x ↠-expl y
        go (rfl t) = {!refl t!}
        go (step aRb p) = {!!}
