{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic

module Computation.Property.VectorizedSubstitution
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Computation.Definition
open import Computation.Property
open import ParallelReduction.Property.VectorizedSubstitution

open import Relation.Binary renaming (refl-trans-close to rtc)
open import Relation.Binary.Pointwise
open import Proof

open import Syntax
open import Syntax.Context
open import Substitution
open import ParallelReduction
open import Computation.Proof

-- TODO: include pointwise-(rtc of reflexive R) commutativity
-- in the standard library
liftSub-to-↠ : ∀{m n}{tag}
  (σ σ' : Sub m n)
  {t t' : expr-of-type tag m}
  (t↠t' : t ↠ t')
  (e↠e' : Pointwise _↠_ σ σ')
  → ------------------------------
  sub σ t ↠ sub σ' t'
liftSub-to-↠ σ σ' t↠t' e↠e' =
  go σ σ' (subrel {_P_ = rtc _▷_} t↠t') e↠e'
  where go : ∀{m n}{tag}
             (σ σ' : Sub m n)
             {t t' : expr-of-type tag m}
             (t▷*t' : (rtc _▷_) t t')
             (e↠e' : Pointwise _↠_ σ σ')
             → ------------------------------
             sub σ t ↠ sub σ' t'
        go σ σ' (rfl t) = liftSub-refl σ σ' t
        go σ σ' (step {t}{t'}{t″} t▷t' t'▷*t″) e↠e' =
          proof sub σ t
            〉 _↠_ 〉 sub σ t'
              :by: subrel {_R_ = _▷_} $ ap (sub σ) ⦃ Relating-sub-▷ ⦄ t▷t'
                   [: _↠_ ]
            〉 _↠_ 〉 sub σ' t″ :by: go σ σ' t'▷*t″ e↠e'
          qed



