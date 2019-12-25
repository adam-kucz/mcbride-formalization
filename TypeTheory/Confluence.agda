{-# OPTIONS --exact-split --prop --safe #-}
open import TypeTheory.Basic using (Rig; wfs)
open import Foundation.PropUniverses

module TypeTheory.Confluence
  {𝑅 : 𝒰 ˙} ⦃ r : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

-- Lemma 14 (vectorized substitution)

open import TypeTheory.Syntax using (Var; Term; Elim; expr-of-type)
open Term; open Elim
open import TypeTheory.Substitution using (Sub; sub)
open import TypeTheory.ParallelReduction using (_▷_)
open _▷_

open import Foundation.Relation.Binary.Property using (refl)

liftSub-to-▷ : ∀ {m n} {tag}
  (σ σ' : Sub m n)
  {t t' : expr-of-type tag m}
  (t▷t' : t ▷ t')
  (𝒆▷𝒆' : (v : Var m) → σ v ▷ σ' v)
  → ------------------------------
  sub σ t ▷ sub σ' t'
liftSub-to-▷ {m} {n} {tag} σ σ' t▷t' 𝒆▷𝒆' = go t▷t'
  where go : {t t' : expr-of-type tag m}
          (t▷t' : t ▷ t')
          → ---------------------------
          sub σ t ▷ sub σ' t'
        go (sort i) = refl (⋆ i)
        go (pi π t▷t' t▷t'') = {!!}
        go (lam t▷t') = {!!}
        go (elim t▷t') = {!!}
        go (elim-comp t▷t' t▷t'') = {!!}
        go (var v) = {!!}
        go (app t▷t' t▷t'') = {!!}
        go (annot t▷t' t▷t'') = {!!}
        go (lam-comp π t▷t' t▷t'' t▷t''' t▷t'''') = {!!}
