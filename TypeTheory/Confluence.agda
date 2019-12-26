{-# OPTIONS --exact-split --prop --safe #-}
open import TypeTheory.Basic using (Rig; wfs)
open import Foundation.PropUniverses

module TypeTheory.Confluence
  {𝑅 : 𝒰 ˙} ⦃ r : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import TypeTheory.Syntax using (Var; Term; Elim; expr-of-type)
open Term; open Elim
open import TypeTheory.Substitution using (Sub; sub; lift)
open import TypeTheory.ParallelReduction using (_▷_)
open _▷_

-- Lemma 14 (vectorized substitution)

open import Foundation.Data.Nat using (suc)
open import Foundation.Relation.Binary.Property using (refl)
open import Foundation.Prop'.Proof

private
  liftSubVec : ∀ {m n}
    (σ σ' : Sub m n)
    (𝒆▷𝒆' : (v : Var m) → σ v ▷ σ' v)
    → -------------------------------
    (v : Var (suc m)) → (lift σ) v ▷ (lift σ') v
  liftSubVec σ σ' 𝒆▷𝒆' Var.new = refl (var Var.new)
  liftSubVec σ σ' 𝒆▷𝒆' (Var.old v) = {!𝒆▷𝒆' v!}

liftSub-to-▷ : ∀ {m n} {tag}
  (σ σ' : Sub m n)
  {t t' : expr-of-type tag m}
  (t▷t' : t ▷ t')
  (𝒆▷𝒆' : (v : Var m) → σ v ▷ σ' v)
  → ------------------------------
  sub σ t ▷ sub σ' t'
liftSub-to-▷ σ σ' (sort i) 𝒆▷𝒆' = refl (⋆ i)
liftSub-to-▷ σ σ' (pi π {S} {S'} {T} {T'} S▷S' T▷T') 𝒆▷𝒆' =
  pi π (liftSub-to-▷ σ σ' S▷S' 𝒆▷𝒆')
       (liftSub-to-▷ (lift σ) (lift σ')
       T▷T'
       (liftSubVec σ σ' 𝒆▷𝒆'))
liftSub-to-▷ σ σ' (lam t▷t') 𝒆▷𝒆' = {!!}
liftSub-to-▷ σ σ' (elim t▷t') 𝒆▷𝒆' = {!!}
liftSub-to-▷ σ σ' (elim-comp t▷t' t▷t'') 𝒆▷𝒆' = {!!}
liftSub-to-▷ σ σ' (var v) 𝒆▷𝒆' = {!!}
liftSub-to-▷ σ σ' (app t▷t' t▷t'') 𝒆▷𝒆' = {!!}
liftSub-to-▷ σ σ' (annot t▷t' t▷t'') 𝒆▷𝒆' = {!!}
liftSub-to-▷ σ σ' (lam-comp π t▷t' t▷t'' t▷t''' t▷t'''') 𝒆▷𝒆' = {!!}
        -- go : ∀ {m} {t t' : expr-of-type tag m}
        --   (t▷t' : t ▷ t')
        --   → ---------------------------
        --   sub σ t ▷ sub σ' t'
        -- go (sort i) = refl (⋆ i)
        -- go (pi π {S} {S'} {T} {T'} S▷S' T▷T') =
        --   
        -- go (lam t▷t') = {!!}
        -- go (elim t▷t') = {!!}
        -- go (elim-comp t▷t' t▷t'') = {!!}
        -- go (var v) = {!!}
        -- go (app t▷t' t▷t'') = {!!}
        -- go (annot t▷t' t▷t'') = {!!}
        -- go (lam-comp π t▷t' t▷t'' t▷t''' t▷t'''') = {!!}
