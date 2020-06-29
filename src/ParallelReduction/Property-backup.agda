{-# OPTIONS --exact-split --prop #-}
open import Basic using (Rig; wfs)
open import PropUniverses

module ParallelReduction.Property
  {𝑅 : 𝒰 ˙} ⦃ rig : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import ParallelReduction.Definition
open import Syntax
open import Syntax.Context

open import Type.Sum hiding (_,_)
open import Data.Nat
open import Logic
open import Proof

-- annot-▷-form :
--   {t T : Term n}{e e' : Elim n}
--   (p : e ▷ e')
--   (q : e == t ꞉ T)
--   → --------------------------------
--   ∃ λ t' → ∃ λ T' → e' == t' ꞉ T'
-- annot-▷-form {t = t}{T} (ctx (elim e) es es' p) q = t , (T , q)
-- annot-▷-form (ctx — es es' p) q = annot-▷-form p q
-- annot-▷-form (ctx (C₀ ꞉ C₁) (e₀ Σ., e₁) (e₀' Σ., e₁') (p₀ , p₁)) q =
--   fill-holes e₀' C₀ , (fill-holes e₁' C₁ , Id-refl _)
