{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import Basic using (Rig; wfs)
open import PropUniverses

module Confluence
  {𝑅 : 𝒰 ˙} ⦃ r : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Syntax using (Var; Term; Elim; expr-of-type)
open Term; open Elim
open import Substitution using (Sub; sub; _[_/new]; lift; rename)
open import ParallelReduction using (_▷_)
open _▷_

-- Lemma 14 (vectorized substitution)

open import Data.Nat using (suc)
open import Proposition.Identity renaming (Idₚ to Id) using ()
open import Proof
open import Proposition.Proof
open import ParallelReduction.Proof

private
  liftSubVec : ∀ {m n}
    (σ σ' : Sub m n)
    (𝒆▷𝒆' : (v : Var m) → σ v ▷ σ' v)
    → -------------------------------
    (v : Var (suc m)) → lift σ v ▷ lift σ' v
  liftSubVec σ σ' 𝒆▷𝒆' Var.new = refl (var Var.new)
  liftSubVec σ σ' 𝒆▷𝒆' (Var.old v) = ap (rename Var.old) $ 𝒆▷𝒆' v

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
liftSub-to-▷ σ σ' (lam t▷t') 𝒆▷𝒆' =
  lam (liftSub-to-▷ (lift σ) (lift σ') t▷t' (liftSubVec σ σ' 𝒆▷𝒆'))
liftSub-to-▷ σ σ' (elim t▷t') 𝒆▷𝒆' = elim (liftSub-to-▷ σ σ' t▷t' 𝒆▷𝒆')
liftSub-to-▷ σ σ' (elim-comp t▷t' t▷t'') 𝒆▷𝒆' =
  elim-comp (liftSub-to-▷ σ σ' t▷t' 𝒆▷𝒆')
            (liftSub-to-▷ σ σ' t▷t'' 𝒆▷𝒆')
liftSub-to-▷ σ σ' (var v) 𝒆▷𝒆' = 𝒆▷𝒆' v
liftSub-to-▷ σ σ' (app t▷t' t▷t'') 𝒆▷𝒆' =
  app (liftSub-to-▷ σ σ' t▷t' 𝒆▷𝒆')
      (liftSub-to-▷ σ σ' t▷t'' 𝒆▷𝒆')
liftSub-to-▷ σ σ' (annot t▷t' t▷t'') 𝒆▷𝒆' =
  annot (liftSub-to-▷ σ σ' t▷t' 𝒆▷𝒆')
        (liftSub-to-▷ σ σ' t▷t'' 𝒆▷𝒆')
liftSub-to-▷ σ σ'
    (lam-comp π {t}{t'}{S}{S'}{T}{T'}{s}{s'} t▷t' t▷t'' t▷t''' t▷t'''')
    𝒆▷𝒆' =
  proof (λx, sub (lift σ) t ꞉ [ π x: sub σ S ]→ sub (lift σ) T) ` sub σ s
    〉 _▷_ 〉 (sub (lift σ') t' ꞉ sub (lift σ') T') [ sub σ' s' ꞉ sub σ' S' /new]
      :by: lam-comp π
             (liftSub-to-▷ (lift σ) (lift σ') t▷t' (liftSubVec σ σ' 𝒆▷𝒆'))
             (liftSub-to-▷ σ σ' t▷t'' 𝒆▷𝒆')
             (liftSub-to-▷ (lift σ) (lift σ') t▷t''' (liftSubVec σ σ' 𝒆▷𝒆'))
             (liftSub-to-▷ σ σ' t▷t'''' 𝒆▷𝒆')
    〉 _==_ 〉 (sub (lift σ') (t' ꞉ T')) [ sub σ' (s' ꞉ S') /new]
      :by: Id.refl _
    〉 _==_ 〉 sub σ' ((t' ꞉ T') [ s' ꞉ S' /new])
      :by: {!!}
    〉 _==_ 〉 sub σ' (t' [ s' ꞉ S' /new]) ꞉ sub σ' (T' [ s' ꞉ S' /new])
      :by: Id.refl _
  qed
  
  -- goal : (λx,
--       sub (lift σ) t ꞉ [ π x: sub σ S ]→ sub (lift σ) T) ` sub σ s
--       ▷
--       sub σ' (t' [ s' ꞉ S' /new]) ꞉ sub σ' (T' [ s' ꞉ S' /new])

-- (λx, t ꞉ [ π x: S ]→ T) ` s ▷ (t' ꞉ T') [ (s' ꞉ S') /new]
