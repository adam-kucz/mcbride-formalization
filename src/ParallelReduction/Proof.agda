{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import Basic using (Rig; wfs)
open import PropUniverses

module ParallelReduction.Proof
  {𝑅 : 𝒰 ˙} ⦃ r : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Syntax using (Term; Elim; ExprTag; expr-of-type)
open Term; open Elim; open ExprTag
open import ParallelReduction
open import Substitution ⦃ r ⦄ ⦃ 𝑤𝑓𝑠 ⦄
  using (_[_/new]; rename-[-/new])

open import Proposition.Identity as Id using (_==_)
open Id.Id renaming (sym to Id-sym)
open import Proof
open import Function.Proof

open import Renaming
open import Liftable

instance
  Composable-==-▷ : ∀ {n} {tag}
    → Composable (𝒰 ⁺ ⊔ 𝒱) _==_ (_▷_ {n = n} {tag})
  Composable-==-▷ = composable-==-R _▷_

  Composable-▷-== : ∀ {n} {tag}
    → Composable (𝒰 ⁺ ⊔ 𝒱) (_▷_ {n = n} {tag}) _==_
  Composable-▷-== = composable-R-== _▷_
  
  Relating-rename-▷ : ∀ {m n} {tag}
    {ρ : Ren m n}
    → ---------------------------
    Relating (rename ρ) (_▷_ {n = m} {tag}) (_▷_ {n = n} {tag})
  rel-preserv ⦃ Relating-rename-▷ {ρ = ρ} ⦄ (sort i) = refl (⋆ i)
  rel-preserv ⦃ Relating-rename-▷ {ρ = ρ} ⦄ (pi π S▷S' T▷T') =
    pi π (rel-preserv S▷S') (rel-preserv T▷T')
  rel-preserv ⦃ Relating-rename-▷ {ρ = ρ} ⦄ (lam t▷t') =
    lam (rel-preserv t▷t')
  rel-preserv ⦃ Relating-rename-▷ {ρ = ρ} ⦄ (elim e▷e') =
    elim (rel-preserv e▷e')
  rel-preserv ⦃ Relating-rename-▷ {ρ = ρ} ⦄ (elim-comp t▷t' T▷T') =
    elim-comp (rel-preserv t▷t') (rel-preserv T▷T')
  rel-preserv ⦃ Relating-rename-▷ {ρ = ρ} ⦄ (var v) =
    var (ρ v)
  rel-preserv ⦃ Relating-rename-▷ {ρ = ρ} ⦄ (app f▷f' s▷s') =
    app (rel-preserv f▷f') (rel-preserv s▷s')
  rel-preserv ⦃ Relating-rename-▷ {ρ = ρ} ⦄ (annot t▷t' T▷T') =
    annot (rel-preserv t▷t') (rel-preserv T▷T')
  rel-preserv ⦃ Relating-rename-▷ {ρ = ρ} ⦄
    (lam-comp π {t}{t'}{S}{S'}{T}{T'}{s}{s'} t▷t' S▷S' T▷T' s▷s') =
    proof (λx, rename (lift ρ) t ꞉ [ π x: rename ρ S ]→ rename (lift ρ) T) `
          rename ρ s
      〉 _▷_ 〉 (rename (lift ρ) (t' ꞉ T')) [ rename ρ (s' ꞉ S') /new]
        :by: lam-comp π (rel-preserv t▷t') (rel-preserv S▷S')
                        (rel-preserv T▷T') (rel-preserv s▷s')
      〉 _==_ 〉 rename ρ ((t' ꞉ T') [ s' ꞉ S' /new])
        :by: Id-sym $ rename-[-/new] ρ (t' ꞉ T') (s' ꞉ S')
    qed
