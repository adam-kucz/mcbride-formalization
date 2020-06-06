{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import Basic using (Rig; wfs)
open import PropUniverses

module ParallelReduction.Proof
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax
open import ParallelReduction
open import Substitution as Subs hiding (sub; _[_/new])

open import Proof
open import Function.Proof

open import Renaming
open import Liftable

private
  _[_/new] = Subs._[_/new] ⦃ subst = SubstitutableElim ⦄
  sub = λ {tag}{m}{n} →
    Subs.sub ⦃ subst = SubstitutableExpr {tag = tag} ⦄ {m}{n}
infix 180 _[_/new]

module comp-▷ {n} {tag}
  where open MakeComposable (_▷_ {n = n} {tag}) public

instance
  Relating-sub-▷ : ∀ {m n} {tag}
    {σ : Sub m n}
    → ---------------------------
    Relating (sub σ) (_▷_ {n = m} {tag}) (_▷_ {n = n} {tag})
  Relating-rename-▷ : ∀ {m n} {tag}
    {ρ : Ren m n}
    → ---------------------------
    Relating (rename ρ) (_▷_ {n = m} {tag}) (_▷_ {n = n} {tag})

open import Type.Sum hiding (_,_)
open import Logic

open import Syntax.Context

rel-preserv ⦃ Relating-sub-▷ {σ = σ} ⦄ (elim-comp T t▷t') =
  elim-comp (sub σ T) $ rel-preserv t▷t'
rel-preserv ⦃ Relating-sub-▷ {σ = σ} ⦄
  (lam-comp π {t}{t'}{S}{S'}{T}{T'}{s}{s'} t▷t' S▷S' T▷T' s▷s') =
  proof (λx, sub (lift σ) t ꞉ [ π x: sub σ S ]→ sub (lift σ) T) ` sub σ s
    〉 _▷_ 〉 sub (newSub (sub σ (s' ꞉ S'))) (sub (lift σ) (t' ꞉ T'))
      :by: lam-comp π (rel-preserv t▷t') (rel-preserv S▷S')
                      (rel-preserv T▷T') (rel-preserv s▷s')
    === sub (newSub (sub σ (s' ꞉ S')) ⍟ lift σ) (t' ꞉ T')
      :by: ap (λ — → — (t' ꞉ T')) $
           sub-∘ ⦃ subst = SubstitutableExpr ⦄
             (newSub (sub σ (s' ꞉ S'))) (lift σ) 
    === sub (σ ⍟ newSub (s' ꞉ S')) (t' ꞉ T')
      :by: ap (λ — → sub — (t' ꞉ T')) $ sym {R = _==_} $
           Subs.sub-newSub σ (s' ꞉ S')
    === sub σ (sub (newSub (s' ꞉ S')) (t' ꞉ T'))
      :by: ap (λ — → — (t' ꞉ T')) $ sym $ sub-∘ σ (newSub (s' ꞉ S')) 
  qed
rel-preserv ⦃ Relating-sub-▷ ⦄ (⋆ i) = ⋆ i
rel-preserv ⦃ Relating-sub-▷ {σ = σ} ⦄ (var v) = refl (σ v)
rel-preserv ⦃ Relating-sub-▷ ⦄ ([ π x: S▷S' ]→ T▷T') =
  [ π x: rel-preserv S▷S' ]→ rel-preserv T▷T'
rel-preserv ⦃ Relating-sub-▷ ⦄ (λx, t▷t') = λx, rel-preserv t▷t'
rel-preserv ⦃ Relating-sub-▷ ⦄ (f▷f' ` s▷s') =
  rel-preserv f▷f' ` rel-preserv s▷s'
rel-preserv ⦃ Relating-sub-▷ ⦄ (s▷s' ꞉ S▷S') =
  rel-preserv s▷s' ꞉ rel-preserv S▷S'
rel-preserv ⦃ Relating-sub-▷ ⦄ ⌊ e▷e' ⌋ = ⌊ rel-preserv e▷e' ⌋

open import Function hiding (_$_)

rel-preserv ⦃ Relating-rename-▷ {ρ = ρ} ⦄ {a}{b} a▷b =
  proof rename ρ a
    === sub (var ∘ ρ) a    :by: ap (λ — → — a) $ rename-as-sub ρ
    〉 _▷_ 〉 sub (var ∘ ρ) b :by: ap (sub (var ∘ ρ)) a▷b
    === rename ρ b         :by: ap (λ — → — b) $ sym $ rename-as-sub ρ
  qed
