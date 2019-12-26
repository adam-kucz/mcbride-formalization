{-# OPTIONS --exact-split --prop --safe #-}
open import TypeTheory.Basic using (Rig; wfs)
open import Foundation.PropUniverses

module TypeTheory.ParallelReduction
  {𝑅 : 𝒰 ˙} ⦃ r : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

-- Definition 12 (parallel reduction)

open import TypeTheory.Syntax using (Term; Elim; ExprTag; expr-of-type)
open Term; open Elim; open ExprTag
open import TypeTheory.Substitution as Subs using (_[_/new])
import TypeTheory.Computation as Comp

infix 36 _▷_
data _▷_ {n} : ∀ {tag} (s t : expr-of-type tag n) → 𝒰 ⁺ ⊔ 𝒱 ᵖ where
  sort : ∀ i
    → ---------------
    ⋆ {n = n} i ▷ ⋆ i

  pi : ∀ π {S S'} {T T'}
    (S▷S' : S ▷ S')
    (T▷T' : T ▷ T')
    → -----------------------------
    [ π x: S ]→ T ▷ [ π x: S' ]→ T'

  lam : ∀ {t t'}
    (t▷t' : t ▷ t')
    → --------------
    λx, t ▷ λx, t'

  elim : ∀ {e e'}
    (e▷e' : e ▷ e')
    → ---------------
    ⌊ e ⌋ ▷ ⌊ e' ⌋

  elim-comp : ∀ {t t'} {T T'}
    (t▷t' : t ▷ t')
    (T▷T' : T ▷ T')
    → ---------------
    ⌊ t ꞉ T ⌋ ▷ t'

  var : ∀ v
    → ------------
    var v ▷ var v

  app : ∀ {f f'} {s s'}
    (f▷f' : f ▷ f')
    (s▷s' : s ▷ s')
    → ---------------
    f ` s ▷ f' ` s'

  annot : ∀ {t t'} {T T'}
    (t▷t' : t ▷ t')
    (T▷T' : T ▷ T')
    → ---------------
    t ꞉ T ▷ t' ꞉ T'

  lam-comp : ∀ π {t t'} {S S'} {T T'} {s s'}
    (t▷t' : t ▷ t')
    (S▷S' : S ▷ S')
    (T▷T' : T ▷ T')
    (s▷s' : s ▷ s')
    → ---------------
    (λx, t ꞉ [ π x: S ]→ T) ` s ▷ (t' ꞉ T') [ (s' ꞉ S') /new]

-- Lemma 13 (parallel reduction computes)

open import Foundation.Relation.Binary.Property
  using (Reflexive; refl; _⊆_; subrel)
import Foundation.Relation.Binary.ReflexiveTransitiveClosure

instance
  Reflexive▷ : ∀ {n} {tag} → Reflexive (_▷_ {n} {tag})
  refl ⦃ Reflexive▷ {n} {term} ⦄ (⋆ i) = sort i
  refl ⦃ Reflexive▷ {n} {term} ⦄ ([ ρ x: S ]→ T) = pi ρ (refl S) (refl T)
  refl ⦃ Reflexive▷ {n} {term} ⦄ (λx, t) = lam (refl t)
  refl ⦃ Reflexive▷ {n} {term} ⦄ ⌊ e ⌋ = elim (refl e)
  refl ⦃ Reflexive▷ {n} {elim} ⦄ (var v) = var v
  refl ⦃ Reflexive▷ {n} {elim} ⦄ (f ` s) = app (refl f) (refl s)
  refl ⦃ Reflexive▷ {n} {elim} ⦄ (s ꞉ S) = annot (refl s) (refl S)

open import Foundation.Function.Proof
open Comp using (1-hole-ctx; _[_/—]; ContextClosed; ctx-closed)
open 1-hole-ctx

private
  ▷cc : ∀ {m n} {tag tag'}
    {e e' : expr-of-type tag m}
    (e▷e' : e ▷ e')
    (C : 1-hole-ctx tag m tag' n)
    → ----------------------------
    C [ e /—] ▷ C [ e' /—]
  ▷cc e▷e' — = e▷e'
  ▷cc e▷e' [ ρ x: S ]→ C ↓ = pi ρ (refl S) (▷cc e▷e' C)
  ▷cc e▷e' ([ ρ x: C ↓]→ T) = pi ρ (▷cc e▷e' C) (refl T)
  ▷cc e▷e' (λx, C) = lam (▷cc e▷e' C)
  ▷cc e▷e' ⌊ C ⌋ = elim (▷cc e▷e' C)
  ▷cc e▷e' (f ` C ↓) = app (refl f) (▷cc e▷e' C)
  ▷cc e▷e' (C ↓` s) = app (▷cc e▷e' C) (refl s)
  ▷cc e▷e' (s ꞉ C ↓) = annot (refl s) (▷cc e▷e' C)
  ▷cc e▷e' (C ↓꞉ S) = annot (▷cc e▷e' C) (refl S)

instance
  ContextClosed▷ : ContextClosed _▷_
  rel-preserv ⦃ ContextClosed▷ {C = C} ⦄ e▷e' = ▷cc e▷e' C

open Comp using (_⇝_; _↠_)
open _⇝_

⇝-⊆-▷ : ∀ {n} {tag} →
  (_⇝_ {n = n} {tag = tag}) ⊆ (_▷_ {n = n} {tag = tag})
subrel ⦃ ⇝-⊆-▷ ⦄ (β-exact (Comp.β π s S t T)) =
  lam-comp π (refl t) (refl S) (refl T) (refl s)
subrel ⦃ ⇝-⊆-▷ ⦄ (v-exact (Comp.v t T)) = elim-comp (refl t) (refl T)
subrel ⦃ ⇝-⊆-▷ ⦄ (hole C[—] x⇝y) = ctx-closed (subrel ⦃ ⇝-⊆-▷ ⦄ x⇝y) C[—]

open import Foundation.Proof
open import TypeTheory.Computation.Proof

▷-⊆-↠ : ∀ {n} {tag} →
  (_▷_ {n = n} {tag = tag}) ⊆ (_↠_ {n = n} {tag = tag})
subrel ⦃ ▷-⊆-↠ ⦄ (sort i) = refl (⋆ i)
subrel ⦃ ▷-⊆-↠ ⦄ (pi π {S} {S'} {T} {T'} S▷S' T▷T') = 
  proof [ π x: S ]→ T
    〉 _↠_ 〉 [ π x: S' ]→ T
      :by: ctx-closed (subrel ⦃ ▷-⊆-↠ ⦄ S▷S') ([ π x: — ↓]→ T)
    〉 _↠_ 〉 [ π x: S' ]→ T'
      :by: ctx-closed (subrel ⦃ ▷-⊆-↠ ⦄ T▷T') ([ π x: S' ]→ — ↓)
  qed
subrel ⦃ ▷-⊆-↠ ⦄ (lam t▷t') = ctx-closed (subrel ⦃ ▷-⊆-↠ ⦄ t▷t') (λx, —)
subrel ⦃ ▷-⊆-↠ ⦄ (elim e▷e') = ctx-closed (subrel ⦃ ▷-⊆-↠ ⦄ e▷e') (⌊ — ⌋)
subrel ⦃ ▷-⊆-↠ ⦄ (elim-comp {t} {t'} {T} {T'} t▷t' T▷T') =
  proof ⌊ t ꞉ T ⌋
    〉 _⇝_ 〉 t  :by: v-exact (Comp.v t T)
    〉 _↠_ 〉 t' :by: subrel ⦃ ▷-⊆-↠ ⦄ t▷t'
  qed
subrel ⦃ ▷-⊆-↠ ⦄ (var v) = refl (var v)
subrel ⦃ ▷-⊆-↠ ⦄ (app {f} {f'} {s} {s'} f▷f' s▷s') =
  proof f ` s
    〉 _↠_ 〉 f' ` s  :by: ctx-closed (subrel ⦃ ▷-⊆-↠ ⦄ f▷f') (— ↓` s)
    〉 _↠_ 〉 f' ` s' :by: ctx-closed (subrel ⦃ ▷-⊆-↠ ⦄ s▷s') (f' ` — ↓)
  qed
subrel ⦃ ▷-⊆-↠ ⦄ (annot {t} {t'} {T} {T'} t▷t' T▷T') =
  proof t ꞉ T
    〉 _↠_ 〉 t' ꞉ T  :by: ctx-closed (subrel ⦃ ▷-⊆-↠ ⦄ t▷t') (— ↓꞉ T)
    〉 _↠_ 〉 t' ꞉ T' :by: ctx-closed (subrel ⦃ ▷-⊆-↠ ⦄ T▷T') (t' ꞉ — ↓)
  qed
subrel ⦃ ▷-⊆-↠ ⦄ (lam-comp π {t} {t'} {S} {S'} {T} {T'} {s} {s'} t▷t' S▷S' T▷T' s▷s') =
  proof (λx, t ꞉ [ π x: S ]→ T) ` s
    〉 _↠_ 〉 (λx, t' ꞉ [ π x: S ]→ T) ` s
      :by: ctx-closed (subrel ⦃ ▷-⊆-↠ ⦄ t▷t') ((λx, — ↓꞉ [ π x: S ]→ T) ↓` s)
    〉 _↠_ 〉 (λx, t' ꞉ [ π x: S ]→ T') ` s
      :by: ctx-closed (subrel ⦃ ▷-⊆-↠ ⦄ T▷T') ((λx, t' ꞉ [ π x: S ]→ — ↓ ↓) ↓` s)
    〉 _↠_ 〉 (λx, t' ꞉ [ π x: S' ]→ T') ` s
      :by: ctx-closed (subrel ⦃ ▷-⊆-↠ ⦄ S▷S') ((λx, t' ꞉ [ π x: — ↓]→ T' ↓) ↓` s)
    〉 _↠_ 〉 (λx, t' ꞉ [ π x: S' ]→ T') ` s'
      :by: ctx-closed (subrel ⦃ ▷-⊆-↠ ⦄ s▷s') ((λx, t' ꞉ [ π x: S' ]→ T') ` — ↓)
    〉 _⇝_ 〉 (t' ꞉ T') [ s' ꞉ S' /new]
      :by: β-exact (Comp.β π s' S' t' T')
  qed

