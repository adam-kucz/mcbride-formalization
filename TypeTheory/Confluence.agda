{-# OPTIONS --exact-split --prop  #-}
open import TypeTheory.Basic using (Rig; wfs)
open import Foundation.PropUniverses

module TypeTheory.Confluence
  {𝑅 : 𝒰 ˙} ⦃ r : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

-- Definition 10 (diamond property)

open import Foundation.Relation.Binary using (Rel)
open import Foundation.Relation.Binary.Property
open import Foundation.Relation.Binary.ReflexiveTransitiveClosure
open import Foundation.Logic using (∃; _∧_; _,_)

diamond : {X : 𝒵 ˙} (R : Rel 𝒴 X X) → 𝒵 ⊔ 𝒴 ᵖ
diamond _R_ = ∀ {s p q}
  (sRp : s R p)
  (sRq : s R q)
  → ------------
  ∃ λ r → p R r ∧ q R r

-- Lemma 11 (parallelogram)

diamond-2-rtc-diamond :
  {R : Rel 𝒴 X X}
  (diamond-R : diamond R)
  → ----------------------
  diamond (refl-trans-close R)
diamond-2-rtc-diamond {R = _R_} diamond-R = go
  where _R*_ = refl-trans-close _R_
        go : diamond _R*_
        go {s} {s} {q} (rfl s) sR*q = q , (sR*q , refl q)
        go {s} {p} {q} (step {s} {s'} {p} sRs' s'R*p) sR*q = hi
          where hi : ∃ λ r → p R* r ∧ q R* r
                q'step : ∀ {s s'}
                  (sRs' : s R s')
                  (sR*q : s R* q)
                  → -------------------------
                  ∃ λ q' → s' R* q' ∧ q R q'
                hi with q'step sRs' sR*q
                hi | q' , (s'R*q' , qRq') with go s'R*p s'R*q'
                hi | _ , (_ , qRq') | r , (pR*r , q'R*r) =
                  r , (pR*r , step qRq' q'R*r)
                q'step {s} {s'} sRs' (rfl s) = s' , (refl s' , sRs')
                q'step sRs' (step sRt tR*q) with diamond-R sRs' sRt
                q'step sRs' (step sRt tR*q) | t' , (s'Rt' , tRt') with q'step tRt' tR*q
                q'step sRs' (step sRt tR*q) | t' , (s'Rt' , tRt') | q' , (t'R*q' , qRq') =
                  q' , (step s'Rt' t'R*q' , qRq')

parallelogram :
  (R : Rel 𝒴 X X)
  {P : Rel 𝒵 X X} ⦃ R⊆P : R ⊆ P ⦄ ⦃ P⊂R* : P ⊆ refl-trans-close R ⦄
  (diamond-P : diamond P)
  → ----------------------
  diamond (refl-trans-close R)
parallelogram R {P} diamond-P = result
  where diamond-rtc-P : diamond (refl-trans-close P)
        result : diamond (refl-trans-close R)
        result sR*p sR*q with diamond-rtc-P (subrel sR*p) (subrel sR*q)
        result sR*p sR*q | q , (left , right) = q , (P*→R* left , P*→R* right)
          where P*→R* = subrel ⦃ subrel-rtc-to-rtc-subrel-rtc ⦄
        diamond-rtc-P = diamond-2-rtc-diamond diamond-P

-- Definition 12 (parallel reduction)

open import TypeTheory.Syntax
open import TypeTheory.Computation as Comp using (_[_/new])

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
    (λx, t ꞉ [ π x: S ]→ T) ` s ▷ (t' ꞉ T')[ s' ꞉ S' /new]

-- Lemma 13 (parallel reduction computes)

instance
  Reflexive▷ : ∀ {n} {tag} → Reflexive (_▷_ {n} {tag})
  refl ⦃ Reflexive▷ {n} {term} ⦄ (⋆ i) = sort i
  refl ⦃ Reflexive▷ {n} {term} ⦄ ([ ρ x: S ]→ T) = pi ρ (refl S) (refl T)
  refl ⦃ Reflexive▷ {n} {term} ⦄ (λx, t) = lam (refl t)
  refl ⦃ Reflexive▷ {n} {term} ⦄ ⌊ e ⌋ = elim (refl e)
  refl ⦃ Reflexive▷ {n} {elim} ⦄ (var v) = var v
  refl ⦃ Reflexive▷ {n} {elim} ⦄ (f ` s) = app (refl f) (refl s)
  refl ⦃ Reflexive▷ {n} {elim} ⦄ (s ꞉ S) = annot (refl s) (refl S)

open import Foundation.Data.Nat using (suc; _+_; +-suc)
open Comp using (1-hole-ctx; _[_/—])
open 1-hole-ctx
open import Foundation.Prop'.Identity.Transport
open import Foundation.Prop'.Identity using (ap)
open import Foundation.Prop'.Function using (_$_)

private
  prcc : ∀ {m n} {tag tag'}
    {e e' : expr-of-type tag (m + n)}
    (e▷e' : e ▷ e')
    (C : 1-hole-ctx tag m tag' n)
    → ----------------------------
    C [ e /—] ▷ C [ e' /—]
  prcc e▷e' — = e▷e'
  prcc {suc m} {n} {tag} {tag'} {e} {e'} e▷e' [ ρ x: S ]→ C ↓ = 
    pi ρ (refl S) (prcc ? C)
  prcc e▷e' ([ ρ x: C ↓]→ T) = pi ρ (prcc e▷e' C) (refl T)
  prcc e▷e' (λx, C) = lam (prcc {!!} C)
  prcc e▷e' ⌊ C ⌋ = elim (prcc e▷e' C)
  prcc e▷e' (f ` C ↓) = app (refl f) (prcc e▷e' C)
  prcc e▷e' (C ↓` s) = app (prcc e▷e' C) (refl s)
  prcc e▷e' (s ∶ C ↓) = annot (refl s) (prcc e▷e' C)
  prcc e▷e' (C ↓∶ S) = annot (prcc e▷e' C) (refl S)

parellel-reduction-ctx-closed : ∀ {m n} {tag tag'}
  {e e' : expr-of-type tag (n + m)}
  (e▷e' : e ▷ e')
  (C : 1-hole-ctx tag n tag' m)
  → ----------------------------
  C [ e /—] ▷ C [ e' /—]
parellel-reduction-ctx-closed = prcc

open Comp using (_⇝_)
open _⇝_

computation-⊆-parallel-reduction : ∀ {n} {tag} →
  (_⇝_ {n = n} {tag = tag}) ⊆ (_▷_ {n = n} {tag = tag})
subrel ⦃ computation-⊆-parallel-reduction {n} {tag} ⦄ = go
  where go : {x y : expr-of-type tag n} (x⇝y : x ⇝ y) → x ▷ y
        go (β-exact (Comp.β π s S t T)) =
          lam-comp π (refl t) (refl S) (refl T) (refl s)
        go (v-exact (Comp.v t T)) = elim-comp (refl t) (refl T)
        go (hole Comp.— x⇝y) = go x⇝y
        go (hole Comp.[ ρ x: S ]→ C[—] ↓ x⇝y) = {!!}
        go (hole (Comp.[ ρ x: C[—] ↓]→ T) x⇝y) =
          pi ρ {!!} (refl T)
        go (hole (Comp.λx, C[—]) x⇝y) = {!!}
        go (hole Comp.⌊ C[—] ⌋ x⇝y) = {!!}
        go (hole (f Comp.` C[—] ↓) x⇝y) = {!!}
        go (hole (C[—] Comp.↓` s) x⇝y) = {!!}
        go (hole (s Comp.∶ C[—] ↓) x⇝y) = {!!}
        go (hole (C[—] Comp.↓∶ S) x⇝y) = {!!}
