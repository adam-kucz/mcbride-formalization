{-# OPTIONS --exact-split --prop #-}
open import Basic
open import PropUniverses

module Subtyping.Definition
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

-- Definition 17 (subtyping)

open import Data.Nat hiding (_⊔_)
open import Syntax.Definition
open import Computation

infix 36 _~_
data _~_ : RelOnExpr (𝒰 ⁺ ⊔ 𝒱) where
  ~sort : ∀ i
    → ---------------
    ⋆ {n = n} i ~ ⋆ i

  ~var : ∀ (v : Var m)
    → ------------
    var v ~ var v

  ~pi : ∀ π {S S' : Term m}{T T'}
    (S~S' : S ~ S')
    (T~T' : T ~ T')
    → -----------------------------
    [ π x: S ]→ T ~ [ π x: S' ]→ T'

  ~lam : ∀ {t t' : Term (m +1)}
    (t~t' : t ~ t')
    → --------------
    _~_ {tag = term} (λx, t) (λx, t')

  ~elim : ∀ {e e' : Elim m}
    (e~e' : e ~ e')
    → ---------------
    _~_ {tag = term} (⌊ e ⌋) (⌊ e' ⌋)

  ~app : ∀ {f f'}{s s' : Term m}
    (f~f' : f ~ f')
    (s~s' : s ~ s')
    → ---------------
    f ` s ~ f' ` s'

  ~annot : ∀ {s s'}(S S' : Term m)
    (p : s ~ s')
    → -------------
    s ꞉ S ~ s' ꞉ S'

open import Relation.Binary hiding (_~_)

instance
  Reflexive~ : Reflexive (_~_ {n = n}{tag})
  Transitive~ : Transitive (_~_ {n = n}{tag})
  Symmetric~ : Symmetric (_~_ {n = n}{tag})

refl ⦃ Reflexive~ {tag = term} ⦄ (⋆ i) = ~sort i
refl ⦃ Reflexive~ {tag = term} ⦄ ([ ρ x: S ]→ T) = ~pi ρ (refl S) (refl T)
refl ⦃ Reflexive~ {tag = term} ⦄ (λx, t) = ~lam (refl t)
refl ⦃ Reflexive~ {tag = term} ⦄ ⌊ e ⌋ = ~elim (refl e)
refl ⦃ Reflexive~ {tag = elim} ⦄ (var v₁) = ~var v₁
refl ⦃ Reflexive~ {tag = elim} ⦄ (f ` s) = ~app (refl f) (refl s)
refl ⦃ Reflexive~ {tag = elim} ⦄ (s ꞉ S) = ~annot S S (refl s)

trans ⦃ Transitive~ ⦄ (~sort i) q = q
trans ⦃ Transitive~ ⦄ (~var v') q = q
trans ⦃ Transitive~ ⦄ (~pi π p p₁) (~pi π q q₁) = ~pi π (trans p q) (trans p₁ q₁)
trans ⦃ Transitive~ ⦄ (~lam p) (~lam q) = ~lam (trans p q)
trans ⦃ Transitive~ ⦄ (~elim p) (~elim q) = ~elim (trans p q)
trans ⦃ Transitive~ ⦄ (~app p p₁) (~app q q₁) = ~app (trans p q) (trans p₁ q₁)
trans ⦃ Transitive~ ⦄ (~annot S S' p) (~annot S″ S‴ q) = ~annot S S‴ (trans p q)

sym ⦃ Symmetric~ ⦄ (~sort i) = ~sort i
sym ⦃ Symmetric~ ⦄ (~var v₁) = ~var v₁
sym ⦃ Symmetric~ ⦄ (~pi π p p₁) = ~pi π (sym p) (sym p₁)
sym ⦃ Symmetric~ ⦄ (~lam p) = ~lam (sym p)
sym ⦃ Symmetric~ ⦄ (~elim p) = ~elim (sym p)
sym ⦃ Symmetric~ ⦄ (~app p p₁) = ~app (sym p) (sym p₁)
sym ⦃ Symmetric~ ⦄ (~annot S S' p) = ~annot S' S (sym p)

data _≼_ : RelOnExpr (𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲) where
  ≼similar : {S T : expr-of-type tag m}
    (p : S ~ T)
    → ----------
    S ≼ T

  ≼sort : ∀ {i j}
    (p : j ≻ i)
    → ------------
    ⋆ {n = n} i ≼ ⋆ j

  ≼pi : ∀ π {S S' : Term m}{T T'}
    (p : S' ≼ S)
    (q : T ≼ T')
    → ---------------------
    [ π x: S ]→ T ≼ [ π x: S' ]→ T'

-- Lemma 18 (subtyping transitivity)

instance
  Reflexive≼ : Reflexive (_≼_ {n = n}{tag})
  Transitive≼ : Transitive (_≼_ {n = n}{tag})

refl ⦃ Reflexive≼ ⦄ t = ≼similar (refl t)

trans ⦃ Transitive≼ ⦄ (≼similar p) (≼similar p₁) =
  ≼similar (trans p p₁)
trans ⦃ Transitive≼ ⦄ (≼similar (~sort i)) q@(≼sort _) = q
trans ⦃ Transitive≼ ⦄ (≼similar (~pi π p p₁)) (≼pi π q q₁) =
  ≼pi π (trans q (≼similar (sym p))) (trans (≼similar p₁) q₁)
trans ⦃ Transitive≼ ⦄ p@(≼sort _) (≼similar (~sort i)) = p
trans ⦃ Transitive≼ ⦄ (≼sort p) (≼sort p₁) = ≼sort (trans p₁ p)
trans ⦃ Transitive≼ ⦄ (≼pi π p p₁) (≼similar (~pi π q q₁)) =
  ≼pi π (trans (≼similar (sym q)) p) (trans p₁ (≼similar q₁))
trans ⦃ Transitive≼ ⦄ (≼pi π p p₁) (≼pi π q q₁) =
  ≼pi π (trans q p) (trans p₁ q₁)
