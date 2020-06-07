{-# OPTIONS --exact-split --prop #-}
open import Basic
open import PropUniverses

module Subtyping.Contradiction where

module Generic
    {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
    {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
    where
  open import Data.Nat hiding (_⊔_)
  open import Syntax

  -- Definition 17 (subtyping) [similarity]

  infix 36 _~_
  data _~_ {n} : ∀ {tag} (s t : expr-of-type tag n) → 𝒰 ⁺ ⊔ 𝒱 ᵖ where
    ~annot : ∀{s s'}(S S' : Term n)
      (p : s ~ s')
      → -------------
      s ꞉ S ~ s' ꞉ S'
  
    ⋆ : ∀ i → ⋆ i ~ ⋆ i
  
    var : ∀ v → var v ~ var v
  
    [_x:_]→_ : ∀ π {S S' T T'}
      (S▷S' : S ~ S')
      (T▷T' : T ~ T')
      → ---------------
      [ π x: S ]→ T ~ [ π x: S' ]→ T'
  
    λx,_ : ∀{t t'}
      (t▷t' : t ~ t')
      → ------------------------------------
      λx, t ~ λx, t'
  
    _`_ : ∀{f f' s s'}
      (f▷f' : f ~ f')
      (s▷s' : s ~ s')
      → ------------------------------------
      f ` s ~ f' ` s'
  
    ⌊_⌋ : ∀{e e'}
      (e▷e' : e ~ e')
      → --------------------
      ⌊ e ⌋ ~ ⌊ e' ⌋
  
  
  open import Syntax.Context
  
  open import Relation.Binary
    hiding (_~_; Reflexive~; Transitive~; Symmetric~)
  
  instance
    Reflexive~ : Reflexive (_~_ {n = n}{tag})
    Transitive~ : Transitive (_~_ {n = n}{tag})
    Symmetric~ : Symmetric (_~_ {n = n}{tag})
    ContextClosed~ : ContextClosed _~_
  
  open import Proof
  
  refl ⦃ Reflexive~ {tag = term} ⦄ (⋆ i) = ⋆ i
  refl ⦃ Reflexive~ {tag = term} ⦄ ([ π x: S ]→ T) =
    [ π x: refl S ]→ refl T
  refl ⦃ Reflexive~ {tag = term} ⦄ (λx, t) = λx, refl t
  refl ⦃ Reflexive~ {tag = term} ⦄ ⌊ e ⌋ = ⌊ refl e ⌋
  refl ⦃ Reflexive~ {tag = elim} ⦄ (var x) = var x
  refl ⦃ Reflexive~ {tag = elim} ⦄ (f ` s) = refl f ` refl s
  refl ⦃ Reflexive~ {tag = elim} ⦄ (s ꞉ S) = ~annot S S $ refl s
  
  trans ⦃ Transitive~ ⦄ (~annot S _ p)(~annot _ S″ q) =
    ~annot S S″ $ trans p q
  trans ⦃ Transitive~ ⦄ (⋆ _) q = q
  trans ⦃ Transitive~ ⦄ (var _) q = q
  trans ⦃ Transitive~ ⦄ ([ π x: p₀ ]→ p₁)([ π x: q₀ ]→ q₁) =
    [ π x: trans p₀ q₀ ]→ trans p₁ q₁
  trans ⦃ Transitive~ ⦄ (λx, p)(λx, q) = λx, trans p q
  trans ⦃ Transitive~ ⦄ (p₀ ` p₁)(q₀ ` q₁) = trans p₀ q₀ ` trans p₁ q₁
  trans ⦃ Transitive~ ⦄ ⌊ p ⌋ ⌊ q ⌋ = ⌊ trans p q ⌋
  
  sym ⦃ Symmetric~ ⦄ (~annot S S' p) = ~annot S' S $ sym p
  sym ⦃ Symmetric~ ⦄ (⋆ i) = ⋆ i
  sym ⦃ Symmetric~ ⦄ (var x) = var x
  sym ⦃ Symmetric~ ⦄ ([ π x: p₀ ]→ p₁) = [ π x: sym p₀ ]→ sym p₁
  sym ⦃ Symmetric~ ⦄ (λx, p) = λx, sym p
  sym ⦃ Symmetric~ ⦄ (p₀ ` p₁) = sym p₀ ` sym p₁
  sym ⦃ Symmetric~ ⦄ ⌊ p ⌋ = ⌊ sym p ⌋
  
  open import Logic
  
  ctx-closed ⦃ ContextClosed~ ⦄ (term t) _ = refl t
  ctx-closed ⦃ ContextClosed~ ⦄ (elim e) _ = refl e
  ctx-closed ⦃ ContextClosed~ ⦄ — p = p
  ctx-closed ⦃ ContextClosed~ ⦄ ([ π x: C₀ ]→ C₁)(p₀ , p₁) =
    [ π x: ctx-closed C₀ p₀ ]→ ctx-closed C₁ p₁
  ctx-closed ⦃ ContextClosed~ ⦄ (λx, C) p = λx, ctx-closed C p
  ctx-closed ⦃ ContextClosed~ ⦄ ⌊ C ⌋ p = ⌊ ctx-closed C p ⌋
  ctx-closed ⦃ ContextClosed~ ⦄ (C₀ ` C₁)(p₀ , p₁) =
    ctx-closed C₀ p₀ ` ctx-closed C₁ p₁
  ctx-closed ⦃ ContextClosed~ ⦄ (C₀ ꞉ C₁)(p₀ , p₁) =
    ~annot _ _ $ ctx-closed C₀ p₀

-- Inadmissibility of Lemma 19 (similairty preservation)

  open import ParallelReduction

  postulate
    step-▷-preserves-~ : {S S' T : expr-of-type tag m}
      (p : S ~ T)
      (q : S ▷ S')
      → -------------------------
      ∃ λ T' → S' ~ T' ∧ T ▷ T'

open import Basic.Instance
open import Data.Nat
open import Data.FinNat

instance
  _ = HemiringFinℕ+*
WFS = WellFoundedSortsℕ

open Generic {R = None-one-tons} ⦃ wfs = WFS ⦄
open import Syntax {R = None-one-tons} ⦃ wfs = WFS ⦄
open import ParallelReduction {R = None-one-tons} ⦃ wfs = WFS ⦄

S S' T : Elim 0
S = (λx, ⌊ var new ⌋ ꞉ [ 0 x: ⋆ 0 ]→ ⋆ 0) ` ⋆ 0
S' = ⌊ ⋆ 0 ꞉ ⋆ 0 ⌋ ꞉ ⋆ 0
T = (λx, ⌊ var new ⌋ ꞉ ⋆ 0) ` ⋆ 0

bad-~ : S ~ T
bad-~ = ~annot ([ 0 x: ⋆ 0 ]→ ⋆ 0) (⋆ 0) (λx, ⌊ var new ⌋) ` ⋆ 0

bad-▷ : S ▷ S'
bad-▷ = lam-comp 0 ⌊ var new ⌋ (⋆ 0) (⋆ 0) (⋆ 0)

open import Logic

bad-preservation : ∃ λ T' → S' ~ T' ∧ T ▷ T'
bad-preservation = step-▷-preserves-~ bad-~ bad-▷

contradiction : ⊥
contradiction with bad-preservation
contradiction |
  ⌊ ⋆ zero ꞉ S ⌋ ꞉ T ,
  (~annot (⋆ 0) T ⌊ ~annot (⋆ 0) S (⋆ 0) ⌋ ,
   ())
