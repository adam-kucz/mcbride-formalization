{-# OPTIONS --exact-split --safe --prop  #-}
module TypeTheory.Computation where

open import TypeTheory.Basic using (Rig; wfs)
open import TypeTheory.Syntax

open import Foundation.PropUniverses

-- Definition 5 (contraction, reduction, computation)

infix 4 _[_/new]
_[_/new] :
  ⦃ _ : Rig X ⦄
  ⦃ _ : wfs 𝒰 𝒱 Y ⦄
  {e' : Expr}
  → -----------------
  (e : Expr-2-Set e') (f : Elim) → Expr-2-Set e'
e [ f /new] = e

infix 2 _⇝β_ _⇝v_
data _⇝β_ ⦃ _ : Rig X ⦄ ⦃ _ : wfs 𝒰 𝒱 Y ⦄ : (e e' : Elim) → 𝒰₀ ᵖ where
  β : ∀ {π} {s t S T}
    → ----------------------------------------------------
    (λx, t ꞉ ([ π x: S ]→ T)) ` s ⇝β (t ꞉ T) [ s ꞉ S /new]

data _⇝v_ ⦃ _ : Rig X ⦄ ⦃ _ : wfs 𝒰 𝒱 Y ⦄ : (t T : Term) → 𝒰₀ ᵖ where
  v : ∀ {t T}
    → --------------
    ⌊ t ꞉ T ⌋ ⇝v t

data 1-hole-ctx
  {R : 𝒰 ˙}
  ⦃ _ : Rig R ⦄
  {S : 𝒱 ˙}
  ⦃ _ : wfs 𝒲 𝒯 S ⦄
  : ------------------------
  (e e' : Expr) → 𝒰 ⁺ ⊔ 𝒱 ˙
  where
  — : ∀ {e}
    → ------------
    1-hole-ctx e e
  
  [_x:_]→_↓ : ∀ {e}
    (r : R)
    (S : Term)
    (C[—] : 1-hole-ctx e term)
    → ---------------------
    1-hole-ctx e term

  [_x:_↓]→_ : ∀ {e}
    (r : R)
    (C[—] : 1-hole-ctx e term)
    (T : Term)
    → ----------------------
    1-hole-ctx e term

  λx,_ : ∀ {e}
    (C[—] : 1-hole-ctx e term)
    → ----------------------
    1-hole-ctx e term

  ⌊_⌋ : ∀ {e}
    (C[—] : 1-hole-ctx e elim)
    → ---------------------
    1-hole-ctx e term

  _`_↓ : ∀ {e}
    (f : Elim)
    (C[—] : 1-hole-ctx e term)
    → ----------------------
    1-hole-ctx e elim

  _↓`_ : ∀ {e}
    (C[—] : 1-hole-ctx e elim)
    (s : Term)
    → ---------------------
    1-hole-ctx e elim

  _∶_↓ : ∀ {e}
    (s : Term)
    (C[—] : 1-hole-ctx e term)
    → ----------------------
    1-hole-ctx e elim

  _↓∶_ : ∀ {e}
    (C[—] : 1-hole-ctx e term)
    (S : Term)
    → ----------------------
    1-hole-ctx e elim


infix 35 _[_/—]
_[_/—] : {R : 𝒰 ˙} ⦃ _ : Rig R ⦄ {S : 𝒱 ˙} ⦃ _ : wfs 𝒲 𝒯 S ⦄
  {e₁ e₂ : Expr}
  (C[—] : 1-hole-ctx e₁ e₂)
  (e : Expr-2-Set e₁)
  → ----------------------
  Expr-2-Set e₂
— [ e /—] = e
[ π x: S ]→ C[—] ↓ [ e /—] = [ π x: S ]→ C[—] [ e /—]
([ π x: C[—] ↓]→ T) [ e /—] = [ π x: C[—] [ e /—] ]→ T
(λx, C[—]) [ e /—] = λx, C[—] [ e /—]
⌊ C[—] ⌋ [ e /—] = ⌊ C[—] [ e /—] ⌋
(f ` C[—] ↓) [ e /—] = f ` C[—] [ e /—]
(C[—] ↓` s) [ e /—] = C[—] [ e /—] ` s
(s ∶ C[—] ↓) [ e /—] = s ꞉ C[—] [ e /—]
(C[—] ↓∶ S) [ e /—] = C[—] [ e /—] ꞉ S

infix 1 _⇝_
data _⇝_ {R : 𝒰 ˙} ⦃ _ : Rig R ⦄ {S : 𝒱 ˙} ⦃ _ : wfs 𝒲 𝒯 S ⦄ :
     {e' : Expr} (s t : Expr-2-Set e') → 𝒰 ⁺ ⊔ 𝒱 ᵖ where
  β-exact : ∀ {s t}
    (β : s ⇝β t)
    → -------------
    s ⇝ t

  v-exact : ∀ {s t}
    (v : s ⇝v t)
    → -------------
    s ⇝ t

  hole : ∀ {e₁ e₂} {s t}
    (C[—] : 1-hole-ctx e₁ e₂)
    (reduct : s ⇝ t)
    → --------------------
    C[—] [ s /—] ⇝ C[—] [ t /—]

open import Foundation.Relation.Binary.ReflexiveTransitiveClosure
  using (refl-trans-close)

infix 1 _↠_
_↠_ : ∀ {R : 𝒰 ˙} ⦃ _ : Rig R ⦄ {S : 𝒱 ˙} ⦃ _ : wfs 𝒲 𝒯 S ⦄ {e}
  (e₁ : Expr-2-Set e)
  (e₂ : Expr-2-Set e)
  → --------------------
  𝒰 ⁺ ⊔ 𝒱 ᵖ
_↠_ = refl-trans-close _⇝_
