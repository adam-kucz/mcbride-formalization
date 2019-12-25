{-# OPTIONS --exact-split --prop --safe #-}
open import Foundation.PropUniverses
open import TypeTheory.Basic using (Rig; wfs)

module TypeTheory.Computation
  {𝑅 : 𝒰 ˙} ⦃ r : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import TypeTheory.Syntax
open import TypeTheory.Substitution using (_[_/new])

open import Foundation.Prop'.Identity hiding (refl)
open import Foundation.Prop'.Function using (_$_)
open import Foundation.Relation.Binary
open import Foundation.Operation.Binary.Property
open import Foundation.Data.Nat using (ℕ; suc)

-- Definition 5 (contraction, reduction, computation)

infix 36 _⇝β_ _⇝v_
data _⇝β_ {n : ℕ} : (e e' : Elim n) → 𝒰₀ ᵖ where
  β : ∀ π s S t T
    → ----------------------------------------------------
    (λx, t ꞉ ([ π x: S ]→ T)) ` s ⇝β (t ꞉ T) [ s ꞉ S /new]

data _⇝v_ {n : ℕ} : (t T : Term n) → 𝒰₀ ᵖ
  where
  v : ∀ t T
    → --------------
    ⌊ t ꞉ T ⌋ ⇝v t

data 1-hole-ctx
  : --------------------------------------------------
  (hole : ExprTag) -- required type of hole
  (m : ℕ) -- number of free variables in hole
  (result : ExprTag) -- type resulting from filling hole
  (n : ℕ) -- number of free variables of the context (n ≤ m)
  → 𝒰 ⁺ ⊔ 𝒱 ˙
  where
  — : ∀ {n} {e}
    → ------------
    1-hole-ctx e n e n
  
  [_x:_]→_↓ : ∀ {e} {m n}
    (ρ : 𝑅)
    (S : Term n)
    (C[—] : 1-hole-ctx e m term (suc n))
    → ---------------------
    1-hole-ctx e m term n

  [_x:_↓]→_ : ∀ {e} {m n}
    (ρ : 𝑅)
    (C[—] : 1-hole-ctx e m term n)
    (T : Term (suc n))
    → ----------------------
    1-hole-ctx e m term n

  λx,_ : ∀ {e} {m n}
    (C[—] : 1-hole-ctx e m term (suc n))
    → ----------------------
    1-hole-ctx e m term n

  ⌊_⌋ : ∀ {e} {m n}
    (C[—] : 1-hole-ctx e m elim n)
    → ---------------------
    1-hole-ctx e m term n

  _`_↓ : ∀ {e} {m n}
    (f : Elim n)
    (C[—] : 1-hole-ctx e m term n)
    → ----------------------
    1-hole-ctx e m elim n

  _↓`_ : ∀ {e} {m n}
    (C[—] : 1-hole-ctx e m elim n)
    (s : Term n)
    → ---------------------
    1-hole-ctx e m elim n

  _꞉_↓ : ∀ {e} {m n}
    (s : Term n)
    (C[—] : 1-hole-ctx e m term n)
    →  ----------------------
    1-hole-ctx e m elim n

  _↓꞉_ : ∀ {e} {m n}
    (C[—] : 1-hole-ctx e m term n)
    (S : Term n)
    → ----------------------
    1-hole-ctx e m elim n

infix 180 _[_/—]
_[_/—] : {m n : ℕ}
  {tag₁ tag₂ : ExprTag}
  (C[—] : 1-hole-ctx tag₁ m tag₂ n)
  (e : expr-of-type tag₁ m)
  → ----------------------
  expr-of-type tag₂ n
— [ e /—] = e
_[_/—] ([ π x: S ]→ C[—] ↓) e = [ π x: S ]→ C[—] [ e /—]
([ π x: C[—] ↓]→ T) [ e /—] = [ π x: C[—] [ e /—] ]→ T
_[_/—] (λx, C[—]) e = λx, C[—] [ e /—]
⌊ C[—] ⌋ [ e /—] = ⌊ C[—] [ e /—] ⌋
(f ` C[—] ↓) [ e /—] = f ` C[—] [ e /—]
(C[—] ↓` s) [ e /—] = C[—] [ e /—] ` s
(s ꞉ C[—] ↓) [ e /—] = s ꞉ C[—] [ e /—]
(C[—] ↓꞉ S) [ e /—] = C[—] [ e /—] ꞉ S

RelOnExpr : (𝒲 : Universe) → 𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲 ⁺ ˙
RelOnExpr 𝒲 = ∀ {n} {tag} → Rel 𝒲 (expr-of-type tag n) (expr-of-type tag n)

open import Foundation.Function.Proof using (Relating; ap; rel-preserv)

ContextClosed : (R : RelOnExpr 𝒵) → 𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒵 ᵖ
ContextClosed R = ∀ {m n} {tag tag'}
  {C : 1-hole-ctx tag m tag' n}
  → ----------------------------
  Relating (C [_/—]) R R

ctx-closed : ∀ {_R_ : RelOnExpr 𝒵}
  ⦃ _ : ContextClosed _R_ ⦄
  {m n} {tag tag'}
  {e e' : expr-of-type tag m}
  (eRe' : e R e')
  (C : 1-hole-ctx tag m tag' n)
  → ----------------------------
  C [ e /—] R C [ e' /—]
ctx-closed eRe' C = ap (C [_/—]) eRe'

open import Foundation.Relation.Binary.ReflexiveTransitiveClosure

infix 36 _⇝_
data _⇝_ : RelOnExpr (𝒰 ⁺ ⊔ 𝒱)
  where
  β-exact : ∀ {n} {s t : Elim n}
    (β : s ⇝β t)
    → -------------
    s ⇝ t

  v-exact : ∀ {n} {s t : Term n}
    (v : s ⇝v t)
    → -------------
    s ⇝ t

  hole : ∀ {m n} {tag₁ tag₂} {s t}
    (C[—] : 1-hole-ctx tag₁ m tag₂ n)
    (reduct : s ⇝ t)
    → --------------------
    C[—] [ s /—] ⇝ C[—] [ t /—]

instance
  ContextClosed⇝ : ContextClosed _⇝_
  rel-preserv ⦃ ContextClosed⇝ {C = C} ⦄ s⇝t = hole C s⇝t

infix 36 _↠_
_↠_ : RelOnExpr (𝒰 ⁺ ⊔ 𝒱)
_↠_ = refl-trans-close _⇝_
  
