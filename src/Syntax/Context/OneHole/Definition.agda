{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Syntax.Context.OneHole.Definition
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax

open import Type.Sum hiding (_,_)
open import Data.Nat hiding (_⊔_)

data OneHoleContext
  : ------------------------------------------------------------
  (hole : ExprTag) -- required type of hole
  (m : ℕ) -- number of free variables in hole
  (result : ExprTag) -- type resulting from filling hole
  (n : ℕ) -- number of free variables of the context (n ≤ m)
  → 𝒰 ⁺ ⊔ 𝒱 ˙
  where
  — : ∀{n tag} → OneHoleContext tag n tag n

  [_x:_]→_↓ : ∀ {m n tag}
    (π : R)
    (S : Term n)
    (C : OneHoleContext tag m term (n +1))
    → ---------------------
    OneHoleContext tag m term n

  [_x:_↓]→_ : ∀ {m n tag}
    (π : R)
    (C₀ : OneHoleContext tag m term n)
    (T : Term (n +1))
    → ---------------------
    OneHoleContext tag m term n

  λx,_ : ∀{m n tag}
    (C : OneHoleContext tag m term (n +1))
    → ----------------------
    OneHoleContext tag m term n

  ⌊_⌋ : ∀{m n tag}
    (C : OneHoleContext tag m elim n)
    → ---------------------
    OneHoleContext tag m term n

  _`_↓ : ∀ {m n tag}
    (f : Elim n)
    (C : OneHoleContext tag m term n)
    → ----------------------
    OneHoleContext tag m elim n

  _↓`_ : ∀ {m n tag}
    (C : OneHoleContext tag m elim n)
    (s : Term n)
    → ----------------------
    OneHoleContext tag m elim n

  _꞉_↓ : ∀ {m n tag}
    (s : Term n)
    (C : OneHoleContext tag m term n)
    →  ----------------------
    OneHoleContext tag m elim n

  _↓꞉_ : ∀ {m n tag}
    (C₀ : OneHoleContext tag m term n)
    (S : Term n)
    →  ----------------------
    OneHoleContext tag m elim n

infix 180 _[_/—]
_[_/—] : ∀{m n tag₀ tag₁}
  (C[—] : OneHoleContext tag₀ m tag₁ n)
  (e : expr-of-type tag₀ m)
  → ----------------------
  expr-of-type tag₁ n
— [ e /—] = e
[ π x: S ]→ C[—] ↓ [ e /—] = [ π x: S ]→ C[—] [ e /—]
([ π x: C[—] ↓]→ T) [ e /—] = [ π x: C[—] [ e /—] ]→ T
(λx, C[—]) [ e /—] = λx, C[—] [ e /—]
⌊ C[—] ⌋ [ e /—] = ⌊ C[—] [ e /—] ⌋
(f ` C[—] ↓) [ e /—] = f ` C[—] [ e /—]
(C[—] ↓` s) [ e /—] = C[—] [ e /—] ` s
(s ꞉ C[—] ↓) [ e /—] = s ꞉ C[—] [ e /—]
(C[—] ↓꞉ S) [ e /—] = C[—] [ e /—] ꞉ S

open import Function.Proof

OneContextClosed : (R : RelOnExpr 𝒵) → 𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒵 ᵖ
OneContextClosed R = ∀ {m n} {tag tag'}
  {C : OneHoleContext tag m tag' n}
  → ----------------------------
  Relating (C [_/—]) R R

1-ctx-closed : ∀ {_R'_ : RelOnExpr 𝒵}
  ⦃ 1-cc : OneContextClosed _R'_ ⦄
  {m n tag tag'}
  {e e' : expr-of-type tag m}
  (eRe' : e R' e')
  (C : OneHoleContext tag m tag' n)
  → ----------------------------
  C [ e /—] R' C [ e' /—]
1-ctx-closed ⦃ 1-cc ⦄ eRe' C = ap (C [_/—]) ⦃ 1-cc {C = C} ⦄ eRe'
