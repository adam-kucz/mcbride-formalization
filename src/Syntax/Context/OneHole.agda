{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Syntax.Context.OneHole
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax

open import Type.Sum hiding (_,_)
open import Data.Nat hiding (_⊔_)
open import Data.Vec

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

open import Syntax.Context.Arbitrary
open import Function hiding (_$_)

as-arbitrary : ∀{hole m result n}
  (C[—] : OneHoleContext hole m result n)
  → ----------------------------------------
  Context [ hole Σ., m ] result n
as-arbitrary — = —
as-arbitrary [ π x: S ]→ C[—] ↓ = [ π x: term S ]→ as-arbitrary C[—]
as-arbitrary ([ π x: C[—] ↓]→ T) = [ π x: as-arbitrary C[—] ]→ term T
as-arbitrary (λx, C[—]) = λx, as-arbitrary C[—]
as-arbitrary ⌊ C[—] ⌋ = ⌊ as-arbitrary C[—] ⌋
as-arbitrary (f ` C[—] ↓) = elim f ` as-arbitrary C[—]
as-arbitrary (C[—] ↓` s) = as-arbitrary C[—] ` term s
as-arbitrary (s ꞉ C[—] ↓) = term s ꞉ as-arbitrary C[—]
as-arbitrary (C[—] ↓꞉ S) = as-arbitrary C[—] ꞉ term S

open import Proof

open import Proposition.Identity.Coercion

as-one-hole : ∀{hole m result n k}{v : Holes k}
  (C : Context v result n)
  (p : k == 1)
  (q : v Het.== [ hole Σ., m ])
  → ----------------------------------------
  OneHoleContext hole m result n
as-one-hole {hole}{m}{result}{n} — p q =
  coe (ap2 (OneHoleContext hole m)
           (ap (pr₁ ∘ head) $ subrel {_R_ = Het._==_} $ sym q)
           (ap (pr₂ ∘ head) $ subrel {_R_ = Het._==_} $ sym q)) —
as-one-hole ([ π x: C ]→ C₁) p q = {!!}
as-one-hole (λx, C) p q = {!!}
as-one-hole ⌊ C ⌋ p q = {!!}
as-one-hole (C ` C₁) p q = {!!}
as-one-hole (C ꞉ C₁) p q = {!!}

ctx-equivalence : 
  (hole : ExprTag) -- required type of hole
  (m : ℕ) -- number of free variables in hole
  (result : ExprTag) -- type resulting from filling hole
  (n : ℕ) -- number of free variables of the context (n ≤ m)
  → ---------------------------------------------------------
  Bijection (OneHoleContext hole m result n)
            (Context [ hole Σ., m ] result n)
forw ⦃ ctx-equivalence hole m result n ⦄ = as-arbitrary
back ⦃ ctx-equivalence hole m result n ⦄ = {!!}
bi-inverse ⦃ ctx-equivalence hole m result n ⦄ = {!!}

{-
open import Type.Unit

infix 180 _[_/—]
_[_/—] : {m n : ℕ}
  {tag₀ tag₁ : ExprTag}
  (C[—] : 1-hole-ctx tag₀ m tag₁ n)
  (e : expr-of-type tag₀ m)
  → ----------------------
  expr-of-type tag₁ n
C[—] [ e /—] = fill-holes (e Σ., ↑type ⋆) C[—]

open import Function.Proof

1-ContextClosed : (R : RelOnExpr 𝒵) → 𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒵 ᵖ
1-ContextClosed R = ∀ {m n} {tag tag'}
  {C : 1-hole-ctx tag m tag' n}
  → ----------------------------
  Relating (C [_/—]) R R

1-ctx-closed : ∀ {_R'_ : RelOnExpr 𝒵}
  ⦃ 1-cc : 1-ContextClosed _R'_ ⦄
  {m n tag tag'}
  {e e' : expr-of-type tag m}
  (eRe' : e R' e')
  (C : 1-hole-ctx tag m tag' n)
  → ----------------------------
  C [ e /—] R' C [ e' /—]
1-ctx-closed ⦃ 1-cc ⦄ eRe' C = ap (C [_/—]) ⦃ 1-cc {C = C} ⦄ eRe'

instance
  1-CtxClosed-of-CtxClosed :
     {R : RelOnExpr 𝒵}
     ⦃ context-closed : ContextClosed R ⦄
     → ----------------------------------
     1-ContextClosed R

rel-preserv ⦃ 1-CtxClosed-of-CtxClosed {C = C} ⦄ rab =
  ctx-closed C λ { zero _ → rab ; (_ +1) (s≤s ())}
-}
