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

open import Data.Tree.Binary
open import Syntax.Context.Arbitrary
open import Function hiding (_$_)

hole-loc : ∀{hole m result n}
  (C[—] : OneHoleContext hole m result n)
  → ---------------------------------------
  Holes
hole-loc {hole}{m} — = [ hole Σ., m ]
hole-loc [ _ x: _ ]→ C[—] ↓ = ◻ /\ hole-loc C[—]
hole-loc ([ _ x: C[—] ↓]→ _) = hole-loc C[—] /\ ◻
hole-loc (λx, C[—]) = hole-loc C[—]
hole-loc ⌊ C[—] ⌋ = hole-loc C[—]
hole-loc (_ ` C[—] ↓) = ◻ /\ hole-loc C[—]
hole-loc (C[—] ↓` _) = hole-loc C[—] /\ ◻
hole-loc (_ ꞉ C[—] ↓) = ◻ /\ hole-loc C[—]
hole-loc (C[—] ↓꞉ _) = hole-loc C[—] /\ ◻

as-arbitrary : ∀{hole m result n}
  (C[—] : OneHoleContext hole m result n)
  → ----------------------------------------
  Context (hole-loc C[—]) result n
as-arbitrary — = —
as-arbitrary [ π x: S ]→ C[—] ↓ = [ π x: term S ]→ as-arbitrary C[—]
as-arbitrary ([ π x: C[—] ↓]→ T) = [ π x: as-arbitrary C[—] ]→ term T
as-arbitrary (λx, C[—]) = λx, as-arbitrary C[—]
as-arbitrary ⌊ C[—] ⌋ = ⌊ as-arbitrary C[—] ⌋
as-arbitrary (f ` C[—] ↓) = elim f ` as-arbitrary C[—]
as-arbitrary (C[—] ↓` s) = as-arbitrary C[—] ` term s
as-arbitrary (s ꞉ C[—] ↓) = term s ꞉ as-arbitrary C[—]
as-arbitrary (C[—] ↓꞉ S) = as-arbitrary C[—] ꞉ term S

open import Type.Unit

as-filling : ∀{hole m result n}
  (C[—] : OneHoleContext hole m result n)
  (e : expr-of-type hole m)
  → --------------------------------------
  all-types (hole-loc C[—])
as-filling — e = e
as-filling [ _ x: _ ]→ C[—] ↓ e = ↑type ⋆ Σ., as-filling C[—] e
as-filling ([ _ x: C[—] ↓]→ _) e = as-filling C[—] e Σ., ↑type ⋆
as-filling (λx, C[—]) e = as-filling C[—] e
as-filling ⌊ C[—] ⌋ e = as-filling C[—] e
as-filling (_ ` C[—] ↓) e = ↑type ⋆ Σ., as-filling C[—] e
as-filling (C[—] ↓` _) e = as-filling C[—] e Σ., ↑type ⋆
as-filling (_ ꞉ C[—] ↓) e = ↑type ⋆ Σ., as-filling C[—] e
as-filling (C[—] ↓꞉ _) e = as-filling C[—] e Σ., ↑type ⋆

open import Data.Maybe
import Data.List as L
open import Collection
open import Logic
open import Proof

open import Proposition.Identity.Coercion

private
  to-list/\== : (l r : Holes){x : ExprTag × ℕ}
    (p : holes-to-list (l /\ r) == L.[ x ])
    → ---------------------------------------------------------
    (holes-to-list l == L.[ x ] ∧ holes-to-list r == L.[]) ∨
    (holes-to-list l == L.[] ∧ holes-to-list r == L.[ x ])

open import Structure.Monoid

to-list/\== l r p with (
  proof holes-to-list l ∙ holes-to-list r
    === holes-to-list (l /\ r)           :by: holes-to-list-∙ l r
    === L.[ _ ]                          :by: p
  qed)
... | q with holes-to-list l | holes-to-list r
to-list/\== l r p | q | L.[ h ] | L.[] = ∨left (q , Id-refl L.[])
to-list/\== l r p | q | L.[] | L.[ h ] = ∨right (Id-refl L.[] , q)

-- postulate
--   as-one-hole : ∀{hole m result n}
--     {t : Holes}
--     (p : holes-to-list t == L.[ hole Σ., m ])
--     (C : Context t result n)
--     → -----------------------------------------------------------------
--     OneHoleContext hole m result n
{-
as-one-hole {hole}{m}{result}{n}{t = [ _ ]} p — = coe (coer p) —
  where coer : (q : L.[ result Σ., n ] == L.[ hole Σ., m ])
               → ----------------------------------------
               OneHoleContext hole m hole m
               ==
               OneHoleContext hole m result n
        coer (Id-refl _) = Id-refl _
as-one-hole {t = [ _ ]} p (λx, C) = λx, as-one-hole p C
as-one-hole {t = [ _ ]} p ⌊ C ⌋ = ⌊ as-one-hole p C ⌋
as-one-hole {t = l /\ r} p ([ π x: C₀ ]→ C₁) = {!!}
as-one-hole {t = l /\ r} p (λx, C) = λx, as-one-hole p C
as-one-hole {t = l /\ r} p ⌊ C ⌋ = ⌊ as-one-hole p C ⌋
as-one-hole {t = l /\ r} p (C₀ ` C₁) = ?
as-one-hole {t = l /\ r} p (C₀ ꞉ C₁) = {!!}
-}

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

context-equivalence : ∀{m n tag₀ tag₁}
  (C[—] : OneHoleContext tag₀ m tag₁ n)
  (e : expr-of-type tag₀ m)
  → ----------------------------------------
  C[—] [ e /—] == fill-holes (as-filling C[—] e) (as-arbitrary C[—])
context-equivalence — e = Id-refl e
context-equivalence [ π x: S ]→ C[—] ↓ e =
  ap ([ π x: S ]→_) $ context-equivalence C[—] e
context-equivalence ([ π x: C[—] ↓]→ T) e =
  ap ([ π x:_]→ T) $ context-equivalence C[—] e
context-equivalence (λx, C[—]) e =
  ap λx,_ $ context-equivalence C[—] e
context-equivalence ⌊ C[—] ⌋ e =
  ap ⌊_⌋ $ context-equivalence C[—] e
context-equivalence (f ` C[—] ↓) e =
  ap (f `_) $ context-equivalence C[—] e
context-equivalence (C[—] ↓` s) e =
  ap (_` s) $ context-equivalence C[—] e
context-equivalence (s ꞉ C[—] ↓) e =
  ap (s ꞉_) $ context-equivalence C[—] e
context-equivalence (C[—] ↓꞉ S) e =
  ap (_꞉ S) $ context-equivalence C[—] e

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

OneCtxClosed-of-CtxClosed :
  {R : RelOnExpr 𝒵}
  ⦃ context-closed : ContextClosed R ⦄
  → ----------------------------------
  OneContextClosed R

rel-preserv ⦃ OneCtxClosed-of-CtxClosed {R = R}{C = C} ⦄ {a}{b} rab =
  go rab C
  where go : ∀{m n tag tag'}{e e' : expr-of-type tag m}
             (p : R e e')
             (C : OneHoleContext tag m tag' n)
             → ----------------------------------------
             R (C [ e /—]) (C [ e' /—])
        go p — = p
        go p [ π x: S ]→ C ↓ =
          ctx-closed ([ π x: term S ]→ —)
            {es = ↑type ⋆ Σ., _}
            {es' = ↑type ⋆ Σ., _}
            (↑prop ⋆ₚ , go p C)
        go p ([ π x: C ↓]→ T) =
          ctx-closed ([ π x: — ]→ term T)
            {es = _ Σ., ↑type ⋆}
            {es' = _ Σ., ↑type ⋆}
            (go p C , ↑prop ⋆ₚ)
        go p (λx, C) = ctx-closed (λx, —) (go p C)
        go p ⌊ C ⌋ = ctx-closed ⌊ — ⌋ (go p C)
        go p (f ` C ↓) =
          ctx-closed (elim f ` —)
            {es = ↑type ⋆ Σ., _}
            {es' = ↑type ⋆ Σ., _}
            (↑prop ⋆ₚ , go p C)
        go p (C ↓` s) =
          ctx-closed (— ` term s)
            {es =  _ Σ., ↑type ⋆}
            {es' = _ Σ., ↑type ⋆}
            (go p C , ↑prop ⋆ₚ)
        go p (s ꞉ C ↓) =
          ctx-closed (term s ꞉ —)
            {es = ↑type ⋆ Σ., _}
            {es' = ↑type ⋆ Σ., _}
            (↑prop ⋆ₚ , go p C)
        go p (C ↓꞉ S) = 
          ctx-closed (— ꞉ term S)
            {es =  _ Σ., ↑type ⋆}
            {es' = _ Σ., ↑type ⋆}
            (go p C , ↑prop ⋆ₚ)
