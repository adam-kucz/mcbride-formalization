{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Syntax.Context.OneHole.Equivalence
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax.Context.OneHole.Definition
open import Syntax.Context.Arbitrary
open import Syntax

open import Type.Sum hiding (_,_) renaming (_×_ to _χ_)
open import Data.Nat
open import Data.Tree.Binary
open import Function hiding (_$_)

import Data.Functor as F
open import Data.Functor.Construction
open import Data.Maybe.Functor
open import Data.Tree.Binary.Functor
open F.Functor (ComposeFunctor ⦃ BinaryTreeFunctor ⦄ ⦃ MaybeFunctor ⦄)

hole-loc : ∀{hole m result n}
  (C[—] : OneHoleContext hole m result n)
  → ---------------------------------------
  Holes
hole-loc {hole}{m} — = [ hole Σ., 0 ]
hole-loc [ _ x: _ ]→ C[—] ↓ = ◻ /\ fmap [ id × suc ] (hole-loc C[—])
hole-loc ([ _ x: C[—] ↓]→ _) = hole-loc C[—] /\ ◻
hole-loc (λx, C[—]) = fmap [ id × suc ] (hole-loc C[—])
hole-loc ⌊ C[—] ⌋ = hole-loc C[—]
hole-loc (_ ` C[—] ↓) = ◻ /\ hole-loc C[—]
hole-loc (C[—] ↓` _) = hole-loc C[—] /\ ◻
hole-loc (_ ꞉ C[—] ↓) = ◻ /\ hole-loc C[—]
hole-loc (C[—] ↓꞉ _) = hole-loc C[—] /\ ◻

as-arbitrary : ∀{hole m result n}
  (C[—] : OneHoleContext hole m result n)
  → ----------------------------------------
  Context (fmap [ id × _+ n ] (hole-loc C[—])) result n

open import Data.Nat
open import Proof

open import Proposition.Identity.Coercion

as-arbitrary — = —
as-arbitrary [ π x: S ]→ C[—] ↓ =
  [ π x: term S ]→ coe {!!} (as-arbitrary C[—])
as-arbitrary ([ π x: C[—] ↓]→ T) = [ π x: as-arbitrary C[—] ]→ term T
as-arbitrary {n = n} (λx, C[—]) =
  λx, coe (ap (λ f → Context (f (hole-loc C[—])) term (n +1)) (
    proof fmap [ id × _+ (n +1) ]
      === fmap ([ id × _+ n ] ∘ [ id × suc ])
        :by: ap fmap ?
      === fmap [ id × _+ n ] ∘ fmap [ id × suc ]
        :by: fmap-∘ [ id × _+ n ] [ id × suc ]
    qed))
    (as-arbitrary C[—])
as-arbitrary ⌊ C[—] ⌋ = ⌊ as-arbitrary C[—] ⌋
as-arbitrary (f ` C[—] ↓) = elim f ` as-arbitrary C[—]
as-arbitrary (C[—] ↓` s) = as-arbitrary C[—] ` term s
as-arbitrary (s ꞉ C[—] ↓) = term s ꞉ as-arbitrary C[—]
as-arbitrary (C[—] ↓꞉ S) = as-arbitrary C[—] ꞉ term S
-- as-arbitrary [ π x: S ]→ C[—] ↓ = [ π x: term S ]→ as-arbitrary C[—]
-- as-arbitrary (λx, C[—]) = λx, as-arbitrary C[—]

-- open import Collection
-- import Data.List as L
-- import Data.Maybe

-- HolesListable : Listable _ Holes (ExprTag × ℕ)
-- HolesListable = NestedListable (ExprTag × ℕ) HoleType Holes
-- private
--   instance
--     _ = HolesListable

-- open import Structure.Monoid hiding (e)

-- holes-to-list = to-list ⦃ HolesListable ⦄

-- holes-to-list-∙ : ∀ l r
--   → ------------------------------------------------------------
--   holes-to-list l ∙ holes-to-list r == holes-to-list (l /\ r)
-- holes-to-list-∙ l r =
--   proof holes-to-list l ∙ holes-to-list r
--     === mconcat (L.map f (to-list l) ∙ L.map f (to-list r))
--       :by: sym $ mconcat-∪ (L.map f (to-list l)) (L.map f (to-list r))
--     === holes-to-list (l /\ r)
--       :by: ap mconcat $ sym $ L.map++ (to-list l) (to-list r) f
--   qed
--   where f = to-list {Col = HoleType}

open import Logic

empty-holes : Holes → 𝒰₀ ᵖ
empty-holes ◻ = ⊤
empty-holes [ _ ] = ⊥
empty-holes (l /\ r) = empty-holes l ∧ empty-holes r

data one-hole tag m : Holes → 𝒰₀ ˙ where
  leaf : one-hole tag m [ tag Σ., m ]
  left : ∀{l r}
    (p : one-hole tag m l)
    (q : empty-holes r)
    → ------------------
    one-hole tag m (l /\ r)
  right : ∀{l r}
    (p : empty-holes l)
    (q : one-hole tag m r)
    → ------------------
    one-hole tag m (l /\ r)

as-expr : ∀{tag m t}
  (p : empty-holes t)
  (C : Context t tag m)
  → ----------------------------------------
  expr-of-type tag m
as-expr p (term t) = t
as-expr p (elim e) = e
as-expr p ([ π x: C₀ ]→ C₁) =
  [ π x: as-expr (∧left p) C₀ ]→ as-expr (∧right p) C₁
as-expr p (λx, C) = λx, as-expr p C
as-expr p ⌊ C ⌋ = ⌊ as-expr p C ⌋
as-expr p (C₀ ` C₁) = as-expr (∧left p) C₀ ` as-expr (∧right p) C₁
as-expr p (C₀ ꞉ C₁) = as-expr (∧left p) C₀ ꞉ as-expr (∧right p) C₁

as-one-hole : ∀{hole m result n t}
  (p : one-hole hole m t)
  (C : Context t result n)
  → ----------------------------------------
  OneHoleContext hole m result n
as-one-hole p (λx, C) = λx, as-one-hole p C
as-one-hole p ⌊ C ⌋ = ⌊ as-one-hole p C ⌋
as-one-hole leaf — = —
as-one-hole (left p q)([ π x: C₀ ]→ C₁) =
  [ π x: as-one-hole p C₀ ↓]→ as-expr q C₁
as-one-hole (right p q)([ π x: C₀ ]→ C₁) =
  [ π x: as-expr p C₀ ]→ as-one-hole q C₁ ↓
as-one-hole (left p q)(C₀ ` C₁) = as-one-hole p C₀ ↓` as-expr q C₁
as-one-hole (right p q)(C₀ ` C₁) = as-expr p C₀ ` as-one-hole q C₁ ↓
as-one-hole (left p q)(C₀ ꞉ C₁) = as-one-hole p C₀ ↓꞉ as-expr q C₁
as-one-hole (right p q)(C₀ ꞉ C₁) = as-expr p C₀ ꞉ as-one-hole q C₁ ↓

one-hole-hole-loc :  ∀{hole m result n}
  (C[—] : OneHoleContext hole m result n)
  → ----------------------------------------
  one-hole hole m (fmap [ id × _+ n ] (hole-loc C[—]))
{-
one-hole-hole-loc — = leaf
one-hole-hole-loc [ _ x: _ ]→ C[—] ↓ =
  right ⋆ₚ (one-hole-hole-loc C[—])
one-hole-hole-loc ([ _ x: C[—] ↓]→ _) =
  left (one-hole-hole-loc C[—]) ⋆ₚ
one-hole-hole-loc (λx, C[—]) = one-hole-hole-loc C[—]
one-hole-hole-loc ⌊ C[—] ⌋ = one-hole-hole-loc C[—]
one-hole-hole-loc (_ ` C[—] ↓) =
  right ⋆ₚ (one-hole-hole-loc C[—])
one-hole-hole-loc (C[—] ↓` _) =
  left (one-hole-hole-loc C[—]) ⋆ₚ
one-hole-hole-loc (_ ꞉ C[—] ↓) =
  right ⋆ₚ (one-hole-hole-loc C[—])
one-hole-hole-loc (C[—] ↓꞉ _) =
  left (one-hole-hole-loc C[—]) ⋆ₚ
-}

as-one-hole-as-arbitrary : ∀{hole m result n}
  (C[—] : OneHoleContext hole m result n)
  → --------------------------------------------------------------
  as-one-hole (one-hole-hole-loc C[—]) (as-arbitrary C[—]) == C[—]
{-
as-one-hole-as-arbitrary — = Id.refl —
as-one-hole-as-arbitrary [ π x: S ]→ C[—] ↓ =
  ap [ π x: S ]→_↓ $ as-one-hole-as-arbitrary C[—]
as-one-hole-as-arbitrary ([ π x: C[—] ↓]→ T) =
  ap ([ π x:_↓]→ T) $ as-one-hole-as-arbitrary C[—]
as-one-hole-as-arbitrary (λx, C[—]) =
  ap λx,_ $ as-one-hole-as-arbitrary C[—]
as-one-hole-as-arbitrary ⌊ C[—] ⌋ =
  ap ⌊_⌋ $ as-one-hole-as-arbitrary C[—]
as-one-hole-as-arbitrary (f ` C[—] ↓) =
  ap (f `_↓) $ as-one-hole-as-arbitrary C[—]
as-one-hole-as-arbitrary (C[—] ↓` s) =
  ap (_↓` s) $ as-one-hole-as-arbitrary C[—]
as-one-hole-as-arbitrary (s ꞉ C[—] ↓) =
  ap (s ꞉_↓) $ as-one-hole-as-arbitrary C[—]
as-one-hole-as-arbitrary (C[—] ↓꞉ S) =
  ap (_↓꞉ S) $ as-one-hole-as-arbitrary C[—]
-}

{-
hole-loc-as-one-hole : ∀{hole n t tag m}
  (p : one-hole hole n t)
  (C : Context t tag m)
  → -------------------------------------------------------------
  hole-loc (as-one-hole p C) == t
hole-loc-as-one-hole p (λx, C) = hole-loc-as-one-hole p C
hole-loc-as-one-hole p ⌊ C ⌋ = hole-loc-as-one-hole p C
hole-loc-as-one-hole leaf — = Id.refl [ _ Σ., _ ]
hole-loc-as-one-hole (left p q)([ _ x: C₀ ]→ C₁) =
  ap2 _/\_ (hole-loc-as-one-hole p C₀) {!!}
hole-loc-as-one-hole (right p q)([ _ x: C₀ ]→ C₁) = {!!}
hole-loc-as-one-hole (left p q)(C₀ ` C₁) = {!!}
hole-loc-as-one-hole (right p q)(C₀ ` C₁) = {!!}
hole-loc-as-one-hole (left p q)(C₀ ꞉ C₁) = {!!}
hole-loc-as-one-hole (right p q)(C₀ ꞉ C₁) = {!!}

as-arbitrary-as-one-hole : ∀{hole m result n t}
  (p : one-hole hole m t)
  → ------------------------------------------------------
  as-arbitrary {hole}{m}{result}{n} ∘ as-one-hole p ~ id
as-arbitrary-as-one-hole {n = n} p (λx, C) =
  Id.ap2 {K = λ t _ → Context t term n}
         (λ (t : Holes)(C : Context t term (n +1)) → λx, C)
         (hole-loc-as-one-hole p C)
         (as-arbitrary-as-one-hole p C)
as-arbitrary-as-one-hole p ⌊ C ⌋ = {!!}
as-arbitrary-as-one-hole p ([ π x: C₀ ]→ C₁) = {!!}
as-arbitrary-as-one-hole p (C₀ ` C₁) = {!!}
as-arbitrary-as-one-hole p (C₀ ꞉ C₁) = {!!}
as-arbitrary-as-one-hole leaf — = Het.refl —
-}

open import Type.Unit

as-filling : ∀{hole m result n}
  (C[—] : OneHoleContext hole m result n)
  (e : expr-of-type hole m)
  → --------------------------------------
  all-types (fmap [ id × _+ n ] (hole-loc C[—]))
{-
as-filling — e = e
as-filling [ _ x: _ ]→ C[—] ↓ e = ↑type ⋆ Σ., as-filling C[—] e
as-filling ([ _ x: C[—] ↓]→ _) e = as-filling C[—] e Σ., ↑type ⋆
as-filling (λx, C[—]) e = as-filling C[—] e
as-filling ⌊ C[—] ⌋ e = as-filling C[—] e
as-filling (_ ` C[—] ↓) e = ↑type ⋆ Σ., as-filling C[—] e
as-filling (C[—] ↓` _) e = as-filling C[—] e Σ., ↑type ⋆
as-filling (_ ꞉ C[—] ↓) e = ↑type ⋆ Σ., as-filling C[—] e
as-filling (C[—] ↓꞉ _) e = as-filling C[—] e Σ., ↑type ⋆
-}

context-equivalence : ∀{m n tag₀ tag₁}
  (C[—] : OneHoleContext tag₀ m tag₁ n)
  (e : expr-of-type tag₀ m)
  → ----------------------------------------
  C[—] [ e /—] == fill-holes (as-filling C[—] e) (as-arbitrary C[—])
{-
context-equivalence — e = Id.refl e
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
-}

OneCtxClosed-of-CtxClosed :
  {R : RelOnExpr 𝒵}
  ⦃ context-closed : ContextClosed R ⦄
  → ----------------------------------
  OneContextClosed R

open import Function.Proof

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
