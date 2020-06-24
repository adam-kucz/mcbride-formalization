{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Syntax.Context.OneHole.Substitutable
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax.Context.OneHole.Definition
open import Syntax.Context.OneHole.Equivalence
open import Syntax.Context.Arbitrary renaming ([_] to [[_]])
open import Syntax.Context.Substitutable
open import Substitution

open import Data.Nat

instance
  SubstitutableOneHoleContext : ∀{hole m tag} →
    Substitutable (
      λ n → OneHoleContext hole (m + n) tag n)

private
  subc = λ {tag}{t}{m}{n} →
    sub ⦃ subst = SubstitutableContext {t = t}{tag} ⦄ {m = m}{n}

open import Type.Sum hiding (_,_)
open import Data.Nat
open import Data.Nat.Arithmetic.Subtraction.Unsafe
open import Function hiding (_$_)
open import Proof

import Data.Functor as F
open import Data.Functor.Construction
open import Data.Maybe.Functor
open import Data.Tree.Binary.Functor
open F.Functor (ComposeFunctor ⦃ BinaryTreeFunctor ⦄ ⦃ MaybeFunctor ⦄)

open import Proposition.Identity.Coercion

hole-loc-as-fmap : ∀{hole n tag m}
  (C : OneHoleContext hole n tag m)
  → ---------------------------------
  hole-loc C == fmap [ id × _+ m ] (fmap [ id × _- m ] (hole-loc C))
hole-loc-as-fmap {hole}{n} — =
  ap (λ — → [[ hole Σ., — + n ]]) $ sym $ subrel $
  left-inverse-of (_+ n) 0
hole-loc-as-fmap [ π x: S ]→ C ↓ = {!!}
hole-loc-as-fmap ([ π x: C ↓]→ T) = {!!}
hole-loc-as-fmap {m = m} (λx, C) = ap (λ — → — (hole-loc C)) (
  proof id
    === fmap id
      :by: sym fmap-id
    === fmap ([ id × _+ m ] ∘ [ id × _- m ])
      :by: {!!}
    === fmap [ id × _+ m ] ∘ fmap [ id × _- m ]
      :by: fmap-∘ [ id × _+ m ] [ id × _- m ]
  qed)
hole-loc-as-fmap ⌊ C ⌋ = hole-loc-as-fmap C
hole-loc-as-fmap (f ` C ↓) = {!!}
hole-loc-as-fmap (C ↓` s) = {!!}
hole-loc-as-fmap (s ꞉ C ↓) = {!!}
hole-loc-as-fmap (C ↓꞉ S) = {!!}

one-hole-fmap : ∀{hole n tag m} k
  (C : OneHoleContext hole (n + m) tag m)
  → -----------------------------------------------------------------------------
  one-hole hole (n + k) (fmap [ id × _+ k ] (fmap [ id × _- m ] (hole-loc C)))
one-hole-fmap k C = {!!}

SubstitutableOneHoleContext {hole}{m}{tag} = DirectSubstitutable
  (λ {m}{n} σ C →
    as-one-hole (one-hole-fmap n C) (
      subc σ (coe (ap (λ t → Context t tag m) (hole-loc-as-fmap C))
                  (as-arbitvrary C))))
  {!as-one-hole-as-arbitrary!}
  {!!}
