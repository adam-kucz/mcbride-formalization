{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Computation.Equivalence
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Computation.Definition
open import Syntax

private
  module Tag {tag : ExprTag} where
    open import Substitution
    open WithInstanceArgs ⦃ subst = SubstitutableExpr {tag = tag} ⦄ public
open Tag

open import Data.Nat hiding (_⊔_)

infix 36 _⇝'_
data _⇝'_ : RelOnExpr (𝒰 ⁺ ⊔ 𝒱) where
  β : ∀ π (s S : Term n)(t T : Term (n +1))
    → ----------------------------------------------------
    (λx, t ꞉ ([ π x: S ]→ T)) ` s ⇝' (t ꞉ T) [ s ꞉ S /new]

  v : (t T : Term n)
    → --------------
    ⌊ t ꞉ T ⌋ ⇝' t

  λx,_ : {t t' : Term (n +1)}
    (p : t ⇝' t')
    → ------------------------
    λx, t ⇝' λx, t'

  ⌊_⌋ : {e e' : Elim n}
    (p : e ⇝' e')
    → -----------------
    ⌊ e ⌋ ⇝' ⌊ e' ⌋

  [_x:_]→_↓ : ∀ π {T T' : Term (n +1)}
    (S : Term n)
    (T⇝'T' : T ⇝' T')
    → -------------------------------
    [ π x: S ]→ T ⇝' [ π x: S ]→ T'

  [_x:_↓]→_ : ∀ π {S S' : Term n}
    (S⇝'S' : S ⇝' S')
    (T : Term (n +1))
    → -------------------------------
    [ π x: S ]→ T ⇝' [ π x: S' ]→ T

  _`_↓ : ∀
    (f : Elim n){s s'}
    (s⇝'s' : s ⇝' s')
    → -------------------------------
    f ` s ⇝' f ` s'

  _↓`_ : ∀{f f'}
    (f⇝'f' : f ⇝' f')
    (s : Term n)
    → -------------------------------
    f ` s ⇝' f' ` s

  _꞉_↓ : ∀
    (s : Term n){S S'}
    (S⇝'S' : S ⇝' S')
    → -------------------------------
    s ꞉ S ⇝' s ꞉ S'

  _↓꞉_ : ∀{s s'}
    (s⇝'s' : s ⇝' s')
    (S : Term n)
    → -------------------------------
    s ꞉ S ⇝' s' ꞉ S

open import Syntax.Context
open import Computation.Property.General

open import Relation.Binary

instance
  ⇝'⊆⇝ : (_⇝'_ {n = n}{tag}) ⊆ _⇝_
  ⇝⊆⇝' : (_⇝_ {n = n}{tag}) ⊆ _⇝'_

subrel ⦃ ⇝'⊆⇝ ⦄ (β π s S t T) = β π s S t T
subrel ⦃ ⇝'⊆⇝ ⦄ (v t T) = v t T
subrel ⦃ ⇝'⊆⇝ ⦄ (λx, t⇝'t') =
  1-ctx-closed (subrel ⦃ ⇝'⊆⇝ ⦄ t⇝'t') (λx, —)
subrel ⦃ ⇝'⊆⇝ ⦄ ⌊ e⇝'e' ⌋ =
  1-ctx-closed (subrel ⦃ ⇝'⊆⇝ ⦄ e⇝'e') ⌊ — ⌋
subrel ⦃ ⇝'⊆⇝ ⦄ [ π x: S ]→ T⇝'T' ↓ =
  1-ctx-closed (subrel ⦃ ⇝'⊆⇝ ⦄ T⇝'T') ([ π x: S ]→ — ↓)
subrel ⦃ ⇝'⊆⇝ ⦄ ([ π x: S⇝'S' ↓]→ T) =
  1-ctx-closed (subrel ⦃ ⇝'⊆⇝ ⦄ S⇝'S') ([ π x: — ↓]→ T)
subrel ⦃ ⇝'⊆⇝ ⦄ (f ` s⇝'s' ↓) =
  1-ctx-closed (subrel ⦃ ⇝'⊆⇝ ⦄ s⇝'s') (f ` — ↓)
subrel ⦃ ⇝'⊆⇝ ⦄ (f⇝'f' ↓` s) =
  1-ctx-closed (subrel ⦃ ⇝'⊆⇝ ⦄ f⇝'f') (— ↓` s)
subrel ⦃ ⇝'⊆⇝ ⦄ (s ꞉ S⇝'S' ↓) =
  1-ctx-closed (subrel ⦃ ⇝'⊆⇝ ⦄ S⇝'S') (s ꞉ — ↓)
subrel ⦃ ⇝'⊆⇝ ⦄ (s⇝'s' ↓꞉ S) =
  1-ctx-closed (subrel ⦃ ⇝'⊆⇝ ⦄ s⇝'s') (— ↓꞉ S)

subrel ⦃ ⇝⊆⇝' ⦄ (β π s S t T) = β π s S t T
subrel ⦃ ⇝⊆⇝' ⦄ (v t T) = v t T
subrel ⦃ ⇝⊆⇝' ⦄ (hole — s⇝t) = subrel s⇝t
subrel ⦃ ⇝⊆⇝' ⦄ (hole (λx, C[—]) s⇝t) = λx, subrel (hole C[—] s⇝t)
subrel ⦃ ⇝⊆⇝' ⦄ (hole ⌊ C[—] ⌋ s⇝t) = ⌊ subrel (hole C[—] s⇝t) ⌋
subrel ⦃ ⇝⊆⇝' ⦄ (hole [ π x: S ]→ C[—] ↓ s⇝t) =
  [ π x: S ]→ subrel (hole C[—] s⇝t) ↓
subrel ⦃ ⇝⊆⇝' ⦄ (hole ([ π x: C[—] ↓]→ T) s⇝t) =
  [ π x: subrel (hole C[—] s⇝t) ↓]→  T
subrel ⦃ ⇝⊆⇝' ⦄ (hole (f ` C[—] ↓) s⇝t) =
  f ` subrel (hole C[—] s⇝t) ↓
subrel ⦃ ⇝⊆⇝' ⦄ (hole (C[—] ↓` s) s⇝t) =
  subrel (hole C[—] s⇝t) ↓` s
subrel ⦃ ⇝⊆⇝' ⦄ (hole (s ꞉ C[—] ↓) s⇝t) =
  s ꞉ subrel (hole C[—] s⇝t) ↓
subrel ⦃ ⇝⊆⇝' ⦄ (hole (C[—] ↓꞉ S) s⇝t) =
  subrel (hole C[—] s⇝t) ↓꞉ S
