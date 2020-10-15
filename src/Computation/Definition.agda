{-# OPTIONS --exact-split #-}
open import Universes
open import Basic using (Rig; wfs)

module Computation.Definition
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax

open import Type.Identity hiding (refl)
open import Function using (_$_)
open import Relation.Binary
open import Operation.Binary.Property
open import Data.Nat hiding (_⊔_)

-- Definition 5 (contraction, reduction, computation)

private
  module Tag {tag : ExprTag} where
    open import Substitution
    open WithInstanceArgs ⦃ subst = SubstitutableExpr {tag = tag} ⦄ public
open Tag

open import Syntax.Context.OneHole.Definition
open import Logic

infix 36 _⇝_
data _⇝_ : RelOnExpr (𝒰 ⁺ ⊔ 𝒱) where
  β : ∀ π (s S : Term n)(t T : Term (n +1))
    → ----------------------------------------------------
    (λx, t ꞉ ([ π x: S ]→ T)) ` s ⇝ (t ꞉ T) [ s ꞉ S /new]

  v : (t T : Term n)
    → --------------
    ⌊ t ꞉ T ⌋ ⇝ t

  hole : ∀ {m n tag₀ tag₁ s t}
    (C[—] : OneHoleContext tag₀ m tag₁ n)
    (reduct : s ⇝ t)
    → --------------------
    C[—] [ s /—] ⇝ C[—] [ t /—]

open import Relation.Binary.ReflexiveTransitiveClosure

infix 36 _↠_
_↠_ : RelOnExpr (𝒰 ⁺ ⊔ 𝒱)
_↠_ = refl-trans-close _⇝_
  
-- infix 36 _↠-expl_
-- data _↠-expl_ : RelOnExpr (𝒰 ⁺ ⊔ 𝒱) where
--   β : ∀ π {s s' S S' : Term n}{t t' T T' : Term (n +1)}
--     (t↠t' : t ↠-expl t')(S↠S' : S ↠-expl S')
--     (T↠T' : T ↠-expl T')(s↠s' : s ↠-expl s')
--     → ----------------------------------------------------------------
--     (λx, t ꞉ ([ π x: S ]→ T)) ` s ↠-expl (t' ꞉ T') [ s' ꞉ S' /new]

--   v : {t t' : Term n}(T : Term n)
--     (t↠t' : t ↠-expl t')
--     → ------------------------
--     ⌊ t ꞉ T ⌋ ↠-expl t'

--   ⋆ : ∀ i → ⋆ {n = n} i ↠-expl ⋆ i

--   var : (x : Var n) → var x ↠-expl var x

--   [_x:_]→_ : ∀
--     (π : R) {S S' : Term n}{T T'}
--     (S↠S' : S ↠-expl S') (T↠T' : T ↠-expl T')
--     → --------------------------------------------
--     [ π x: S ]→ T ↠-expl [ π x: S' ]→ T'

--   λx,_ : ∀{t t' : Term (n +1)}
--     (t↠t' : t ↠-expl t')
--     → ----------------------
--     _↠-expl_ {n = n}{term} (λx, t)(λx, t')

--   ⌊_⌋ : ∀{e e' : Elim n}
--     (e↠e' : e ↠-expl e')
--     → ---------------------
--     _↠-expl_ {n = n}{term} ⌊ e ⌋ ⌊ e' ⌋

--   _`_ : ∀{f f' : Elim n}{s s' : Term n}
--     (f↠f' : f ↠-expl f') (s↠s' : s ↠-expl s')
--     → --------------------------------------------
--     f ` s ↠-expl f' ` s'

--   _꞉_ : ∀{s s' S S' : Term n}
--     (s↠s' : s ↠-expl s') (S↠S' : S ↠-expl S')
--     →  ------------------------------------------
--     s ꞉ S ↠-expl s' ꞉ S'

