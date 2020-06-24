{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Computation.Definition
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax

open import Proposition.Identity hiding (refl)
open import Proposition.Function using (_$_)
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
  
