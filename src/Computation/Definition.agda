{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Computation.Definition
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax
open import Substitution using (_[_/new])

open import Proposition.Identity hiding (refl)
open import Proposition.Function using (_$_)
open import Relation.Binary
open import Operation.Binary.Property
open import Data.Nat hiding (_⊔_)

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

open import Syntax.Context.OneHole

infix 36 _⇝_
data _⇝_ : RelOnExpr (𝒰 ⁺ ⊔ 𝒱)
  where
  β-exact : {s t : Elim n}
    (β : s ⇝β t)
    → -------------
    s ⇝ t

  v-exact : {s t : Term n}
    (v : s ⇝v t)
    → -------------
    s ⇝ t

  hole : ∀ {m n tag₀ tag₁ s t}
    (C[—] : OneHoleContext tag₀ m tag₁ n)
    (reduct : s ⇝ t)
    → --------------------
    C[—] [ s /—] ⇝ C[—] [ t /—]

open import Relation.Binary.ReflexiveTransitiveClosure

infix 36 _↠_
_↠_ : RelOnExpr (𝒰 ⁺ ⊔ 𝒱)
_↠_ = refl-trans-close _⇝_
  
