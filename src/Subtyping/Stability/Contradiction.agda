{-# OPTIONS --exact-split --prop #-}
module Subtyping.Stability.Contradiction where

open import Universes
open import Basic

module Generic
    {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
    {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
    where
  open import Data.Nat hiding (_⊔_)
  open import Syntax

  infixl 30 _≼_
  data _≼_ : RelOnExpr (𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲) where
    refl≼ : (e : expr-of-type tag n) → e ≼ e
  
    sort : ∀{i j}
      (p : j ≻ i)
      → ------------
      _≼_ {n}{term} (⋆ i) (⋆ j)
  
    [_x:_]→_ : ∀ π {S S' T T'}
      (p : S' ≼ S)
      (q : T ≼ T')
      → ---------------------
      _≼_ {n}{term} ([ π x: S ]→ T)([ π x: S' ]→ T')

  private
    module Tag {tag : ExprTag} where
      open import Substitution ⦃ rig ⦄ ⦃ wfs ⦄
      open WithInstanceArgs ⦃ subst = SubstitutableExpr {tag = tag} ⦄ public
  open Tag

  postulate
    ≼-stable' : ∀
      (r : Term m){R R'}
      (n≤m : n ≤ m)
      {tag}
      {S T : expr-of-type tag (m +1)}
      (S≼T : S ≼ T)
      (R'≼R : R' ≼ R)
      → ---------------
      S [ r ꞉ R / n [ n≤m ]] ≼ T [ r ꞉ R' / n [ n≤m ]]


open import Data.Nat
open import Data.FinNat

open import Basic.Instance
instance
    _ = HemiringFinℕ+*
WFS = WellFoundedSortsℕ

open import Syntax {R = None-one-tons} ⦃ wfs = WFS ⦄
-- private
--   module Tag {tag : ExprTag} where
--     open import Substitution {R = None-one-tons} ⦃ wfs = WFS ⦄
--     open WithInstanceArgs ⦃ subst = SubstitutableExpr {tag = tag} ⦄ public
-- open Tag
-- open import Substitution {R = None-one-tons} ⦃ wfs = WFS ⦄
--   hiding (sub; _[_/_[_]])
open Generic {R = None-one-tons} ⦃ wfs = WFS ⦄

open import Logic
open import Proof

contradiction : ⊥
contradiction with prf
  where prf : ⋆ 0 ꞉ ⋆ 1 ≼ ⋆ 0 ꞉ ⋆ 0
        prf = ≼-stable' (⋆ 0) (z≤ 0) (refl≼ S) (sort (z<s 0))
          where S : Elim 1
                S = var new
... | ()
