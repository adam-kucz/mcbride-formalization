{-# OPTIONS --exact-split --prop #-}
open import Basic
open import PropUniverses

module Subtyping.Stability
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Subtyping.Definition
open import Subtyping.Property
open import Subtyping.Proof

-- Lemma 21 (subtyping stability)
-- modified to reflect true need

open import Syntax
open import Renaming
open import Substitution using (nthSub; lift-nth)
private
  module Tag {tag : ExprTag} where
    open import Substitution
    open WithInstanceArgs ⦃ subst = SubstitutableExpr {tag = tag} ⦄ public
open Tag
open import Liftable

-- open import Type.BinarySum renaming (_+_ to _⊹_)
open import Proposition.BinarySum
open import Data.Nat hiding (_⊔_)
-- open import Relation.Binary hiding (_~_)
-- open import Relation.Binary.Pointwise
-- open import Function hiding (_$_; _~_)
open import Logic
open import Proof
open import Function.Proof

-- open import Axiom.FunctionExtensionality

module StabilityVersion2 (
  ≼-stable' : ∀(r : Term m){R R'}
    (n≤m : n ≤ m)
    {S T : expr-of-type tag (m +1)}
    (S≼T : S ≼ T)
    (R'≼≽R : R' ≼ R)
    → ---------------
    S [ r ꞉ R / n [ n≤m ]] ≼ T [ r ꞉ R' / n [ n≤m ]]
  ) where

  open import Basic.Instance
  open import Data.Nat
  open import Data.FinNat
  instance
    _ = HemiringFinℕ+*
  WFS = WellFoundedSortsℕ

  open import Syntax {R = None-one-tons} ⦃ wfs = WFS ⦄
  open import ParallelReduction {R = None-one-tons} ⦃ wfs = WFS ⦄


  contradiction : ⊥
  contradiction = {!≼-stable' (⋆ 0)!}

-- instance
--   RelatingRename-≼ : ∀{tag}
--     {ρ : Ren m n}
--     → ---------------
--     Relating (rename ⦃ r = RenameableExpr {tag = tag} ⦄ ρ) _≼_ _≼_

-- ≼-stable : ∀(r : Term m){R R'}
--   (n≤m : n ≤ m)
--   {S T : expr-of-type tag (m +1)}
--   (S≼T : S ≼ T)
--   (R'≼≽R : R' ≼ R ∨ R ≼ R')
--   → ---------------
--   S [ r ꞉ R / n [ n≤m ]] ≼ T [ r ꞉ R' / n [ n≤m ]]
-- ≼-stable r n≤m (refl≼ _) R'≼≽R = {!!}
-- ≼-stable r n≤m (sort p) _ = sort p
-- ≼-stable {n = n} r {R}{R'} n≤m ([_x:_]→_ π {T = T}{T'} S'≼S T≼T') R'≼≽R =
--   [ π x: ≼-stable r n≤m S'≼S $ ∨-recursion ∨right ∨left R'≼≽R ]→ (
--     proof sub (lift (nthSub n n≤m (r ꞉ R))) T
--       === sub (nthSub (n +1) (ap suc n≤m) (shift (r ꞉ R))) T
--         :by: ap (λ — → sub — T) $ subrel {sup = _==_} $ fun-ext $
--              lift-nth (r ꞉ R) n≤m [: _==_ ]
--       〉 _≼_ 〉 sub (nthSub (n +1) (ap suc n≤m) (shift (r ꞉ R'))) T'
--         :by: ≼-stable (shift r) (ap suc n≤m) T≼T' $
--              [ ap shift ⸴ ap shift ] R'≼≽R
--       === sub (lift (nthSub n n≤m (r ꞉ R'))) T'
--         :by: ap (λ — → sub — T') $ sym $ subrel {sup = _==_} $ fun-ext $
--              lift-nth (r ꞉ R') n≤m
--     qed)
