{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import Basic using (Rig; wfs)
open import PropUniverses

module Substitution.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Substitution.Definition

open import Proposition.Comparable
open import Data.Nat
open import Relation.Binary hiding (_~_)
open import Function hiding (_$_)
open import Logic
open import Proof

open import Syntax
open import Liftable
open import Renaming

lift-nth :
  (f : Elim m)
  (p : n < m +1)
  → -------------------------------------------------------------
  lift (nthSub n p f) ~ nthSub (n +1) (s<s p) (shift f)
lift-nth f p new = refl (var new)
lift-nth {n = n} f p (old v)
  with compare (index v) _<_ n ⦃ Comparableℕ ⦄
lift-nth f p (old v) | lt _ = refl (var (old (contract v _)))
lift-nth f p (old v) | eq _ = refl (shift f)
lift-nth f p (old (old v)) | gt _ = refl (var (old v))

postulate
  rename-[-/new] :
    (ρ : Ren m n)
    (e : expr-of-type tag (m +1))
    (f : Elim m)
    → --------------------------------------------------------------
    rename ⦃ r = RenameableExpr ⦄ ρ (e [ f /new])
    ==
    rename (lift ρ) e [ rename ⦃ r = RenameableExpr ⦄ ρ f /new]

postulate
  sub-sub :
    (σ' : Sub n k)
    (σ : Sub m n)
    → ----------------------------------
    sub {tag = tag} (σ' ⍟ σ) ~ sub σ' ∘ sub σ

open import Proposition.Identity hiding (refl)
open import Axiom.FunctionExtensionality

postulate
  sub-new-shift :
    (f : Elim m)
    → ------------------------------
    sub (newSub f) ∘ shift ~ 𝑖𝑑 (expr-of-type tag m)
-- sub-new-shift {term} (⋆ i) f = refl (⋆ i)
-- sub-new-shift {term} ([ ρ x: S ]→ T) f = {!!}
-- sub-new-shift {term} (λx, t) f = ap λx,_ {!!}
-- sub-new-shift {term} ⌊ e ⌋ f = {!!}
-- sub-new-shift {elim} (var v) f = refl (var v)
-- sub-new-shift {elim} (f' ` s) f = {!!}
-- sub-new-shift {elim} (s ꞉ S) f = {!!}

⍟-newSub : ∀ (σ : Sub m n) f
  → ---------------------------------------
  σ ⍟ newSub f ~ newSub (sub σ f) ⍟ lift σ
⍟-newSub σ f new = refl (sub σ f)
⍟-newSub σ f (old v) = Id.sym $ sub-new-shift (sub σ f) (σ v)

sub-sub-new :
  (σ : Sub m n)
  (e : expr-of-type tag (m +1))
  (f : Elim m)
  → ------------------------------------------------------
  (sub (lift σ) e) [ sub σ f /new] == sub σ (e [ f /new])
sub-sub-new σ e f =
  proof sub (newSub (sub σ f)) (sub (lift σ) e)
    === sub (newSub (sub σ f) ⍟ lift σ) e
      :by: Id.sym $ sub-sub (newSub (sub σ f)) (lift σ) e
    === sub (σ ⍟ newSub f) e
      :by: ap (λ — → sub — e) $ Id.sym $ fun-ext $ ⍟-newSub σ f
    === sub σ (sub (newSub f) e)
      :by: sub-sub σ (newSub f) e
  qed

-- lift-⍟ :
--   (σ' : Sub n k)
--   (σ : Sub m n)
--   → ----------------------------------
--   lift (σ' ⍟ σ) ~ lift σ' ⍟ lift σ
-- lift-⍟ σ' σ new = Id.refl (default new)
-- lift-⍟ σ' σ (old v) =
--   proof lift (σ' ⍟ σ) (old v)
--     === shift (sub σ' (σ v))
--       :by: Id.refl _
--     === sub (lift σ') (shift (σ v))
--       :by: {!!}
--     === (lift σ' ⍟ lift σ) (old v)
--       :by: Id.refl _
--   qed

-- open import Axiom.FunctionExtensionality

-- sub-sub {tag = term} σ' σ (⋆ i) = Id.refl (⋆ i)
-- sub-sub {tag = term} σ' σ ([ ρ x: S ]→ T) = {!!}
-- sub-sub {tag = term} σ' σ (λx, t) =
--   proof λx, sub (lift (σ' ⍟ σ)) t
--     === λx, sub (lift σ' ⍟ lift σ) t
--       :by: ap (λ — → λx, sub — t) $ fun-ext $ lift-⍟ σ' σ
--     === λx, sub (lift σ') (sub (lift σ) t)
--       :by: ap λx,_ $ sub-sub (lift σ') (lift σ) t
--   qed
-- sub-sub {tag = term} σ' σ ⌊ e ⌋ = {!!}
-- sub-sub {tag = elim} σ' σ (var v) = Id.refl (sub σ' (σ v))
-- sub-sub {tag = elim} σ' σ (f ` s) = {!!}
-- sub-sub {tag = elim} σ' σ (s ꞉ S) = {!!}
    
--     -- sub (newSub (sub σ' f)) (sub (lift σ') e) === sub σ' (sub (newSub f) e)


-- rename-[-/new] {tag = term} ρ (⋆ i) f = refl (⋆ i)
-- rename-[-/new] {tag = term} ρ ([ π x: S ]→ T) f = {!!}
-- rename-[-/new] {tag = term} ρ (λx, t) f =
--   proof rename ρ ((λx, t) [ f /new])
--     === λx, rename (lift ρ) (sub (lift (newSub f)) t)
--       :by: Id.refl _
--     === λx, (sub (lift (newSub (rename ρ f))) (rename (lift (lift ρ)) t))
--       :by: ap λx,_ {!!}
--     === rename (lift ρ) (λx, t) [ rename ρ f /new]
--       :by: Id.refl _
--   qed
-- rename-[-/new] {tag = term} ρ ⌊ e ⌋ f = {!!}
-- rename-[-/new] {tag = elim} ρ (var v) f = {!!}
-- rename-[-/new] {tag = elim} ρ (f' ` s) f = {!!}
-- rename-[-/new] {tag = elim} ρ (s ꞉ S) f = {!!}
