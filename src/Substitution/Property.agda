{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import Basic using (Rig; wfs)
open import PropUniverses

module Substitution.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Substitution.Definition
open import Substitution.Property.CommuteAuxiliary

open import Proposition.Comparable
open import Data.Nat hiding (l)
open import Relation.Binary hiding (_~_)
open import Function hiding (_$_)
open import Logic
open import Proof

open import Syntax ⦃ rig ⦄ ⦃ wfs ⦄
open import Liftable
open import Renaming

open import Proposition.Identity.Coercion
open import Axiom.FunctionExtensionality

private
  lift-var∘ : (ρ : Ren m n) →
    var ∘ lift ρ == lift (var ∘ ρ)

lift-var∘ ρ = subrel {_P_ = _==_} $ fun-ext λ
  { new → Het.refl (var new)
  ; (old v) → Het.refl (var (old (ρ v)))}

rename-as-sub : 
  (ρ : Ren m n)
  (e : expr-of-type tag m)
  → --------------------------------------------------------------
  rename ⦃ r = RenameableExpr ⦄ ρ e == sub (var ∘ ρ) e
rename-as-sub {tag = term} ρ (⋆ i) = Id-refl (⋆ i)
rename-as-sub {tag = term} ρ ([ π x: S ]→ T) =
  ap2 [ π x:_]→_ (rename-as-sub ρ S) (
    proof rename (lift ρ) T
      === sub (var ∘ lift ρ) T
        :by: rename-as-sub (lift ρ) T
      === sub (lift (var ∘ ρ)) T
        :by: ap (λ — → sub — T) $ lift-var∘ ρ
    qed)
rename-as-sub {tag = term} ρ (λx, t) = ap λx,_ (
  proof rename (lift ρ) t
    === sub (var ∘ lift ρ) t
      :by: rename-as-sub (lift ρ) t
    === sub (lift (var ∘ ρ)) t
      :by: ap (λ — → sub — t) $ lift-var∘ ρ
  qed)
rename-as-sub {tag = term} ρ ⌊ e ⌋ = ap ⌊_⌋ $ rename-as-sub ρ e
rename-as-sub {tag = elim} ρ (var v) = Id-refl (var (ρ v))
rename-as-sub {tag = elim} ρ (f ` s) =
  ap2 _`_ (rename-as-sub ρ f) (rename-as-sub ρ s)
rename-as-sub {tag = elim} ρ (s ꞉ S) =
  ap2 _꞉_ (rename-as-sub ρ s) (rename-as-sub ρ S)

-- sub-newSub:
-- sub σ ∘ newSub f == sub (newSub (sub σ f)) ∘ (sub (var ∘ old) σ)
-- apply to e:
-- sub σ (sub (newSub f) e) == sub (newSub (sub σ f)) (sub (sub (var ∘ old) σ) e)
-- by sub-comm-hyp:
-- sub σ (sub (newSub f) e) == sub (sub σ (newSub f)) (sub σ e)

-- -- intuitively: 
-- sub σ' ∘ sub σ == sub (sub σ' σ)

-- applying to sub-newSub:
-- sub σ (sub (newSub f) e) == sub (sub σ (newSub f)) e
-- remains:
-- sub σ (newSub f) == sub (newSub (sub σ f)) ∘ lift σ
-- checks out ✓

-- applying to lift-⍟:
-- sub (var ∘ old) (sub σ' e) == sub (lift σ') (sub (var ∘ old) e)
-- we get:
-- sub (var ∘ old) (sub σ' e) == sub (sub (var ∘ old) σ') e
-- sub (lift σ') (sub (var ∘ old) e) == sub (sub σ' (var ∘ old)) e
-- remains:
-- sub (var ∘ old) σ'
-- =?=
-- sub σ' (var ∘ old)
-- false

-- seems false:
-- sub (sub ρ σ') (sub ρ e)
-- =?=
-- sub ρ (sub σ' e)

lift-⍟ :
  (σ' : Sub n k)
  (σ : Sub m n)
  → --------------------
  lift (σ' ⍟ σ) == lift σ' ⍟ lift σ
lift-⍟ σ' σ = subrel {_P_ = _==_} $ fun-ext λ
  { new → Het.refl default
  ; (old v) →
    proof lift (σ' ⍟ σ) (old v)
      === shift (sub σ' (σ v))
        :by: Id-refl _
      === sub (var ∘ old) (sub σ' (σ v))
        :by: Id-refl _
      het== sub (lift σ') (sub (var ∘ old) (σ v))
        :by: {!!}
      === sub (lift σ') (shift (σ v))
        :by: rename-as-sub
      === (lift σ' ⍟ lift σ) (old v)
        :by: Id-refl _
    qed}

sub-sub :
  (σ' : Sub n k)
  (σ : Sub m n)
  → ----------------------------------------
  sub {tag = tag} (σ' ⍟ σ) ~ sub σ' ∘ sub σ
sub-sub {tag = term} σ' σ (⋆ i) = Het.refl (⋆ i)
sub-sub {tag = term} σ' σ ([ π x: S ]→ T) =
  ap2 [ π x:_]→_ (sub-sub σ' σ S) (
    proof sub (lift (σ' ⍟ σ)) T
      === sub (lift σ' ⍟ lift σ) T
        :by: ap (λ — → sub — T) $ lift-⍟ σ' σ
      het== sub (lift σ') (sub (lift σ) T)
        :by: sub-sub (lift σ') (lift σ) T
    qed)
sub-sub {tag = term} σ' σ (λx, t) = ap λx,_ (
  proof sub (lift (σ' ⍟ σ)) t
    === sub (lift σ' ⍟ lift σ) t
      :by: ap (λ — → sub — t) $ lift-⍟ σ' σ
    het== sub (lift σ') (sub (lift σ) t)
      :by: sub-sub (lift σ') (lift σ) t
  qed)
sub-sub {tag = term} σ' σ ⌊ e ⌋ = ap ⌊_⌋ $ sub-sub σ' σ e
sub-sub {tag = elim} σ' σ (var v) = Het.refl (sub σ' (σ v))
sub-sub {tag = elim} σ' σ (f ` s) = ap2 _`_ (sub-sub σ' σ f) (sub-sub σ' σ s)
sub-sub {tag = elim} σ' σ (s ꞉ S) = ap2 _꞉_ (sub-sub σ' σ s) (sub-sub σ' σ S)


rename-[-/new] :
  (ρ : Ren m n)
  (e : expr-of-type tag (m +1))
  (f : Elim m)
  → --------------------------------------------------------------
  rename ⦃ r = RenameableExpr ⦄ ρ (e [ f /new])
  ==
  rename (lift ρ) e [ rename ⦃ r = RenameableExpr ⦄ ρ f /new]
rename-[-/new] ρ e f =
  proof rename ρ (e [ f /new])
    === (sub (var ∘ ρ) ∘ sub (newSub f)) e
      :by: rename-as-sub ρ (e [ f /new]) 
    === sub ((var ∘ ρ) ⍟ newSub f) e
      :by: subrel {_P_ = _==_} $ isym $ sub-sub (var ∘ ρ) (newSub f) e
    === sub (newSub (sub (var ∘ ρ) f) ⍟ (lift (var ∘ ρ))) e
      :by: ap (λ — → sub — e) $ sub-newSub (var ∘ ρ) f
    === sub (newSub (rename ρ f) ⍟ (var ∘ lift ρ)) e
      :by: ap2 (λ f' ρ' → sub (newSub f' ⍟ ρ') e)
             (sym {R = _==_} $ rename-as-sub ρ f)
             (sym {R = _==_} $ lift-var∘ ρ)
    === (sub (newSub (rename ρ f)) ∘ sub (var ∘ lift ρ)) e
      :by: subrel {_P_ = _==_} $ sub-sub (newSub (rename ρ f)) (var ∘ lift ρ) e
    === rename (lift ρ) e [ rename ρ f /new]
      :by: ap (_[ rename ρ f /new]) $ sym {R = _==_} $
           rename-as-sub (lift ρ) e
  qed
