{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import Basic using (Rig; wfs)
open import PropUniverses

module Substitution.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Substitution.Definition
open import Substitution.Syntax
open import Substitution.Property.CommuteAuxiliary as Comm
open Comm using (sub-newSub) public

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
  module Tag {tag : ExprTag} where
    open WithInstanceArgs ⦃ subst = SubstitutableExpr {tag = tag} ⦄ public
    open Substitutable (SubstitutableExpr {tag = tag}) using (ren) public
open Tag

open import Substitution.Instance
open import Substitution.Basic

rename-[-/new] : ∀{tag}
  (ρ : Ren m n)
  (e : expr-of-type tag (m +1))
  (f : Elim m)
  → --------------------------------------------------------------
  rename ⦃ r = ren ⦄ ρ (e [ f /new])
  ==
  rename (lift ρ) e [ rename ⦃ r = ren ⦄ ρ f /new]
rename-[-/new] ρ e f =
  proof rename ⦃ r = ren ⦄ ρ (e [ f /new])
    === (sub (var ∘ ρ) ∘ sub (newSub f)) e
      :by: subrel {_P_ = _==_} $ ==→~ (rename-as-sub ρ) (e [ f /new]) 
    === sub ((var ∘ ρ) ⍟ newSub f) e
      :by: subrel {_P_ = _==_} $ ==→~ (sub-∘ (var ∘ ρ) (newSub f)) e
    === sub (newSub (sub (var ∘ ρ) f) ⍟ (lift (var ∘ ρ))) e
      :by: ap (λ — → sub — e) $ sub-newSub (var ∘ ρ) f
    === sub (newSub (rename ρ f) ⍟ (var ∘ lift ρ)) e
      :by: ap2 (λ f' ρ' → sub (newSub f' ⍟ ρ') e)
             (subrel {_P_ = _==_} $ (sym $ ==→~ $ rename-as-sub ρ) f)
             (sym {R = _==_} $ lift-var∘ ρ)
    === (sub (newSub (rename ρ f)) ∘ sub (var ∘ lift ρ)) e
      :by: subrel {_P_ = _==_} $ isym $
           ==→~ (sub-∘ (newSub (rename ρ f)) (var ∘ lift ρ)) e
    === rename (lift ρ) e [ rename ρ f /new]
      :by: ap (_[ rename ρ f /new]) $
           subrel {_P_ = _==_} $ isym $
           ==→~ (rename-as-sub (lift ρ)) e
  qed
