{-# OPTIONS --exact-split #-} -- TODO: add --safe, problem: Syntax.Property
open import Basic using (Rig; wfs)
open import Universes

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
open import Function.Proof

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

open import Relation.Binary.Pointwise

instance
  Relating-newSub-refl :
    {Rel : BinRel 𝒳 (Elim n)}
    ⦃ refl-Rel : Reflexive Rel ⦄
    → ---------------------------------------------
    Relating (newSub {n = n}) Rel (Pointwise Rel)
rel-preserv ⦃ Relating-newSub-refl ⦄ a▷b new = a▷b
rel-preserv ⦃ Relating-newSub-refl ⦄ _ (old x) = refl (var x)

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

open import Type.BinarySum renaming (_+_ to _⊹_)

[_+id]∘aux-nthSub : (f : X → Y)(x : X)(q : n ≤ m)
  → -----------------------------------------------------
  [ f + id ] ∘ aux-nthSub x n q ~ aux-nthSub (f x) n q
[_+id]∘aux-nthSub {n = zero}{m} f x q new = Het.refl (inl (f x))
[_+id]∘aux-nthSub {n = zero}{m} f x q (old v) = Het.refl (inr (var v))
[_+id]∘aux-nthSub {n = n +1}{m +1} f x q new = Het.refl (inr (var new))
[_+id]∘aux-nthSub {n = n +1}{m +1} f x q (old v) =
  proof [ f + id ] ([ id + shift ] n')
    het== [ f + shift ] n'
      :by: [ f + id ]∘[ id + shift ] n'
    het== [ id + shift ] ([ f + id ] n')
      :by: sym {R = Het._==_} $ [ id + shift ]∘[ f + id ] n'
    het== [ id + shift ] (aux-nthSub (f x) n (ap pred q) v)
      :by: ap [ id + shift ] $ [ f +id]∘aux-nthSub x (ap pred q) v
  qed
  where n' = aux-nthSub x n (ap pred q) v

private
  aux-lift-nth : ∀ (f : Elim m) n (q : n ≤ m)(x : Var (m +1))
    → --------------------------------------------------------
    shift ([ id , id ] (aux-nthSub f n q x))
    Het.==
    [ id , id ] (aux-nthSub (shift f) (n +1) (ap suc q) (old x))
aux-lift-nth f n q x =
  proof shift' ([ id , id ] x')
    het== [ shift' , shift' ] x'
      :by: (shift' ∘[ id , id ]) x'
    het== [ id , shift' ] ([ shift' + id ] x')
      :by: isym $ [ id , shift' ]∘[ shift' + id ] x'
    het== [ id , shift' ] x″
      :by: ap [ id , shift' ] $ [ shift' +id]∘aux-nthSub f q x
    het== [ id , id ] ([ id + shift' ] x″)
      :by: isym $ [ id , id ]∘[ id + shift' ] x″
  qed
  where x' = aux-nthSub f n q x
        x″ = aux-nthSub (shift f) n q x
        shift' = shift ⦃ ren = RenameableExpr ⦄


lift-nth : (f : Elim m)(q : n ≤ m)
  → -----------------------------------------------------
  lift (nthSub n q f) ~ nthSub (n +1) (ap suc q) (shift f)
lift-nth {m} {zero} f q new = Het.refl (var new)
lift-nth {m} {zero} f q (old x) = aux-lift-nth f 0 q x
lift-nth {m} {n +1} f q new = Het.refl (var new)
lift-nth {m} {n +1} f q (old x) = aux-lift-nth f (n +1) q x
