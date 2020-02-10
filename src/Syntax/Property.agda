{-# OPTIONS --exact-split --prop #-}
open import Basic using (Rig; wfs)
open import PropUniverses

module Syntax.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax.Definition

open import Renaming.Definition
open import Liftable.Definition

open import Axiom.FunctionExtensionality
open import Proof

instance
  RenameableVar : Renameable Var
  LiftableVar : Liftable Var

rename ⦃ RenameableVar ⦄ ρ v = ρ v
rename-id ⦃ RenameableVar ⦄ = fun-ext λ v → Id.refl v
rename-∘ ⦃ RenameableVar ⦄ π ρ = fun-ext λ v → Id.refl (π (ρ v))

default-new ⦃ LiftableVar ⦄ = new

open import Function hiding (_$_)
open import Data.Nat

lift-id==id : ∀ {m} → lift (𝑖𝑑 (Var m))  == 𝑖𝑑 (Var (m +1))
lift-id==id {m} = fun-ext λ
  { new → Id.refl new
  ; (old v) → Id.refl (old v) }

lift-∘ :  ∀ {m n k}
  (π : Ren n k)
  (ρ : Ren m n)
  → ------------------------------------
  lift (π ∘ ρ) == lift π ∘ lift ρ
lift-∘ π ρ = fun-ext λ
  { new → Id.refl new
  ; (old v) → Id.refl (old (π (ρ v))) }

private
  renTerm : ∀ {m n} (ρ : Ren m n) (x : Term m) → Term n
  renElim : ∀ {m n} (ρ : Ren m n) (x : Elim m) → Elim n

renTerm ρ (⋆ i) = ⋆ i
renTerm ρ ([ π x: S ]→ T) = [ π x: renTerm ρ S ]→ renTerm (lift ρ) T
renTerm ρ (λx, t) = λx, renTerm (lift ρ) t
renTerm ρ ⌊ e ⌋ = ⌊ renElim ρ e ⌋

renElim ρ (var v) = var (rename ρ v)
renElim ρ (f ` s) = renElim ρ f ` renTerm ρ s
renElim ρ (s ꞉ S) = renTerm ρ s ꞉ renTerm ρ S

open import Proposition.Identity hiding (refl)

private
  renTerm-id~id : ∀ {m} → renTerm (𝑖𝑑 (Var m)) ~ id
  renElim-id~id : ∀ {m} → renElim (𝑖𝑑 (Var m)) ~ id

renTerm-id~id (⋆ i) = Id.refl (⋆ i)
renTerm-id~id ([ ρ x: S ]→ T) = Id.ap2 ([ ρ x:_]→_) (renTerm-id~id S) (
  proof renTerm (lift id) T
    === renTerm id T        :by: ap (λ — → renTerm — T) lift-id==id
    === T                   :by: renTerm-id~id T
  qed)
renTerm-id~id (λx, t) = ap λx,_ (
  proof renTerm (lift id) t 
    === renTerm id t        :by: ap (λ — → renTerm — t) lift-id==id
    === t                   :by: renTerm-id~id t
  qed)
renTerm-id~id ⌊ e ⌋ = ap ⌊_⌋ $ renElim-id~id e

renElim-id~id (var v) = refl (var v)
renElim-id~id (f ` s) = Id.ap2 _`_ (renElim-id~id f) (renTerm-id~id s)
renElim-id~id (s ꞉ S) = Id.ap2 _꞉_ (renTerm-id~id s) (renTerm-id~id S)

renTerm-∘ : ∀ {m n k}
    (π : Ren n k)
    (ρ : Ren m n)
    → ------------------------------------
    renTerm (π ∘ ρ) ~ renTerm π ∘ renTerm ρ
renElim-∘ : ∀ {m n k}
    (π : Ren n k)
    (ρ : Ren m n)
    → ------------------------------------
    renElim (π ∘ ρ) ~ renElim π ∘ renElim ρ

renTerm-∘ π ρ (⋆ i) = refl (⋆ i)
renTerm-∘ π ρ ([ ν x: S ]→ T) = Id.ap2 [ ν x:_]→_ (renTerm-∘ π ρ S) (
  proof renTerm (lift (π ∘ ρ)) T
    === renTerm (lift π ∘ lift ρ) T
      :by: ap (λ — → renTerm — T) (lift-∘ π ρ)
    === renTerm (lift π) (renTerm (lift ρ) T)
      :by: renTerm-∘ (lift π) (lift ρ) T
  qed)
renTerm-∘ π ρ (λx, t) = ap λx,_ (
  proof renTerm (lift (π ∘ ρ)) t
    === renTerm (lift π ∘ lift ρ) t
      :by: ap (λ — → renTerm — t) (lift-∘ π ρ)
    === renTerm (lift π) (renTerm (lift ρ) t)
      :by: renTerm-∘ (lift π) (lift ρ) t
  qed)
renTerm-∘ π ρ ⌊ e ⌋ = ap ⌊_⌋ (renElim-∘ π ρ e)

renElim-∘ π ρ (var v) = Id.refl (var (π (ρ v)))
renElim-∘ π ρ (f ` s) = Id.ap2 _`_ (renElim-∘ π ρ f) (renTerm-∘ π ρ s)
renElim-∘ π ρ (s ꞉ S) = Id.ap2 _꞉_ (renTerm-∘ π ρ s) (renTerm-∘ π ρ S)

RenameableTerm : Renameable Term
rename ⦃ RenameableTerm ⦄ = renTerm
rename-id ⦃ RenameableTerm ⦄ = fun-ext renTerm-id~id
rename-∘ ⦃ RenameableTerm ⦄ π ρ = fun-ext (renTerm-∘ π ρ)

RenameableElim : Renameable Elim
rename ⦃ RenameableElim ⦄ = renElim
rename-id ⦃ RenameableElim ⦄ = fun-ext renElim-id~id
rename-∘ ⦃ RenameableElim ⦄ π ρ = fun-ext (renElim-∘ π ρ)

instance
  RenameableExpr : ∀ {tag} → Renameable (expr-of-type tag)

RenameableExpr {term} = RenameableTerm
RenameableExpr {elim} = RenameableElim

instance
  LiftableElim : Liftable Elim

default-new ⦃ LiftableElim ⦄ = var new
