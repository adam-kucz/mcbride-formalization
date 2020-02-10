{-# OPTIONS --exact-split --prop #-}
open import Basic
open import Universes

module Liftable.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Liftable.Definition
open import Renaming.Definition
open import Syntax.Definition

open import Type.BinarySum renaming (_+_ to _⊎_)
open import Data.Nat
open import Proposition.Identity hiding (refl)
open import Proposition.Identity.Coercion
open import Function renaming (_$_ to _$'_)
open import Proof
open import Operation.Binary

open import Axiom.FunctionExtensionality

open Selector

lift-by-0~id : ∀ {m n}
  {F : (m : ℕ) → 𝒳 ˙}
  ⦃ lft : Liftable F ⦄
  (σ : Var m → F n)
  → ---------------------
  lift-by 0 σ ~ σ
lift-by-0~id σ v =
  proof lift-by 0 σ v
    === rename id (σ v) :by: Id.refl _
    === σ v             :by: ==→~ rename-id (σ v)
  qed

shift-lift-by~ : ∀ {m n} k
  {F : (m : ℕ) → 𝒳 ˙}
  ⦃ lft : Liftable F ⦄
  (σ : Var m → F n)
  → ----------------------------------------
  shift ∘ lift-by k σ ~ lift (lift-by k σ) ∘ old
lift-lift-by~ : ∀ {m n} k
  {F : (m : ℕ) → 𝒳 ˙}
  ⦃ lft : Liftable F ⦄
  (σ : Var m → F n)
  → ---------------------
  lift (lift-by k σ) ~ lift-by (k +1) σ
lift-by-lift~ : ∀ {m n} k
  {F : (m : ℕ) → 𝒳 ˙}
  ⦃ lft : Liftable F ⦄
  (σ : Var m → F n)
  → ---------------------
  lift-by (k +1) σ
  ~
  lift-by k (lift σ) ∘ coe (ap Var $ sym $ +-suc k m)

shift-lift-by~ zero σ v =
  proof shift (lift-by 0 σ v)
    === shift (σ v)                :by: ap shift $ lift-by-0~id σ v
    === lift σ (old v)             :by: Id.refl _
    === lift (lift-by 0 σ) (old v)
      :by: ap (λ — → lift — (old v)) $ sym $ fun-ext $ lift-by-0~id σ
  qed
shift-lift-by~ {m = m}{n} (k +1) {F} σ v =
  proof shift (lift-by (k +1) σ v)
    === shift (lift-by k (lift σ) v')
      :by: ap2 (λ m (e : F m) → shift e)
               (sym $ +-suc k n)
               (lift-by-lift~ k σ v)
    === lift (lift-by k (lift σ)) (old v')
      :by: shift-lift-by~ k (lift σ) v'
    === shift (lift-by k (lift σ) v')
      :by: Id.refl _
    === shift (lift-by (k +1) σ v)
      :by: ap2 (λ m (e : F m) → shift e)
               (+-suc k n)
               (Id.sym $ lift-by-lift~ k σ v)
    === lift (lift-by (k +1) σ) (old v)
      :by: Id.refl _
  qed
  where v' = coe (ap Var $ sym $ +-suc k m) v

lift-by-lift~ {m = m} zero σ v =
  proof lift σ v
    === lift σ (coe p v)
      :by: ap (lift σ) $ sym $ coe-eval p v
    === lift-by 0 (lift σ) (coe p v)
      :by: sym $ lift-by-0~id (lift σ) (coe p v)
  qed
  where p = ap Var $ sym $ +-suc 0 m
lift-by-lift~ {m = m} (k +1) σ new =
  proof lift-by (k +2) σ new
    === default new
      :by: Id.refl _
    === lift-by (k +1) (lift σ) (coe p new)
      :by: {!!}
  qed
  where p  = ap Var $ sym $ +-suc (k +1) m
        p' = ap Var $ sym $ +-suc k (m +1)
lift-by-lift~ {m = m} (k +1) σ (old v) = {!!}
  -- proof lift-by (k +2) σ v
  --   === [ rename (old ∘ old ∘ old× k) ∘ σ , id ] (without k +2 new v)
  --     :by: Id.refl _
  --   === lift-by (k +1) (lift σ) (coe p v)
  --     :by: {!!}
  -- qed
  -- where p = ap Var $ sym $ +-suc (k +1) m
