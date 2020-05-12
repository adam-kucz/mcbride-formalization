{-# OPTIONS --exact-split --prop #-}
open import Basic
open import Universes

module Liftable.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Liftable.Definition
open import Renaming.Definition ⦃ rig ⦄ ⦃ wfs ⦄
open import Syntax.Definition

open import Type.BinarySum renaming (_+_ to _⊎_)
open import Data.Nat
open import Proposition.Identity hiding (refl)
open import Proposition.Identity.Coercion
open import Function renaming (_$_ to _$'_)
open import Proof
open import Relation.Binary hiding (_~_)
open import Operation.Binary

open import Axiom.FunctionExtensionality

open Selector

lift-by-0~id : ∀ {m n}
  {F : (m : ℕ) → 𝒳 ˙}
  ⦃ lft : Liftable F ⦄
  (σ : Var m → F n)
  → ---------------------
  lift-by 0 σ ~ σ
lift-by-0~id σ v = subrel (
  proof lift-by 0 σ v
    === rename id (σ v) :by: Id-refl _
    === σ v             :by: subrel $ ==→~ rename-id (σ v)
  qed)

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

open import Logic

shift-lift-by~ zero σ v = subrel (
  proof shift (lift-by 0 σ v)
    === shift (σ v)                :by: subrel $ ap shift $ lift-by-0~id σ v
    === lift σ (old v)             :by: Id-refl _
    === lift (lift-by 0 σ) (old v)
      :by: ap (λ — → lift — (old v)) $
           sym $ subrel $ fun-ext $ lift-by-0~id σ
  qed)
shift-lift-by~ {m = m}{n} (k +1) {F} σ v =
  proof shift (lift-by (k +1) σ v)
    〉 Het._==_ 〉 shift (lift-by k (lift σ) v')
      :by: Id.ap2 (λ m (e : F m) → shift e)
             (sym $ +-suc k n)
             (lift-by-lift~ k σ v)
    〉 Het._==_ 〉 lift (lift-by k (lift σ)) (old v')
      :by: shift-lift-by~ k (lift σ) v'
    〉 Het._==_ 〉 shift (lift-by k (lift σ) v')
      :by: Het.refl _
    〉 Het._==_ 〉 shift (lift-by (k +1) σ v)
      :by: Id.ap2 (λ m (e : F m) → shift e)
             (+-suc k n)
             (isym $ lift-by-lift~ k σ v)
    〉 Het._==_ 〉 lift (lift-by (k +1) σ) (old v)
      :by: Het.refl _
  qed
  where v' = coe (ap Var $ sym $ +-suc k m) v

lift-lift-by~ 0 σ v =
  ap (λ — → lift — v) $ fun-ext $ lift-by-0~id σ 
lift-lift-by~ (k +1) σ new = Het.refl _
lift-lift-by~ {m = m}(k +1) σ (old v) =
  proof  lift (lift-by (k +1) σ) (old v)
    het== shift (lift-by (k +1) σ v)
      :by: sym $ shift-lift-by~ (k +1) σ v
    === shift ([ rename (old× (k +1)) ∘ σ , id ] (without k +1 new v))
      :by: Id-refl _
    het== [ shift ∘ rename (old× (k +1)) ∘ σ , shift ] (without k +1 new v)
      :by: (shift ∘[ rename (old× (k +1)) ∘ σ , id ]) (without k +1 new v)
    === [ rename (old ∘ old× (k +1)) ∘ σ , shift ] (without k +1 new v)
      :by: ap (λ — → [ — ∘ σ , shift ] (without k +1 new v)) $
           sym $ rename-∘ old (old× (k +1))
    === [ rename (old× (k +2)) ∘ σ ∘ id , id ∘ shift ] (without k +1 new v)
      :by: Id-refl _
    het== ([ rename (old× (k +2)) ∘ σ , id ] ∘ [ id + shift ]) (without k +1 new v)
      :by: sym $ [ rename (old× (k +2)) ∘ σ , id ]∘[ id + shift ] (without k +1 new v)
    === [ rename (old× (k +2)) ∘ σ , id ] (without k +2 new (old v))
      :by: Id-refl _
    === lift-by (k +2) σ (old v)
      :by: Id-refl _
  qed

lift-by-lift~ {m = m} 0 σ v =
  proof lift-by 1 σ v
    het== lift-by 1 σ (coe coercion v)
      :by: ap (lift-by 1 σ) $ sym $ coe-eval coercion v
    het== lift-by 0 (lift σ) (coe coercion v)
      :by: sym $ lift-by-0~id (lift σ) (coe coercion v)
  qed
  where coercion : Var (m +1) == Var (m +1)
        coercion = Id-refl (Var (m +1))
lift-by-lift~ {m = m}{n} (k +1) σ new =
  proof lift-by (k +2) σ new
    === [ rename (old× (k +2)) ∘ σ , id ] (without k +2 new Var.new)
      :by: Id-refl _
    === default new
      :by: Id-refl _
    het== [ rename (old× (k +1)) ∘ lift σ , id ] (without (k +1) new Var.new)
      :by: ap (λ — → extend-by-right — default-new) $ sym $ +-suc k n
    === lift-by (k +1) (lift σ) Var.new
      :by: Id-refl _
    === lift-by (k +1) (lift σ) (coe coercion Var.new)
      :by: ap (lift-by (k +1) (lift σ)) $ subrel new==new
  qed
  where coercion : Var (k + m +2) == Var (k +1 + (m +1))
        coercion = ap Var $ sym $ +-suc (k +1) m
        new==new : Var.new {n = k + (m +1)} Het.== coe coercion Var.new
        new==new =
          proof Var.new {n = k + (m +1)}
            het== Var.new {n = k + m +1}
              :by: ap (λ — → new {n = —}) $ +-suc k m
            het== coe coercion Var.new
              :by: isym $ coe-eval coercion Var.new
          qed
lift-by-lift~ {m = m}{n} (k +1) {F} σ (old v) =
  proof lift-by (k +2) σ (old v)
    het== lift (lift-by (k +1) σ) (old v)
      :by: sym $ lift-lift-by~ (k +1) σ (old v)
    === shift (lift-by (k +1) σ v)
      :by: Id-refl _
    het== shift (lift-by k (lift σ) (coe (coercion k) v))
      :by: Id.ap2 (λ i (arg : F i) → shift arg)
             (sym $ +-suc k n)
             (lift-by-lift~ k σ v)
    === lift (lift-by k (lift σ)) (old (coe (coercion k) v))
      :by: Id-refl _
    het== lift-by (k +1) (lift σ) (old (coe (coercion k) v))
      :by: lift-lift-by~ k (lift σ) (old (coe (coercion k) v)) 
    === lift-by (k +1) (lift σ) (coe (coercion (k +1)) (old v))
      :by: ap (lift-by (k +1) (lift σ)) old==old
  qed
  where coercion : ∀ k → Var (k + m +1) == Var (k + (m +1))
        coercion k = ap Var $ sym $ +-suc k m
        old==old : old (coe (coercion k) v) == coe (coercion (k +1)) (old v)
        old==old = subrel (
          proof old (coe (coercion k) v)
            het== old v
              :by: Id.ap2 (λ i v → old {n = i} v)
                     (+-suc k m)
                     (coe-eval (coercion k) v)
            het== coe (coercion (k +1)) (old v)
              :by: isym $ coe-eval (coercion (k +1)) (old v)
          qed)
