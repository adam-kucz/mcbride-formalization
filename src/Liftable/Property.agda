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

lift-lift-by~ zero σ v = Het.refl (lift σ v)
lift-lift-by~ (k +1) σ new = Het.refl default
lift-lift-by~ (k +1) σ (old v) = Het.refl (shift (lift-by (k +1) σ v))

import Data.Nat.Proof

lift-by-lift~ zero σ v = ap (lift σ) $ sym $ coe-eval (Id-refl _) v
lift-by-lift~ {m = m}{n}(k +1) σ new =
  proof lift-by (k +2) σ new
    === default {m = k + n +1}
      :by: Id-refl _
    het== default {m = k + (n +1)}
      :by: ap (λ — → default {m = —}) $ sym $ +-suc k n
    === lift-by (k +1) (lift σ) (coe coer new)
      :by: ap (lift-by (k +1) (lift σ)) new==new
  qed
  where coer = ap Var $ sym $ +-suc (k +1) m
        new==new : new {n = k + (m +1)} == coe coer new
        new==new = subrel {_R_ = Het._==_} (
          proof new {n = k + (m +1)}
            het== new {n = k + m +1}
              :by: ap (λ — → new {n = —}) $ +-suc k m
            het== coe coer new
              :by: isym $ coe-eval coer new
          qed)
lift-by-lift~ {m = m}{n}(k +1){F} σ (old v) =
  proof lift-by (k +2) σ (old v)
    === shift (lift-by (k +1) σ v)
      :by: Id-refl _
    het== shift (lift-by k (lift σ) (coe (coer k) v))
      :by: Id.ap2 (λ i (e : F i) → shift {m = i} e)
             (sym $ +-suc k n)
             (lift-by-lift~ k σ v)
    === shift (lift-by k (lift σ) v')
      :by: ap (λ — → shift (lift-by k (lift σ) —)) $
           subrel {_R_ = Het._==_}{_P_ = _==_} (
           proof coe (coer k) v
             het== v
               :by: coe-eval (coer k) v
             het== v'
               :by: index==→var==
                      (sym $ +-suc k m)
                      (sym $ index-nth-var (index v) p')
            qed
           )
    === lift-by (k +1) (lift σ) (coe (coer (k +1)) (old v))
      :by: ap (lift-by (k +1) (lift σ)) coe==old
  qed
  where coer : ∀ k → Var (k + m +1) == Var (k + (m +1))
        coer k = ap Var $ sym $ +-suc k m
        p' : index v < k + (m +1)
        v' : Var (k + (m +1))
        v' = nth-var (index v) p'
        p' = proof index v
               〉 _<_ 〉 k + m +1
                 :by: index< v
               〉 _==_ 〉 k + (m +1)
                 :by: sym $ +-suc k m
             qed
        coe==old : old v' == coe (coer (k +1)) (old v)
        coe==old = subrel (
          proof old v'
            het== old v
              :by: Id.ap2 (λ i (v : Var i) → old v)
                     (+-suc k m)
                     (index==→var==
                       (+-suc k m)
                       (index-nth-var (index v) p'))
            het== coe (coer (k +1)) (old v)
              :by: isym $ coe-eval (coer (k +1)) (old v)
          qed)
