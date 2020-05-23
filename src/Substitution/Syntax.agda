{-# OPTIONS --exact-split --prop #-}
open import Basic using (Rig; wfs)
open import PropUniverses

module Substitution.Syntax
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Substitution.Definition
open import Syntax

open import Data.Nat

instance
  SubstitutableElim : Substitutable Elim
  SubstitutableTerm : Substitutable Term

open import Substitution.Basic

open import Function hiding (_$_)
open import Proof

open import Axiom.FunctionExtensionality

private
  subElim-var~id : subElim {m = m} var ~ id
  subTerm-var~id : subTerm {m = m} var ~ id

subElim-var~id (var v) = Het.refl (var v)
subElim-var~id (f ` s) = ap2 _`_ (subElim-var~id f) (subTerm-var~id s)
subElim-var~id (s ꞉ S) = ap2 _꞉_ (subTerm-var~id s) (subTerm-var~id S)

open import Liftable

lift-var : lift {m = m} var == var
lift-var = subrel {_P_ = _==_} $ fun-ext λ
  { new → Het.refl (var new)
  ; (old v) → Het.refl (var (old v))}

subTerm-var~id (⋆ i) = Het.refl (⋆ i)
subTerm-var~id ([ π x: S ]→ T) = ap2 [ π x:_]→_ (subTerm-var~id S) (
  proof subTerm (lift var) T
    === subTerm var T
      :by: ap (λ — → subTerm — T) lift-var
    het== T
      :by: subTerm-var~id T
  qed)
subTerm-var~id (λx, t) = ap λx,_ (
  proof subTerm (lift var) t
    === subTerm var t
      :by: ap (λ — → subTerm — t) lift-var
    het== t
      :by: subTerm-var~id t
  qed)
subTerm-var~id ⌊ e ⌋ = ap ⌊_⌋ $ subElim-var~id e

private
  subElim-⍟~id :
    (σ : Sub n k)
    (τ : Sub m n)
    → ---------------------------------------
    subElim σ ∘ subElim τ ~ subElim (σ ⍟ τ)
  subTerm-⍟~id :
    (σ : Sub n k)
    (τ : Sub m n)
    → ---------------------------------------
    subTerm σ ∘ subTerm τ ~ subTerm (σ ⍟ τ)

open import Renaming

open import Proposition.Identity.Coercion
-- open import Proposition.Proof

private
  renElim = rename ⦃ r = RenameableElim ⦄
  renTerm = rename ⦃ r = RenameableTerm ⦄
  rene = λ k {m} → renElim (lift-by {m = m} k old)
  rent = λ k {m} → renTerm (lift-by {m = m} k old)
  renv = λ k {m} → lift-by {m = m} k old

lift-shift : ∀
  (σ : Sub m n)
  (k : ℕ)
  → ---------------------------------------------------
  lift-by (k +1) σ ∘ shift ~ shift ∘ lift-by k σ
lift-shift σ zero new = Het.refl _
lift-shift σ zero (old v) = Het.refl _
lift-shift σ (k +1) new = Het.refl _
lift-shift σ (k +1) (old v) = Het.refl _

old-lift : ∀ k {m}
  → --------------------------------------------------
  old ∘ lift-by {m = m} k old == lift-by (k +1) old ∘ old
old-lift zero = Id-refl _
old-lift (k +1) = subrel $ fun-ext λ
  { new → Het.refl _
  ; (old v) → Het.refl _}

lift-⍟-aux-Elim : (k : ℕ){m n : ℕ}
  (σ : Sub m n)
  (e : Elim (k + m))
  → ---------------------------------------------------
  let e' : Elim (k + m +1)
      e' = coe (ap Elim $ +-suc k m) (rene k e) in
  subElim (lift-by (k +1) σ) e'
  Het.==
  rene k (subElim (lift-by k σ) e)
lift-⍟-aux-Term :
  (σ : Sub m n)
  (k : ℕ)
  (e : Term (k + m))
  → ---------------------------------------------------
  subTerm (lift-by (k +1) σ) (rename (lift-by k old) e)
  ==
  rename (lift-by k old) (subTerm (lift-by k σ) e)

lift-⍟-aux-Elim k {m}{n} σ (var v) = {!!}
{-  proof subElim (lift-by (k +1) σ) (coe coer (rene k (var v)))
    === subElim (lift-by (k +1) σ) (var v')
      :by: ap (subElim (lift-by (k +1) σ)) move-coe
    het== rene k (lift-by k σ v)
      :by: aux k v
    === rene k (subElim (lift-by k σ) (var v))
      :by: Id-refl _
  qed
  where coer = ap Elim $ +-suc k m
        v' = coe (ap Var $ +-suc k m) (renv k v)
        move-coe = subrel {_P_ = _==_} (
          proof coe coer (rene k (var v))
            het== rene k (var v)
              :by: coe-eval coer (rene k (var v))
            === var (renv k v)
              :by: Id-refl _
            het== var v'
              :by: Id.ap2 (λ i (v : Var i) → var v)
                     (+-suc k m)
                     (isym $ coe-eval (ap Var $ +-suc k m) (renv k v))
          qed)
        aux : ∀ k v →
          lift-by (k +1) σ (coe (ap Var $ +-suc k m) (renv k v))
          Het.==
          rene k (lift-by k σ v)
        aux zero v = ap (lift σ) $ coe-eval (Id-refl _) (old v)
        aux (k +1) new =
          proof lift-by (k +2) σ (
                  coe (ap Var $ +-suc (k +1) m) (renv (k +1) new))
            === lift-by (k +2) σ (coe (ap Var $ +-suc (k +1) m) new)
              :by: Id-refl _
            het== var (new {n = k + n +1})
              :by: ap (lift-by (k +2) σ) move-coe'
            het== var (new {n = k + (n +1)})
              :by: ap (λ i → var (new {n = i})) $ sym $ +-suc k n
            === rene (k +1) (lift-by (k +1) σ new)
              :by: Id-refl _
          qed
          where move-coe' = 
                  proof coe (ap Var $ +-suc (k +1) m) new
                    het== new {n = k + (m +1)}
                      :by: coe-eval (ap Var $ +-suc (k +1) m) new
                    het== new {n = k + m +1}
                      :by: ap (λ i → new {n = i}) $ +-suc k m
                  qed
        aux (k +1) (old v) = 
          proof lift-by (k +2) σ (
                  coe (ap Var $ +-suc (k +1) m) (shift (renv k v)))
            het== lift-by (k +2) σ (shift v″)
              :by: ap (lift-by (k +2) σ) move-coe'
            het== shift (lift-by (k +1) σ v″)
              :by: lift-shift σ (k +1) v″
            het== shift (rene k (lift-by k σ v))
              :by: Id.ap2 (λ i (e : Elim i) → shift e)
                     (sym $ +-suc k n)
                     (aux k v)
            === renElim (old ∘ lift-by k old) (lift-by k σ v)
              :by: ap (λ — → — (lift-by k σ v)) $ sym {R = _==_} $
                   rename-∘ ⦃ r = RenameableElim ⦄ old (lift-by k old)
            === renElim (lift-by (k +1) old ∘ old) (lift-by k σ v)
              :by: ap (λ — → renElim — (lift-by k σ v)) $ old-lift k
            === rene (k +1) (shift (lift-by k σ v))
              :by: ap (λ — → — (lift-by k σ v)) $
                   rename-∘ ⦃ r = RenameableElim ⦄ (lift-by (k +1) old) old
          qed
          where v″ = coe (ap Var $ +-suc k m) (renv k v)
                move-coe' =
                  proof coe (ap Var $ +-suc (k +1) m) (shift (renv k v))
                    het== shift (renv k v)
                      :by: coe-eval (ap Var $ +-suc (k +1) m) (shift (renv k v))
                    het== shift (coe (ap Var $ +-suc k m) (renv k v))
                      :by: Id.ap2 (λ i (v : Var i) → shift v)
                             (+-suc k m)
                             (isym $ coe-eval (ap Var $ +-suc k m) (renv k v))
                  qed
-}
lift-⍟-aux-Elim k {m} σ (f ` s) =
  proof subElim (lift-by (k +1) σ) (coe (ap Elim $ +-suc k m) (rene k f ` rent k s))
    het== subElim (lift-by (k +1) σ) (coe (ap Elim $ +-suc k m) (rene k f)) `
          subTerm (lift-by (k +1) σ) (coe (ap Term $ +-suc k m) (rent k s))
      :by: {!!}
    het== rene k (subElim (lift-by k σ) f) ` rent k (subTerm (lift-by k σ) s)
      :by: {!!}
  qed
  where move-coe :
          coe (ap Elim $ +-suc k m) (rene k f ` rent k s)
          ==
          coe (ap Elim $ +-suc k m) (rene k f) `
          coe (ap Term $ +-suc k m) (rent k s)
        move-coe = subrel {_P_ = _==_} (
          proof coe (ap Elim $ +-suc k m) (rene k f ` rent k s)
            het== rene k f ` rent k s
              :by: coe-eval (ap Elim $ +-suc k m) (rene k f ` rent k s)
            het== coe (ap Elim $ +-suc k m) (rene k f) `
                  coe (ap Term $ +-suc k m) (rent k s)
              :by: Het.ap3 (λ i (f : Elim i)(s : Term i) → f ` s) ? ? ?
          qed)
lift-⍟-aux-Elim k σ (s ꞉ S) = {!!}

{-
lift-⍟-aux-Elim σ k (var v) = {!!} -- Id-refl (shift (σ v)) 
lift-⍟-aux-Elim σ k (f ` s) =
  ap2 _`_ (lift-⍟-aux-Elim σ k f) (lift-⍟-aux-Term σ k s)
lift-⍟-aux-Elim σ k (s ꞉ S) =
  ap2 _꞉_ (lift-⍟-aux-Term σ k s) (lift-⍟-aux-Term σ k S)

lift-⍟-aux-Term σ k (⋆ i) = Id-refl (⋆ i)
lift-⍟-aux-Term σ k ([ π x: S ]→ T) = {!!}
lift-⍟-aux-Term σ k (λx, t) = ap λx,_ (
  proof {!!}
    === {!!}
      :by: {!!}
  qed)
lift-⍟-aux-Term σ k ⌊ e ⌋ = ap ⌊_⌋ $ lift-⍟-aux-Elim σ k e

lift-⍟ :
  (σ : Sub n k)
  (τ : Sub m n)
  → ---------------------------------------
  lift σ ⍟ lift τ == lift (σ ⍟ τ)
lift-⍟ σ τ = subrel {_P_ = _==_} $ fun-ext λ
  { new → Het.refl (var new)
  ; (old v) →
    proof (lift σ ⍟ lift τ) (old v)
      === subElim (lift σ) (shift (τ v))
        :by: Id-refl _
      het== shift (subElim σ (τ v))
        :by: {!subElim σ!}
      === lift (σ ⍟ τ) (old v)
        :by: Id-refl _
    qed}

subElim-⍟~id σ τ (var v) = Het.refl ((σ ⍟ τ) v)
subElim-⍟~id σ τ (f ` s) =
  ap2 _`_ (subElim-⍟~id σ τ f) (subTerm-⍟~id σ τ s)
subElim-⍟~id σ τ (s ꞉ S) =
  ap2 _꞉_ (subTerm-⍟~id σ τ s) (subTerm-⍟~id σ τ S)

subTerm-⍟~id σ τ (⋆ i) = Het.refl (⋆ i)
subTerm-⍟~id σ τ ([ π x: S ]→ T) =  ap2 [ π x:_]→_ (subTerm-⍟~id σ τ S) (
  proof subTerm (lift σ) (subTerm (lift τ) T)
    het== subTerm (lift σ ⍟ lift τ) T
      :by: subTerm-⍟~id (lift σ) (lift τ) T
    === subTerm (lift (σ ⍟ τ)) T
      :by: ap (λ — → subTerm — T) $ lift-⍟ σ τ
  qed)
subTerm-⍟~id σ τ (λx, t) =
 ap λx,_ (
  proof subTerm (lift σ) (subTerm (lift τ) t)
    het== subTerm (lift σ ⍟ lift τ) t
      :by: subTerm-⍟~id (lift σ) (lift τ) t
    === subTerm (lift (σ ⍟ τ)) t
      :by: ap (λ — → subTerm — t) $ lift-⍟ σ τ
  qed)
subTerm-⍟~id σ τ ⌊ e ⌋ = ap ⌊_⌋ $ subElim-⍟~id σ τ e

sub ⦃ SubstitutableElim ⦄ = subElim
sub-id ⦃ SubstitutableElim ⦄ =
  subrel {_P_ = _==_} $ fun-ext subElim-var~id
sub-∘ ⦃ SubstitutableElim ⦄ σ τ =
  subrel {_P_ = _==_} $ fun-ext $ subElim-⍟~id σ τ

sub ⦃ SubstitutableTerm ⦄ = subTerm
sub-id ⦃ SubstitutableTerm ⦄ =
  subrel {_P_ = _==_} $ fun-ext subTerm-var~id
sub-∘ ⦃ SubstitutableTerm ⦄ σ τ =
  subrel {_P_ = _==_} $ fun-ext $ subTerm-⍟~id σ τ
-}
