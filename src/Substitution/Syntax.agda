{-# OPTIONS --exact-split --prop #-}
open import Basic using (Rig; wfs)
open import PropUniverses

module Substitution.Syntax
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Substitution.Definition
open WithInstanceArgs
open import Syntax

open import Data.Nat

instance
  SubstitutableExpr : ∀{tag} → Substitutable (expr-of-type tag)
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
lift-⍟-aux-Term : (k : ℕ){m n : ℕ}
  (σ : Sub m n)
  (e : Term (k + m))
  → ---------------------------------------------------
  let e' : Term (k + m +1)
      e' = coe (ap Term $ +-suc k m) (rent k e) in
  subTerm (lift-by (k +1) σ) e'
  Het.==
  rent k (subTerm (lift-by k σ) e)

lift-⍟-aux-Elim k {m}{n} σ (var v) =
  proof subElim (lift-by (k +1) σ) (coe coer (rene k (var v)))
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
lift-⍟-aux-Elim k {m}{n} σ (f ` s) =
  proof subElim (lift-by (k +1) σ) (coe (ap Elim $ +-suc k m) (rene k f ` rent k s))
    === subElim (lift-by (k +1) σ) (coe (ap Elim $ +-suc k m) (rene k f)) `
        subTerm (lift-by (k +1) σ) (coe (ap Term $ +-suc k m) (rent k s))
      :by: ap (subElim (lift-by (k +1) σ)) move-coe
    het== rene k (subElim (lift-by k σ) f) ` rent k (subTerm (lift-by k σ) s)
      :by: Het.ap3 (λ i (f : Elim i) (s : Term i) → f ` s)
             (sym $ +-suc k n)
             (lift-⍟-aux-Elim k σ f)
             (lift-⍟-aux-Term k σ s)
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
              :by: Het.ap3 (λ i (f : Elim i)(s : Term i) → f ` s)
                           (+-suc k m)
                           (isym $ coe-eval (ap Elim $ +-suc k m) (rene k f))
                           (isym $ coe-eval (ap Term $ +-suc k m) (rent k s))
          qed)
lift-⍟-aux-Elim k {m}{n} σ (s ꞉ S) =
  proof subElim (lift-by (k +1) σ) (coe (ap Elim $ +-suc k m) (rent k s ꞉ rent k S))
    === subTerm (lift-by (k +1) σ) (coe (ap Term $ +-suc k m) (rent k s)) ꞉
        subTerm (lift-by (k +1) σ) (coe (ap Term $ +-suc k m) (rent k S))
      :by: ap (subElim (lift-by (k +1) σ)) move-coe
    het== rent k (subTerm (lift-by k σ) s) ꞉ rent k (subTerm (lift-by k σ) S)
      :by: Het.ap3 (λ i (s S : Term i) → s ꞉ S)
             (sym $ +-suc k n)
             (lift-⍟-aux-Term k σ s)
             (lift-⍟-aux-Term k σ S)
  qed
  where move-coe :
          coe (ap Elim $ +-suc k m) (rent k s ꞉ rent k S)
          ==
          coe (ap Term $ +-suc k m) (rent k s) ꞉
          coe (ap Term $ +-suc k m) (rent k S)
        move-coe = subrel {_P_ = _==_} (
          proof coe (ap Elim $ +-suc k m) (rent k s ꞉ rent k S)
            het== rent k s ꞉ rent k S
              :by: coe-eval (ap Elim $ +-suc k m) (rent k s ꞉ rent k S)
            het== coe (ap Term $ +-suc k m) (rent k s) ꞉
                  coe (ap Term $ +-suc k m) (rent k S)
              :by: Het.ap3 (λ i (s S : Term i) → s ꞉ S)
                           (+-suc k m)
                           (isym $ coe-eval (ap Term $ +-suc k m) (rent k s))
                           (isym $ coe-eval (ap Term $ +-suc k m) (rent k S))
          qed)

lift-⍟-aux-Term k {m}{n} σ (⋆ i) =
  aux (coe (ap Term $ +-suc k m) (⋆ i))
      (+-suc k m)
      (coe-eval (ap Term $ +-suc k m) (⋆ i) )
  where aux : {l : ℕ}
          (t : Term (k + m +1))
          (p : l == k + m +1)
          (q : t Het.== ⋆ {n = l} i)
          → --------------------------------
          subTerm (lift-by (k +1) σ) t Het.== ⋆ {n = k + (n +1)} i
        aux (⋆ i) (Id-refl _) (Het.refl (⋆ i)) =
          ap (λ l → ⋆ {n = l} i) $ sym $ +-suc k n
lift-⍟-aux-Term k {m}{n} σ ([ π x: S ]→ T) =
  proof subTerm (lift-by (k +1) σ) (
          coe (ap Term $ +-suc k m) (rent k ([ π x: S ]→ T)))
    === [ π x: subTerm (lift-by (k +1) σ) (
                coe (ap Term $ +-suc k m) (rent k S)) ]→
              subTerm (lift (lift-by (k +1) σ)) (
                coe (ap Term $ +-suc (k +1) m) (rent (k +1) T))
      :by: ap (subTerm (lift-by (k +1) σ)) move-coe
    === [ π x: subTerm (lift-by (k +1) σ) (
                coe (ap Term $ +-suc k m) (rent k S)) ]→
              subTerm (lift-by (k +2) σ) (
                coe (ap Term $ +-suc (k +1) m) (rent (k +1) T))
      :by: ap (λ — → [ π x:
                 subTerm (lift-by (k +1) σ) (
                   coe (ap Term $ +-suc k m) (rent k S))]→
                 subTerm — (coe (ap Term $ +-suc (k +1) m) (
                   rent (k +1) T)))
              (subrel {_P_ = _==_} $ fun-ext $ lift-lift-by~ (k +1) σ)
    het== [ π x: rent k (subTerm (lift-by k σ) S) ]→
              rent (k +1) (subTerm (lift-by (k +1) σ) T)
      :by: Het.ap3 (λ i (S : Term i)(T : Term (i +1)) → [ π x: S ]→ T)
                   (sym $ +-suc k n)
                   (lift-⍟-aux-Term k σ S)
                   (lift-⍟-aux-Term (k +1) σ T)
    === rent k ([ π x: subTerm (lift-by k σ) S ]→
                    subTerm (lift (lift-by k σ)) T)
      :by: ap2 (λ —₀ —₁ → [ π x: rent k (subTerm (lift-by k σ) S) ]→
                          renTerm —₀ (subTerm —₁ T))
              (subrel {_P_ = _==_} $ fun-ext $ sym $
               lift-lift-by~ k old)
              (subrel {_P_ = _==_} $ fun-ext $ sym $
               lift-lift-by~ k σ)
  qed
  where move-coe :
          coe (ap Term $ +-suc k m) (rent k ([ π x: S ]→ T))
          ==
          [ π x: coe (ap Term $ +-suc k m) (rent k S) ]→
                 coe (ap Term $ +-suc (k +1) m) (rent (k +1) T)
        move-coe = subrel {_P_ = _==_} (
          proof coe (ap Term $ +-suc k m) (rent k ([ π x: S ]→ T))
            het== rent k ([ π x: S ]→ T)
              :by: coe-eval (ap Term $ +-suc k m) (rent k ([ π x: S ]→ T))
            === [ π x: rent k S ]→ rent (k +1) T
              :by: ap (λ — → [ π x: rent k S ]→ renTerm — T)
                      (subrel {_P_ = _==_} $ fun-ext $ lift-lift-by~ k old)
            het== [ π x: coe (ap Term $ +-suc k m) (rent k S) ]→
                    coe (ap Term $ +-suc (k +1) m) (rent (k +1) T)
              :by: Het.ap3 (λ i (S : Term i) (T : Term (i +1)) → [ π x: S ]→ T)
                     (+-suc k m)
                     (isym $ coe-eval (ap Term $ +-suc k m) (rent k S))
                     (isym $ coe-eval (ap Term $ +-suc (k +1) m) (rent (k +1) T))
          qed)
lift-⍟-aux-Term k {m}{n} σ (λx, t) =
  proof subTerm (lift-by (k +1) σ) (
          coe (ap Term $ +-suc k m) (λx, renTerm (lift (lift-by k old)) t))
    === subTerm (lift-by (k +1) σ) (
          coe (ap Term $ +-suc k m) (λx, rent (k +1) t))
      :by: ap (λ — → subTerm (lift-by (k +1) σ)
                       (coe (ap Term $ +-suc k m) (λx, renTerm — t)))
              (subrel {_P_ = _==_} $ fun-ext $ lift-lift-by~ k old)
    === λx, subTerm (lift (lift-by (k +1) σ)) (
            coe (ap Term $ +-suc (k +1) m) (rent (k +1) t))
      :by: ap (subTerm (lift-by (k +1) σ)) move-coe
    === λx, subTerm (lift-by (k +2) σ) (
            coe (ap Term $ +-suc (k +1) m) (rent (k +1) t))
      :by: ap (λ — → λx, subTerm — (coe
                     (ap Term $ +-suc (k +1) m) (rent (k +1) t)))
              (subrel {_P_ = _==_} $ fun-ext $ lift-lift-by~ (k +1) σ)
    het== λx, rent (k +1) (subTerm (lift-by (k +1) σ) t)
      :by: Id.ap2 (λ i (t : Term (i +1)) → λx, t)
                  (sym $ +-suc k n)
                  (lift-⍟-aux-Term (k +1) σ t)
    === λx, renTerm (lift (lift-by k old)) (subTerm (lift (lift-by k σ)) t)
      :by: ap2 (λ ρ σ → λx, renTerm ρ (subTerm σ t))
               (subrel {_P_ = _==_} $ fun-ext $ sym $
                lift-lift-by~ k old)
               (subrel {_P_ = _==_} $ fun-ext $ sym $
                lift-lift-by~ k σ)
  qed
  where move-coe :
          coe (ap Term $ +-suc k m) (λx, rent (k +1) t)
          ==
          λx, coe (ap Term $ +-suc (k +1) m) (rent (k +1) t)
        move-coe = subrel {_P_ = _==_} (
          proof coe (ap Term $ +-suc k m)
                    (λx, rent (k +1) t)
            het== λx, rent (k +1) t
              :by: coe-eval (ap Term $ +-suc k m) (λx, rent (k +1) t)
            het== λx, coe (ap Term $ +-suc (k +1) m) (rent (k +1) t)
              :by: Id.ap2 (λ i (t : Term (i +1)) → λx, t)
                          (+-suc k m)
                          (isym $ coe-eval (ap Term $ +-suc (k +1) m)
                                           (rent (k +1) t))
          qed)
lift-⍟-aux-Term k {m}{n} σ ⌊ e ⌋ =
  proof subTerm (lift-by (k +1) σ) (coe (ap Term $ +-suc k m) (⌊ rene k e ⌋))
    === ⌊ subElim (lift-by (k +1) σ) (coe (ap Elim $ +-suc k m) (rene k e)) ⌋
      :by: ap (subTerm (lift-by (k +1) σ)) move-coe
    het== ⌊ rene k (subElim (lift-by k σ) e) ⌋
      :by: Id.ap2 (λ i (e : Elim i) → ⌊ e ⌋)
                  (sym $ +-suc k n)
                  (lift-⍟-aux-Elim k σ e)
  qed
  where move-coe :
          coe (ap Term $ +-suc k m) (⌊ rene k e ⌋)
          ==
          ⌊ coe (ap Elim $ +-suc k m) (rene k e) ⌋
        move-coe = subrel {_P_ = _==_} (
          proof coe (ap Term $ +-suc k m) (⌊ rene k e ⌋)
            het== ⌊ rene k e ⌋
              :by: coe-eval (ap Term $ +-suc k m) (⌊ rene k e ⌋)
            het== ⌊ coe (ap Elim $ +-suc k m) (rene k e) ⌋
              :by: Id.ap2 (λ i (e : Elim i) → ⌊ e ⌋)
                     (+-suc k m)
                     (isym $ coe-eval (ap Elim $ +-suc k m) (rene k e))
          qed)

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
      het== subElim (lift σ) (coe (Id-refl _) (shift (τ v)))
        :by: ap (subElim (lift σ)) $ isym $
             coe-eval (Id-refl _) (shift (τ v))
      het== shift (subElim σ (τ v))
        :by: lift-⍟-aux-Elim 0 σ (τ v)
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

elim-ren~sub : (ρ : Ren m n)
  → ----------------------------------------
  renElim ρ ~ subElim (var ∘ ρ)
term-ren~sub : (ρ : Ren m n)
  → ----------------------------------------
  renTerm ρ ~ subTerm (var ∘ ρ)

elim-ren~sub ρ (var v) = Het.refl (var (ρ v))
elim-ren~sub ρ (f ` s) = ap2 _`_ (elim-ren~sub ρ f) (term-ren~sub ρ s)
elim-ren~sub ρ (s ꞉ S) = ap2 _꞉_ (term-ren~sub ρ s) (term-ren~sub ρ S)

lift-var∘ : (ρ : Ren m n)
  → ----------------------------------------
  var ∘ lift ρ == lift (var ∘ ρ)

lift-var∘ ρ = subrel {_P_ = _==_} $ fun-ext λ
  { new → Het.refl (var new)
  ; (old v) → Het.refl (var (old (ρ v)))}

term-ren~sub ρ (⋆ i) = Het.refl (⋆ i)
term-ren~sub ρ ([ π x: S ]→ T) =
  proof [ π x: renTerm ρ S ]→ renTerm (lift ρ) T
    het== [ π x: subTerm (var ∘ ρ) S ]→ subTerm (var ∘ lift ρ) T
      :by: ap2 [ π x:_]→_ (term-ren~sub ρ S) (term-ren~sub (lift ρ) T)
    === [ π x: subTerm (var ∘ ρ) S ]→ subTerm (lift (var ∘ ρ)) T
      :by: ap (λ — → [ π x: subTerm (var ∘ ρ) S ]→ subTerm — T) $
           lift-var∘ ρ
  qed
term-ren~sub ρ (λx, t) =
  proof λx, renTerm (lift ρ) t
    het== λx, subTerm (var ∘ lift ρ) t
      :by: ap λx,_ $ term-ren~sub (lift ρ) t
    === λx, subTerm (lift (var ∘ ρ)) t
      :by: ap (λ — → λx, subTerm — t) $ lift-var∘ ρ
  qed
term-ren~sub ρ ⌊ e ⌋ = ap ⌊_⌋ $ elim-ren~sub ρ e

Substitutable.ren SubstitutableExpr = RenameableExpr
sub ⦃ SubstitutableExpr {term} ⦄ = subTerm
sub-id ⦃ SubstitutableExpr {term} ⦄ =
  subrel {_P_ = _==_} $ fun-ext subTerm-var~id
sub-∘ ⦃ SubstitutableExpr {term} ⦄ σ τ =
  subrel {_P_ = _==_} $ fun-ext $ subTerm-⍟~id σ τ
rename-as-sub ⦃ SubstitutableExpr {term} ⦄ ρ =
  subrel {_P_ = _==_} $ fun-ext $ term-ren~sub ρ

sub ⦃ SubstitutableExpr {elim} ⦄ = subElim
sub-id ⦃ SubstitutableExpr {elim} ⦄ =
  subrel {_P_ = _==_} $ fun-ext subElim-var~id
sub-∘ ⦃ SubstitutableExpr {elim} ⦄ σ τ =
  subrel {_P_ = _==_} $ fun-ext $ subElim-⍟~id σ τ
rename-as-sub ⦃ SubstitutableExpr {elim} ⦄ ρ =
  subrel {_P_ = _==_} $ fun-ext $ elim-ren~sub ρ

SubstitutableTerm = SubstitutableExpr {term}
SubstitutableElim = SubstitutableExpr {elim}
