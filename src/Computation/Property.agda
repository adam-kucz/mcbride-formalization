{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic

module Computation.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Computation.Definition

open import Data.Nat
open import Syntax ⦃ rig ⦄ ⦃ wfs ⦄
open import Syntax.Context ⦃ rig ⦄ ⦃ wfs ⦄
open import Proof

sorts-don't-reduce : {i : S}{e e' : Term n}
  (p : e ⇝ e')
  → --------------------------------
  e ≠ ⋆ {n = n} i
sorts-don't-reduce (v-exact (v _ _)) ()
sorts-don't-reduce (hole — p) (Id-refl (⋆ i)) =
  sorts-don't-reduce p $ Id-refl (⋆ i)
sorts-don't-reduce (hole [ π x: S ]→ C ↓ p) ()
sorts-don't-reduce (hole ([ π x: C ↓]→ T) p) ()
sorts-don't-reduce (hole (λx, C) p) ()
sorts-don't-reduce (hole ⌊ C ⌋ p) ()

open import Logic
open import Proof

pi-reduct-forms : ∀ {π : R}
  {e e' S : Term n}{T}
  (p : e ⇝ e')
  (q : e == [ π x: S ]→ T)
  → --------------------------------
  (∃ λ S' → S ⇝ S' ∧ e' == [ π x: S' ]→ T)
  ∨
  (∃ λ T' → T ⇝ T' ∧ e' == [ π x: S ]→ T')
pi-reduct-forms (v-exact ()) (Id-refl _)
pi-reduct-forms (hole — p) (Id-refl _) = pi-reduct-forms p (Id-refl _)
pi-reduct-forms (hole {t = t} [ π x: S ]→ C[—] ↓ p) (Id-refl _) =
  ∨right (C[—] [ t /—] , (hole C[—] p , Id-refl _))
pi-reduct-forms (hole {t = t} ([ π x: C[—] ↓]→ T) p) (Id-refl _) =
  ∨left (C[—] [ t /—] , (hole C[—] p , Id-refl _))

open import Type.Sum hiding (_,_) renaming (_×_ to _χ_)

pi-compute-forms : ∀ {π : R}
  {S : Term n}{T : Term (n +1)}{e' : Term n}
  (p : [ π x: S ]→ T ↠ e')
  → --------------------------------
  ∃ {X = Term n χ Term (n +1)}
    (λ {(S' Σ., T') → S ↠ S' ∧ T ↠ T' ∧ e' == [ π x: S' ]→ T'})
pi-compute-forms (rfl ([ π x: S ]→ T)) =
  (S Σ., T) , (refl S , refl T , refl ([ π x: S ]→ T))
pi-compute-forms (step [πx:S]→T⇝e″ p)
  with pi-reduct-forms [πx:S]→T⇝e″ (Id-refl _)
pi-compute-forms (step [πx:S]→T⇝e″ p)
  | ∨left (S″ , (S⇝S″ , Id-refl _)) with pi-compute-forms p
pi-compute-forms (step [πx:S]→T⇝e″ p)
  | ∨left (S″ , (S⇝S″ , Id-refl _))
  | (S' Σ., T') , (S″↠S' , T↠T' , Id-refl _) =
  (S' Σ., T') , (step S⇝S″ S″↠S' , T↠T' , Id-refl _)
pi-compute-forms (step [πx:S]→T⇝e″ p)
  | ∨right (T″ , (T⇝T″ , Id-refl _)) with pi-compute-forms p
pi-compute-forms (step [πx:S]→T⇝e″ p)
  | ∨right (T″ , (T⇝T″ , Id-refl _))
  | (S' Σ., T') , (S↠S' , T″↠T' , Id-refl _) =
  (S' Σ., T') , (S↠S' , step T⇝T″ T″↠T' , Id-refl _)

open import Function.Proof

instance
  OneContextClosed⇝ : OneContextClosed _⇝_

rel-preserv ⦃ OneContextClosed⇝ {C = C} ⦄ s⇝t = hole C s⇝t

open import Substitution hiding (sub-∘; rename-as-sub)
open import Liftable
private
  module Tag {tag : ExprTag} where
    open import Substitution
    open WithInstanceArgs ⦃ subst = SubstitutableExpr {tag = tag} ⦄ public
open Tag renaming (sub to subst)

open import Data.Functor
open import Function hiding (_$_)
open import Computation.Proof

postulate
  sub-compute : ∀{m n tag}
    (σ : Sub m n)
    {e e' : expr-of-type tag m}
    (p : e ⇝ e')
    → ------------------------------
    subst σ e ⇝ subst σ e'
{-
sub-compute σ (v-exact (v t T)) = v-exact (v (subst σ t) (subst σ T))
sub-compute σ (β-exact (β π s S t T)) =
  proof (λx, subst (lift σ) t ꞉ [ π x: subst σ S ]→ subst (lift σ) T) `
          subst σ s
    〉 _⇝_ 〉 (subst (lift σ) (t ꞉ T)) [ subst σ (s ꞉ S) /new]
      :by: β-exact (β π (subst σ s) (subst σ S)
                        (subst (lift σ) t) (subst (lift σ) T))
    === subst new-σ (subst (lift σ) (t ꞉ T))
      :by: Id-refl _
    === subst (new-σ ⍟ lift σ) (t ꞉ T)
      :by: ap (λ — → — (t ꞉ T)) {r = _==_} $ sub-∘ new-σ (lift σ)
    === subst (σ ⍟ newSub (s ꞉ S)) (t ꞉ T)
      :by: ap (λ — → subst — (t ꞉ T)) $ sym {R = _==_} $
           sub-newSub σ (s ꞉ S)
    === subst σ ((t ꞉ T) [ s ꞉ S /new])
      :by: ap (λ — → — (t ꞉ T)) {r = _==_} $ sym {R = _==_} $
           sub-∘ σ (newSub (s ꞉ S))
  qed
  where new-σ = newSub (subst σ (s ꞉ S))
sub-compute {m}{n}{tag} σ (hole {s = s}{t} C[—] p) =
  proof subst σ (C[—] [ s /—])
    === subst σ (fill-holes (as-filling C[—] s) (as-arbitrary C[—]))
      :by: ap (subst σ) $ context-equivalence C[—] s
    === fill-holes (sub-all σ (hole-loc C[—]) e') (sub σ C')
      :by: {!sub-compute (lift-by m σ)!}
    〉 _⇝_ 〉 subst σ (C[—] [ t /—])
      :by: {!!}
  qed
  where e' : all-types (fmap [ id × _+ m ] (hole-loc C[—]))
        e' = {!!}
        C' : Context (fmap [ id × _+ m ] (hole-loc C[—])) tag m
        C' = {!!}
-}

open import Renaming

instance
  RelatingSub⇝ : ∀{tag}{σ : Sub m n} →
    Relating (subst {tag} σ) _⇝_ _⇝_
  RelatingRename⇝ : ∀{tag : ExprTag}{ρ : Ren m n} →
    Relating (rename ⦃ r = RenameableExpr {tag = tag} ⦄ ρ) _⇝_ _⇝_

rel-preserv ⦃ RelatingSub⇝ {σ = σ} ⦄ = sub-compute σ

rel-preserv ⦃ RelatingRename⇝ {ρ = ρ} ⦄ {a}{b} a⇝b =
  proof rename ρ a
    === subst (var ∘ ρ) a
      :by: ap (λ — → — a) {r = _==_} $ rename-as-sub ρ
    〉 _⇝_ 〉 subst (var ∘ ρ) b
      :by: ap (subst (var ∘ ρ)) {a = a}{b} a⇝b
    === rename ρ b
      :by: ap (λ — → — b) {r = _==_ } $ sym {R = _==_} $
           rename-as-sub ρ
  qed

instance
  ContextClosed↠ : ContextClosed _↠_

ctx-closed ⦃ ContextClosed↠ ⦄ (term t) p = refl t
ctx-closed ⦃ ContextClosed↠ ⦄ (elim e) p = refl e
ctx-closed ⦃ ContextClosed↠ ⦄ — p = p
ctx-closed ⦃ ContextClosed↠ ⦄ ([ π x: C₀ ]→ C₁){l Σ., r}{l' Σ., r'}(p₀ , p₁) =
  proof [ π x: fill-holes l C₀ ]→ fill-holes r C₁
    〉 _↠_ 〉 [ π x: fill-holes l C₀ ]→ fill-holes r' C₁
      :by: 1-ctx-closed (ctx-closed C₁ p₁) ([ π x: fill-holes l C₀ ]→ — ↓)
    〉 _↠_ 〉 [ π x: fill-holes l' C₀ ]→ fill-holes r' C₁
      :by: 1-ctx-closed (ctx-closed C₀ p₀) ([ π x: — ↓]→ fill-holes r' C₁)
  qed
ctx-closed ⦃ ContextClosed↠ ⦄ (λx, C) p =
  1-ctx-closed (ctx-closed C p) (λx, —)
ctx-closed ⦃ ContextClosed↠ ⦄ ⌊ C ⌋ p =
  1-ctx-closed (ctx-closed C p) ⌊ — ⌋
ctx-closed ⦃ ContextClosed↠ ⦄ (C₀ ` C₁){l Σ., r}{l' Σ., r'}(p₀ , p₁) =
  proof fill-holes l C₀ ` fill-holes r C₁
    〉 _↠_ 〉 fill-holes l C₀ ` fill-holes r' C₁
      :by: 1-ctx-closed (ctx-closed C₁ p₁) (fill-holes l C₀ ` — ↓)
    〉 _↠_ 〉 fill-holes l' C₀ ` fill-holes r' C₁
      :by: 1-ctx-closed (ctx-closed C₀ p₀) (— ↓` fill-holes r' C₁)
  qed
ctx-closed ⦃ ContextClosed↠ ⦄ (C₀ ꞉ C₁){l Σ., r}{l' Σ., r'}(p₀ , p₁) =
  proof fill-holes l C₀ ꞉ fill-holes r C₁
    〉 _↠_ 〉 fill-holes l C₀ ꞉ fill-holes r' C₁
      :by: 1-ctx-closed (ctx-closed C₁ p₁) (fill-holes l C₀ ꞉ — ↓)
    〉 _↠_ 〉 fill-holes l' C₀ ꞉ fill-holes r' C₁
      :by: 1-ctx-closed (ctx-closed C₀ p₀) (— ↓꞉ fill-holes r' C₁)
  qed
