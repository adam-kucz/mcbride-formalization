{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic

module Computation.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Computation.Definition

open import Proposition.Identity hiding (refl)
open import Data.Nat
open import Syntax

sorts-don't-reduce : {i : S}{e e' : Term n}
  (p : e ⇝ e')
  → --------------------------------
  e ≠ ⋆ {n = n} i
sorts-don't-reduce (v-exact (v _ _)) ()
sorts-don't-reduce (hole — p) = sorts-don't-reduce p

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
pi-reduct-forms (v-exact (v _ _)) ()
pi-reduct-forms (hole — p) q = pi-reduct-forms p q
pi-reduct-forms (hole {s = s}{t} [ ρ x: S ]→ C[—] ↓ p)
  (Id-refl ([ ρ x: S ]→ .(C[—] [ s /—]))) =
  ∨right (C[—] [ t /—] , (hole C[—] p , Id-refl _))
pi-reduct-forms (hole {s = s} {t} ([ ρ x: C[—] ↓]→ T) p)
  (Id-refl ([ ρ x: .(C[—] [ s /—]) ]→ T)) =
  ∨left (C[—] [ t /—] , (hole C[—] p , Id-refl _))

open import Type.Sum hiding (_,_)
open import Relation.Binary.ReflexiveTransitiveClosure

pi-compute-forms : ∀ {π : R}
  {S : Term n}{T}{e'}
  (p : [ π x: S ]→ T ↠ e')
  → --------------------------------
  ∃ {X = Term n × Term (n +1)}
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

mk-pi-compute : ∀ (π : R){S S' : Term n}{T T'}
  (p : S ↠ S')
  (q : T ↠ T')
  → ----------------
  [ π x: S ]→ T ↠ [ π x: S' ]→ T'
mk-pi-compute π (rfl S) q = ctx-closed q ([ π x: S ]→ — ↓)
mk-pi-compute π {T = T} (step S⇝S″ S″↠S') q =
  step (hole ([ π x: — ↓]→ T) S⇝S″) (mk-pi-compute π S″↠S' q)

open import Function.Proof

instance
  1-ContextClosed⇝ : 1-ContextClosed _⇝_

rel-preserv ⦃ 1-ContextClosed⇝ {C = C} ⦄ s⇝t = hole C s⇝t

sub-compute : ∀{m n tag}
  (σ : Sub m n)
  {e e' : expr-of-type tag m}
  (p : e ⇝ e')
  → ------------------------------
  subst σ e ⇝ subst σ e'
sub-compute σ (β-exact (β π s S t T)) =
  proof (λx, subst (lift σ) t ꞉ [ π x: subst σ S ]→ subst (lift σ) T) ` subst σ s
    〉 _⇝_ 〉 (subst (lift σ) (t ꞉ T)) [ subst σ (s ꞉ S) /new]
      :by: β-exact (β π (subst σ s) (subst σ S) (subst (lift σ) t) (subst (lift σ) T))
    === subst new-σ (subst (lift σ) (t ꞉ T))
      :by: Id-refl _
    === subst (new-σ ⍟ lift σ) (t ꞉ T)
      :by: ap (λ — → — (t ꞉ T)) $ sub-∘ new-σ (lift σ)  -- sym $ sub-newSub σ (s ꞉ S)
    === subst (σ ⍟ newSub (s ꞉ S)) (t ꞉ T)
      :by: ap (λ — → subst — (t ꞉ T)) $ sym {R = _==_} $
           sub-newSub σ (s ꞉ S)
    === subst σ ((t ꞉ T) [ s ꞉ S /new])
      :by: ap (λ — → — (t ꞉ T)) $ sym $ sub-∘ σ (newSub (s ꞉ S))
  qed
  where new-σ = newSub (subst σ (s ꞉ S))
sub-compute σ (v-exact (v t T)) = v-exact (v (subst σ t) (subst σ T))
sub-compute σ (hole C[—] p) with ⟶ ≤-↔-∃+ $ 1-hole-ctx-inhabited C[—]
sub-compute {m}{n} σ (hole {m'}{n'}{tag₀}{tag₁}{s}{t} C[—] p) | k , q =
  proof subst σ (C[—] [ s /—])
    === C' [ s' /—]
      :by: sub-ctx-aux σ s C[—] k (sym q)
    === C' [ s″ /—]
      :by: ap (C' [_/—]) $ move-coe s
    〉 _⇝_ 〉 C' [ t″ /—]
      :by: hole C' $ sub-compute σ' p
    === C' [ t' /—]
      :by: sym {R = _==_} $ ap (C' [_/—]) $ move-coe t
    === subst σ (C[—] [ t /—])
      :by: sym {R = _==_} $ sub-ctx-aux σ t C[—] k (sym q)
  qed
  where C' = sub σ (coe (ap (λ — → 1-hole-ctx tag₀ — tag₁ m) $ sym q) C[—])
        s' t' s″ t″ : expr-of-type tag₀ (k + n)
        coer = ap (expr-of-type tag₀) $ sym q
        s' = subst (lift-by k σ) (coe coer s)
        t' = subst (lift-by k σ) (coe coer t)
        σ-coer = ap (λ — → Var — → Elim (k + n)) q
        σ' = coe σ-coer (lift-by k σ)
        s″ = subst σ' s
        t″ = subst σ' t
        move-coe :
          (e : expr-of-type tag₀ m')
          → ----------------------------------------
          subst (lift-by k σ) (coe coer e) == subst σ' e
        move-coe e =
          subrel {_P_ = _==_} $
          Het.ap3 (λ i (σ : Sub i (k + n))(e : expr-of-type tag₀ i) → subst σ e)
                  q
                  (isym $ coe-eval σ-coer (lift-by k σ) )
                  (coe-eval coer e)

instance
  RelatingSub⇝ : ∀{tag}{σ : Sub m n} →
    Relating (subst {tag} σ) _⇝_ _⇝_
  RelatingRename⇝ : ∀{tag : ExprTag}{ρ : Ren m n} →
    Relating (rename ⦃ r = RenameableExpr {tag = tag} ⦄ ρ) _⇝_ _⇝_

rel-preserv ⦃ RelatingSub⇝ {σ = σ} ⦄ = sub-compute σ

rel-preserv ⦃ RelatingRename⇝ {ρ = ρ} ⦄ {a}{b} a⇝b =
  proof rename ρ a
    === subst (var ∘ ρ) a     :by: ap (λ — → — a) $ rename-as-sub ρ
    〉 _⇝_ 〉 subst (var ∘ ρ) b :by: ap (subst (var ∘ ρ)) a⇝b
    === rename ρ b            :by: ap (λ — → — b) $ sym $ rename-as-sub ρ
  qed
