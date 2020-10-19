{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic

module Computation.Property.General
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Computation.Definition

open import Data.Nat
open import Syntax ⦃ rig ⦄ ⦃ wfs ⦄
open import Syntax.Context ⦃ rig ⦄ ⦃ wfs ⦄
open import Logic
open import Proof

open import Function.Proof

instance
  OneContextClosed⇝ : OneContextClosed _⇝_

rel-preserv ⦃ OneContextClosed⇝ {C = C} ⦄ s⇝t = hole C s⇝t

open import Liftable
open import Substitution
  hiding (sub; sub-∘; rename-as-sub; _[_/new])

open import Data.Functor
open import Function hiding (_$_)
open import Computation.Proof

private
  module Tag {tag : ExprTag} where
    open import Substitution
    open WithInstanceArgs ⦃ subst = SubstitutableExpr {tag = tag} ⦄ public
open Tag

open import Relation.Binary renaming (refl-trans-close to rtc)

private
  -- parametrize _⇝_ over number of proof steps to convince agda of termination
  data [:_]_⇝_ {n} :
        (k : ℕ)
        (e₀ e₁ : expr-of-type tag n)
        → ----------------------------------------
        𝒰 ⁺ ⊔ 𝒱 ᵖ
        where
    β : ∀ (π : R)(s S : Term n)(t T : Term (n +1))
      → ----------------------------------------------------
      [:_]_⇝_ {tag = elim} 0 ((λx, t ꞉ ([ π x: S ]→ T)) ` s)
                             ((t ꞉ T) [ s ꞉ S /new])
  
    v : (t T : Term n)
      → --------------
      [: 0 ] ⌊ t ꞉ T ⌋ ⇝ t
  
    hole : ∀ {k m tag₀ tag₁ s t}
      (C[—] : OneHoleContext tag₀ m tag₁ n)
      (reduct : [: k ] s ⇝ t)
      → --------------------
      [: k +1 ] C[—] [ s /—] ⇝ C[—] [ t /—]

instance
  [:-]⇝⊆⇝ : (λ e e' → ∃ λ k → [: k ] e ⇝ e') ⊆ _⇝_ {n = n}{tag}
  ⇝⊆[:-]⇝ : _⇝_ {n = n}{tag} ⊆ (λ e e' → ∃ λ k → [: k ] e ⇝ e')

subrel⊆ [:-]⇝⊆⇝ (0 , β π s S t T) = β π s S t T
subrel⊆ [:-]⇝⊆⇝ (0 , v t T) = v t T
subrel⊆ [:-]⇝⊆⇝ (k +1 , hole C[—] p) = hole C[—] (subrel (k , p))

subrel⊆ ⇝⊆[:-]⇝ (β π s S t T) = 0 , β π s S t T
subrel⊆ ⇝⊆[:-]⇝ (v t T) = 0 , v t T
subrel⊆ ⇝⊆[:-]⇝ (hole C[—] p) with subrel⊆ ⇝⊆[:-]⇝ p
subrel⊆ ⇝⊆[:-]⇝ (hole C[—] p) | k , p' = k +1 , hole C[—] p'

sub-compute-aux : ∀ k {m n tag}
  (σ : Sub m n)
  {e e' : expr-of-type tag m}
  (p : [: k ] e ⇝ e')
  → ------------------------------
  ∃ λ k' → [: k' ] sub σ e ⇝ sub σ e'
sub-compute-aux 0 σ (v t T) = 0 , v (sub σ t) (sub σ T)
sub-compute-aux 0 {n = n} σ (β π s S t T) =
  0 , Id.coe (ap ([: 0 ] sub σ ((λx, t ꞉ [ π x: S ]→ T) ` s) ⇝_) p) $
        β π (sub σ s) (sub σ S) (sub (lift σ) t) (sub (lift σ) T)
  where new-σ = newSub (sub σ (s ꞉ S))
        p : Idₚ (Elim n)
              (sub (lift σ) (t ꞉ T) [ sub σ (s ꞉ S) /new])
              (sub σ ((t ꞉ T) [ s ꞉ S /new]))
        p = proof (sub (lift σ) (t ꞉ T)) [ sub σ (s ꞉ S) /new]
              === sub new-σ (sub (lift σ) (t ꞉ T))
                :by: Id.refl _ [: _==_ ]
              === sub (new-σ ⍟ lift σ) (t ꞉ T)
                :by: ap (λ — → — (t ꞉ T)) {r = _==_} $ sub-∘ new-σ (lift σ)
                     [: _==_ ]
              === sub (σ ⍟ newSub (s ꞉ S)) (t ꞉ T)
                :by: ap (λ — → sub — (t ꞉ T)) $ sym {R = _==_} $
                     sub-newSub σ (s ꞉ S)
                     [: _==_ ]
              === sub σ ((t ꞉ T) [ s ꞉ S /new])
                :by: ap (λ — → — (t ꞉ T)) {r = _==_} $ sym {R = _==_} $
                     sub-∘ σ (newSub (s ꞉ S))
                     [: _==_ ]
            qed
sub-compute-aux (k +1) σ (hole {s = s}{t} — s⇝t) = sub-compute-aux k σ s⇝t
sub-compute-aux k σ (hole [ π x: S ]→ C[—] ↓ s⇝t)
  with sub-compute-aux k (lift σ) (hole C[—] s⇝t)
sub-compute-aux k σ (hole [ π x: S ]→ C[—] ↓ s⇝t) | k' , p =
  k' +1 , hole [ π x: sub σ S ]→ — ↓ p
sub-compute-aux k σ (hole ([ π x: C[—] ↓]→ T) s⇝t)
  with sub-compute-aux k σ (hole C[—] s⇝t)
sub-compute-aux k σ (hole ([ π x: C[—] ↓]→ T) s⇝t) | k' , p =
  k' +1 , hole ([ π x: — ↓]→ sub (lift σ) T) p
sub-compute-aux k σ (hole (λx, C[—]) s⇝t)
  with sub-compute-aux k (lift σ) (hole C[—] s⇝t)
sub-compute-aux k σ (hole (λx, C[—]) s⇝t) | k' , p =
  k' +1 , hole (λx, —) p
sub-compute-aux k σ (hole ⌊ C[—] ⌋ s⇝t)
  with sub-compute-aux k σ (hole C[—] s⇝t)
sub-compute-aux k σ (hole ⌊ C[—] ⌋ s⇝t) | k' , p =
  k' +1 , hole ⌊ — ⌋ p
sub-compute-aux k σ (hole (f ` C[—] ↓) s⇝t)
  with sub-compute-aux k σ (hole C[—] s⇝t)
sub-compute-aux k σ (hole (f ` C[—] ↓) s⇝t) | k' , p =
  k' +1 , hole (sub σ f ` — ↓) p
sub-compute-aux k σ (hole (C[—] ↓` s) s⇝t)
  with sub-compute-aux k σ (hole C[—] s⇝t)
sub-compute-aux k σ (hole (C[—] ↓` s) s⇝t) | k' , p =
  k' +1 , hole (— ↓` sub σ s) p
sub-compute-aux k σ (hole (s ꞉ C[—] ↓) s⇝t)
  with sub-compute-aux k σ (hole C[—] s⇝t)
sub-compute-aux k σ (hole (s ꞉ C[—] ↓) s⇝t) | k' , p =
  k' +1 , hole (sub σ s ꞉ — ↓) p
sub-compute-aux k σ (hole (C[—] ↓꞉ S) s⇝t)
  with sub-compute-aux k σ (hole C[—] s⇝t)
sub-compute-aux k σ (hole (C[—] ↓꞉ S) s⇝t) | k' , p =
  k' +1 , hole (— ↓꞉ sub σ S) p

sub-compute : ∀{m n tag}
  (σ : Sub m n)
  {e e' : expr-of-type tag m}
  (p : e ⇝ e')
  → ------------------------------
  sub σ e ⇝ sub σ e'
sub-compute σ p with subrel ⦃ ⇝⊆[:-]⇝ ⦄ p
sub-compute σ p | k , q = subrel $ sub-compute-aux k σ q

open import Renaming

instance
  RelatingSub⇝ : ∀{tag}{σ : Sub m n} →
    Relating (sub {tag} σ) _⇝_ _⇝_
  RelatingRename⇝ : ∀{tag : ExprTag}{ρ : Ren m n} →
    Relating (rename ⦃ r = RenameableExpr {tag = tag} ⦄ ρ) _⇝_ _⇝_

rel-preserv ⦃ RelatingSub⇝ {σ = σ} ⦄ = sub-compute σ

rel-preserv ⦃ RelatingRename⇝ {ρ = ρ} ⦄ {a}{b} a⇝b =
  proof rename ρ a
    === sub (var ∘ ρ) a
      :by: ap (λ — → — a) {r = _==_} $ rename-as-sub ρ [: _==_ ]
    〉 _⇝_ 〉 sub (var ∘ ρ) b
      :by: ap (sub (var ∘ ρ)) {a = a}{b} a⇝b [: _⇝_ ]
    === rename ρ b
      :by: ap (λ — → — b) {r = _==_ } $ sym {R = _==_} $
           rename-as-sub ρ
  qed

instance
  ContextClosed↠ : ContextClosed _↠_

open import Type.Sum renaming (_,_ to _Σ,_)

ctx-closed ⦃ ContextClosed↠ ⦄ (term t) p = refl t
ctx-closed ⦃ ContextClosed↠ ⦄ (elim e) p = refl e
ctx-closed ⦃ ContextClosed↠ ⦄ — p = p
ctx-closed ⦃ ContextClosed↠ ⦄ ([ π x: C₀ ]→ C₁){l Σ, r}{l' Σ, r'}(p₀ , p₁) =
  proof [ π x: fill-holes l C₀ ]→ fill-holes r C₁
    〉 _↠_ 〉 [ π x: fill-holes l C₀ ]→ fill-holes r' C₁
      :by: 1-ctx-closed (ctx-closed C₁ p₁) ([ π x: fill-holes l C₀ ]→ — ↓)
           [: _↠_ ]
    〉 _↠_ 〉 [ π x: fill-holes l' C₀ ]→ fill-holes r' C₁
      :by: 1-ctx-closed (ctx-closed C₀ p₀) ([ π x: — ↓]→ fill-holes r' C₁)
  qed
ctx-closed ⦃ ContextClosed↠ ⦄ (λx, C) p =
  1-ctx-closed (ctx-closed C p) (λx, —)
ctx-closed ⦃ ContextClosed↠ ⦄ ⌊ C ⌋ p =
  1-ctx-closed (ctx-closed C p) ⌊ — ⌋
ctx-closed ⦃ ContextClosed↠ ⦄ (C₀ ` C₁){l Σ, r}{l' Σ, r'}(p₀ , p₁) =
  proof fill-holes l C₀ ` fill-holes r C₁
    〉 _↠_ 〉 fill-holes l C₀ ` fill-holes r' C₁
      :by: 1-ctx-closed (ctx-closed C₁ p₁) (fill-holes l C₀ ` — ↓)
           [: _↠_ ]
    〉 _↠_ 〉 fill-holes l' C₀ ` fill-holes r' C₁
      :by: 1-ctx-closed (ctx-closed C₀ p₀) (— ↓` fill-holes r' C₁)
  qed
ctx-closed ⦃ ContextClosed↠ ⦄ (C₀ ꞉ C₁){l Σ, r}{l' Σ, r'}(p₀ , p₁) =
  proof fill-holes l C₀ ꞉ fill-holes r C₁
    〉 _↠_ 〉 fill-holes l C₀ ꞉ fill-holes r' C₁
      :by: 1-ctx-closed (ctx-closed C₁ p₁) (fill-holes l C₀ ꞉ — ↓)
           [: _↠_ ]
    〉 _↠_ 〉 fill-holes l' C₀ ꞉ fill-holes r' C₁
      :by: 1-ctx-closed (ctx-closed C₀ p₀) (— ↓꞉ fill-holes r' C₁)
  qed
