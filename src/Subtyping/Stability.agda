{-# OPTIONS --exact-split --prop #-}
open import Basic
open import PropUniverses

module Subtyping.Stability
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Subtyping.Definition

-- Lemma 21 (subtyping stability)

open import Proposition.Identity hiding (refl)
open import Proposition.Comparable
open import Data.Nat
open import Proof

open import Syntax.Definition
open import Syntax.Property
open import Substitution
open import Liftable
open import Renaming
open import Subtyping.Proof

open import Axiom.FunctionExtensionality

~-rename :
  {e e' : expr-of-type tag m}
  (p₀ : e ~ e')
  (ρ : Ren m n)
  → ---------------
  rename ⦃ r = RenameableExpr ⦄ ρ e
  ~
  rename ⦃ r = RenameableExpr ⦄ ρ e'
~-rename (~sort i) ρ = ~sort i
~-rename (~var v) ρ = ~var (ρ v)
~-rename (~pi π p₀ p₁) ρ = ~pi π (~-rename p₀ ρ) (~-rename p₁ (lift ρ))
~-rename (~lam p₀) ρ = ~lam (~-rename p₀ (lift ρ))
~-rename (~elim p₀) ρ = ~elim (~-rename p₀ ρ)
~-rename (~app p₀ p₁) ρ = ~app (~-rename p₀ ρ) (~-rename p₁ ρ)
~-rename (~annot S S' p₀) ρ = ~annot (rename ρ S) (rename ρ S') (~-rename p₀ ρ)

~-sub : ∀
  {e e' : expr-of-type tag (m +1)}
  (p₀ : e ~ e')
  {R R'}
  (p₁ : R ~ R')
  (q : n < m +1)
  → ---------------
  e [ R / n [ q ]] ~ e' [ R' / n [ q ]]
~-sub (~sort i) p₁ q = refl (⋆ i)
~-sub {n = n}(~var v) p₁ q with compare (index v) _<_ n ⦃ Comparableℕ ⦄
~-sub {n = n} (~var v) p₁ q | lt _ = refl (var (contract v _))
~-sub {n = n} (~var v) p₁ q | eq _ = p₁
~-sub {n = n} (~var (old v)) p₁ q | gt _ = refl (var v)
~-sub (~pi π p₀ p₂) p₁ q = {!!}
~-sub {n = n}(~lam {t = t}{t' = t'} p₀){R}{R'} p₁ q =
  proof (λx, t) [ R / n [ q ]]
    〉 _==_ 〉 λx, sub (lift (nthSub n q R)) t
      :by: Id.refl _
    〉 _==_ 〉 λx, sub (nthSub (n +1) _ (shift R)) t
      :by: ap (λ — → λx, sub — t) $ fun-ext $ lift-nth R q
    〉 _~_ 〉  λx, sub (nthSub (n +1) _ (shift R')) t'
      :by: ~lam (~-sub p₀ (~-rename p₁ old) (s<s q)) 
    〉 _==_ 〉 λx, sub (lift (nthSub n q R')) t'
      :by: ap (λ — → λx, sub — t') $ Id.sym $ fun-ext $ lift-nth R' q
    〉 _==_ 〉 (λx, t') [ R' / n [ q ]]
      :by: Id.refl _
  qed
~-sub (~elim p₀) p₁ q = ~elim (~-sub p₀ p₁ q)
~-sub (~app p₀ p₀') p₁ q = ~app (~-sub p₀ p₁ q) (~-sub p₀' p₁ q)
~-sub {n = n}(~annot S S' p₀){R}{R'} p₁ q =
  ~annot (S [ R / n [ q ]]) (S' [ R' / n [ q ]]) (~-sub p₀ p₁ q)

≼-stable : (r R R' : Term m)
  (q : n < m +1)
  {S T : expr-of-type tag (m +1)}
  (p : S ≼ T)
  → ---------------
  S [ r ꞉ R / n [ q ]] ≼ T [ r ꞉ R' / n [ q ]]
≼-stable r R R' q (≼similar p) = ≼similar (~-sub p (~annot R R' (refl r)) q)
≼-stable r R R' q (≼sort p) = ≼sort p
≼-stable {n = n} r R R' q (≼pi π {T = T}{T'} S'≼S T≼T') =
  ≼pi π (≼-stable r R' R q S'≼S) (
    proof sub (lift (nthSub n q (r ꞉ R))) T
      〉 _==_ 〉 sub (nthSub (n +1) (s<s q) (shift (r ꞉ R))) T
        :by: ap (λ — → sub — T) $ fun-ext $ lift-nth (r ꞉ R) q
      〉 _≼_ 〉 sub (nthSub (n +1) (s<s q) (shift (r ꞉ R'))) T'
        :by: ≼-stable (shift r) (shift R) (shift R') (s<s q) T≼T'
      〉 _==_ 〉 sub (lift (nthSub n q (r ꞉ R'))) T'
        :by: ap (λ — → sub — T') $ Id.sym $ fun-ext $ lift-nth (r ꞉ R') q
    qed)
