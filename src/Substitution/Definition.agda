{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import Basic using (Rig; wfs)
open import PropUniverses

module Substitution.Definition
  {𝑅 : 𝒰 ˙} ⦃ r : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Syntax
open import Liftable
open import Renaming

open import Data.Nat
open import Data.Nat.Proof
open import Type.Identity using (transport; transport==)
open import Proposition.Comparable
open import Logic hiding (⊥-recursion)
open import Proof


Sub : (m n : ℕ) → 𝒰 ⁺ ⊔ 𝒱 ˙
Sub m n = (v : Var m) → Elim n

instance
  LiftableSub : Liftable Sub
  lift ⦃ LiftableSub ⦄ σ new = var new
  lift ⦃ LiftableSub ⦄ σ (old v) = shift (σ v)

sub : {m n : ℕ} {tag : ExprTag}
  (σ : Sub m n)
  (e : expr-of-type tag m)
  → ------------------------------
  expr-of-type tag n
sub {tag = term} σ (⋆ i) = ⋆ i
sub {tag = term} σ ([ ρ x: S ]→ T) = [ ρ x: sub σ S ]→ sub (lift σ) T
sub {tag = term} σ (λx, e) = λx, sub (lift σ) e
sub {tag = term} σ ⌊ e ⌋ = ⌊ sub σ e ⌋
sub {tag = elim} σ (var x) = σ x
sub {tag = elim} σ (f ` s) = sub σ f ` sub σ s
sub {tag = elim} σ (s ꞉ S) = sub σ s ꞉ sub σ S

nthSub : ∀ {n} m (p : m < suc n)(f : Elim n) → Sub (suc n) n
nthSub m p f v with compare (index v) _<_ m
nthSub {n} m p f v | lt q = var (contract v q')
  where q' : index v < n
        q' =
          proof index v
            〉 _<_ 〉 m :by: q
            〉 _≤_ 〉 n :by: ⟵ -≤-↔-<s p
          qed
nthSub m p f v | eq _ = f
nthSub m p f (old v) | gt _ = var v

newSub : ∀ {n} (f : Elim n) → Sub (suc n) n
newSub = nthSub 0 z<s

infix 180 _[_/new] _[_/_[_]]
_[_/new] : {n : ℕ} {tag : ExprTag}
  → -------------------------------------------------------------
  (e : expr-of-type tag (suc n)) (f : Elim n) → expr-of-type tag n
e [ f /new] = sub (newSub f) e

_[_/_[_]] : {n : ℕ} {tag : ExprTag}
  (e : expr-of-type tag (suc n))
  (f : Elim n)
  (m : ℕ)
  (p : m < suc n)
  → -------------------------------------------------------------
  expr-of-type tag n
e [ f / m [ p ]] = sub (nthSub m p f) e
