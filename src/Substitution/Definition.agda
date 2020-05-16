{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import Basic using (Rig; wfs)
open import PropUniverses

module Substitution.Definition
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax ⦃ rig ⦄ ⦃ wfs ⦄
open import Liftable
open import Renaming

open import Data.Nat
open import Data.Nat.Proof
open import Proposition.Identity hiding (refl)
open import Proposition.Identity.Coercion
open import Proposition.Comparable
open import Function.Extensionality
open import Logic hiding (⊥-recursion)
open import Proof

Sub : (m n : ℕ) → 𝒰 ⁺ ⊔ 𝒱 ˙
Sub m n = (v : Var m) → Elim n

sub :
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

nthSub : ∀ m (p : m < n +1)(f : Elim n) → Sub (n +1) n
nthSub m p f v with compare (index v) _<_ m ⦃ Comparable< ⦄
nthSub {n} m p f v | lt q = var (contract v (
  proof index v
    〉 _<_ 〉 m :by: q
    〉 _≤_ 〉 n :by: ap pred $ ⟶ -<-↔s≤- p
  qed))
nthSub m p f v | eq _ = f
nthSub m p f new | gt m<0 = ⊥-recursion _ (¬-<0 m m<0)
  where open import Proposition.Empty
nthSub m p f (old v) | gt _ = var v

newSub : (f : Elim n) → Sub (n +1) n
newSub {n} = nthSub 0 (z<s n)

infix 180 _[_/new] _[_/_[_]]
_[_/new] : {n : ℕ} {tag : ExprTag}
  → -------------------------------------------------------------
  (e : expr-of-type tag (suc n)) (f : Elim n) → expr-of-type tag n
e [ f /new] = sub (newSub f) e

_[_/_[_]] :
  (e : expr-of-type tag (n +1))
  (f : Elim n)
  (m : ℕ)
  (p : m < n +1)
  → -------------------------------------------------------------
  expr-of-type tag n
e [ f / m [ p ]] = sub (nthSub m p f) e

open import Function

_⍟_ : {m n k : ℕ}
  (σ' : Sub n k)
  (σ : Sub m n)
  → --------------
  Sub m k
σ' ⍟ σ = sub σ' ∘ σ
