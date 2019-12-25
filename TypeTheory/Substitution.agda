{-# OPTIONS --exact-split --prop --safe #-}
open import TypeTheory.Basic using (Rig; wfs)
open import Foundation.PropUniverses

module TypeTheory.Substitution
  {𝑅 : 𝒰 ˙} ⦃ r : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import TypeTheory.Syntax
  using (Var; Elim; Term; ExprTag; expr-of-type)
open Var; open Elim; open Term; open ExprTag
open import Foundation.Data.Nat
  using (ℕ; zero; suc; _+_)

Ren : (m n : ℕ) → 𝒰₀ ˙
Ren m n = (v : Var m) → Var n

-- identity renaming allowing the result to have more variables
idRen1 : (m : ℕ) → Ren m (suc m)
idRen1 (suc m) new = new
idRen1 (suc m) (old v) = old (idRen1 m v)

-- extends renaming by mapping new variable to itself
lift : {m n : ℕ} (ρ : Ren m n) → Ren (suc m) (suc n)
lift ρ new     = new
lift ρ (old x) = old (ρ x)

-- renames variables in an expression according to Ren
rename : {m n : ℕ} (ρ : Ren m n) {τ : ExprTag}
  (e : expr-of-type τ m) → expr-of-type τ n
rename ρ {term} (⋆ i) = ⋆ i
rename ρ {term} ([ ρ₁ x: S ]→ T) = [ ρ₁ x: rename ρ S ]→ rename (lift ρ) T
rename ρ {term} (λx, t) = λx, rename (lift ρ) t
rename ρ {term} ⌊ e ⌋ = ⌊ rename ρ e ⌋
rename ρ {elim} (var x) = var (ρ x)
rename ρ {elim} (f ` s) = rename ρ f ` rename ρ s
rename ρ {elim} (s ꞉ S) = rename ρ s ꞉ rename ρ S

wk1 : {m : ℕ} {τ : ExprTag}
  (e : expr-of-type τ m) → expr-of-type τ (suc m)
wk1 {m} = rename (idRen1 m)

shift-by : {m : ℕ} {τ : ExprTag}
  (n : ℕ)
  (e : expr-of-type τ m)
  → ------------------------------
  expr-of-type τ (n + m)
shift-by zero e = e
shift-by (suc n) e = rename old (shift-by n e)

Sub : (m n : ℕ) → 𝒰 ⁺ ⊔ 𝒱 ˙
Sub m n = (v : Var m) → Elim n

liftSub : {m n : ℕ} (σ : Sub m n) → Sub (suc m) (suc n)
liftSub σ new = var new
liftSub σ (old v) = shift-by 1 (σ v)

sub : {m n : ℕ} {tag : ExprTag}
  (σ : Sub m n)
  (e : expr-of-type tag m)
  → ------------------------------
  expr-of-type tag n
sub {tag = term} σ (⋆ i) = ⋆ i
sub {tag = term} σ ([ ρ x: S ]→ T) = [ ρ x: sub σ S ]→ sub (liftSub σ) T
sub {tag = term} σ (λx, e) = λx, sub (liftSub σ) e
sub {tag = term} σ ⌊ e ⌋ = ⌊ sub σ e ⌋
sub {tag = elim} σ (var x) = σ x
sub {tag = elim} σ (f ` s) = sub σ f ` sub σ s
sub {tag = elim} σ (s ꞉ S) = sub σ s ꞉ sub σ S

infix 180 _[_/new]
_[_/new] : {n : ℕ} {tag : ExprTag}
  → -------------------------------------------------------------
  (e : expr-of-type tag (suc n)) (f : Elim n) → expr-of-type tag n
_[_/new] {n} e f = sub f-for-new e
  where f-for-new : Sub (suc n) n
        f-for-new new = f
        f-for-new (old v) = var v
