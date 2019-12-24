{-# OPTIONS --exact-split --prop  #-} -- TODO: make safe
open import Foundation.PropUniverses
open import TypeTheory.Basic using (Rig; wfs)

module TypeTheory.Computation
  {R : 𝒰 ˙} ⦃ r : Rig R ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import TypeTheory.Syntax

open import Foundation.Data.Nat using (ℕ; suc; zero; _+_; +-suc)
open import Foundation.Prop'.Identity
open import Foundation.Prop'.Identity.Transport
open import Foundation.Prop'.Function using (_$_)
open import Foundation.Relation.Binary.Property
open import Foundation.Operation.Binary.Property

-- Definition 5 (contraction, reduction, computation)

Ren : (m n : ℕ) → 𝒰₀ ˙
Ren m n = (v : Var m) → Var n

-- identity renaming allowing the result to have more variables
idRen : (m n : ℕ) → Ren m (n + m)
idRen (suc m) n new = t' new
  where t' = transport (ap Var $ sym $ +-suc n m)
idRen (suc m) n (old v) = t' (old (idRen m n v))
  where t' = transport (ap Var $ sym $ +-suc n m)

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

wk : {m : ℕ} (n : ℕ) {τ : ExprTag}
  (e : expr-of-type τ m) → expr-of-type τ (n + m)
wk {m} n = rename (idRen m n)

wk' : {m : ℕ} (n : ℕ) {τ : ExprTag}
  (e : expr-of-type τ m) → expr-of-type τ (m + n)
wk' {m} n {τ} e = transport (ap (expr-of-type τ) $ comm n m) (wk n e)

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

infix 36 _⇝β_ _⇝v_
data _⇝β_ {n : ℕ} : (e e' : Elim n) → 𝒰₀ ᵖ where
  β : ∀ π s S t T
    → ----------------------------------------------------
    (λx, t ꞉ ([ π x: S ]→ T)) ` s ⇝β (t ꞉ T) [ s ꞉ S /new]

data _⇝v_ {n : ℕ} : (t T : Term n) → 𝒰₀ ᵖ
  where
  v : ∀ t T
    → --------------
    ⌊ t ꞉ T ⌋ ⇝v t

data 1-hole-ctx
  : --------------------------------------------------
  (hole : ExprTag) -- required type of hole
  (m : ℕ) -- number of variables bound in hole
  (result : ExprTag) -- type resulting from filling hole
  (n : ℕ) -- number of free variables of the context
  → 𝒰 ⁺ ⊔ 𝒱 ˙
  where
  — : ∀ {e}
    → ------------
    1-hole-ctx e 0 e 0
  
  [_x:_]→_↓ : ∀ {e} {m n}
    (ρ : R)
    (S : Term n)
    (C[—] : 1-hole-ctx e m term (suc n))
    → ---------------------
    1-hole-ctx e (suc m) term n

  [_x:_↓]→_ : ∀ {e} {m n}
    (ρ : R)
    (C[—] : 1-hole-ctx e m term n)
    (T : Term (suc n))
    → ----------------------
    1-hole-ctx e m term n

  λx,_ : ∀ {e} {m n}
    (C[—] : 1-hole-ctx e m term (suc n))
    → ----------------------
    1-hole-ctx e (suc m) term n

  ⌊_⌋ : ∀ {e} {m n}
    (C[—] : 1-hole-ctx e m elim n)
    → ---------------------
    1-hole-ctx e m term n

  _`_↓ : ∀ {e} {m n}
    (f : Elim n)
    (C[—] : 1-hole-ctx e m term n)
    → ----------------------
    1-hole-ctx e m elim n

  _↓`_ : ∀ {e} {m n}
    (C[—] : 1-hole-ctx e m elim n)
    (s : Term n)
    → ---------------------
    1-hole-ctx e m elim n

  _∶_↓ : ∀ {e} {m n}
    (s : Term n)
    (C[—] : 1-hole-ctx e m term n)
    →  ----------------------
    1-hole-ctx e m elim n

  _↓∶_ : ∀ {e} {m n}
    (C[—] : 1-hole-ctx e m term n)
    (S : Term n)
    → ----------------------
    1-hole-ctx e m elim n

infix 180 _[_/—]
_[_/—] : {m n : ℕ}
  {tag₁ tag₂ : ExprTag}
  (C[—] : 1-hole-ctx tag₁ m tag₂ n)
  (e : expr-of-type tag₁ (m + n))
  → ----------------------
  expr-of-type tag₂ n
— [ e /—] = e
_[_/—] {suc m} {n} {tag₁} ([ π x: S ]→ C[—] ↓) e = [ π x: S ]→ C[—] [ e' /—]
  where e' = transport (ap (expr-of-type tag₁) $ sym $ +-suc m n) e
([ π x: C[—] ↓]→ T) [ e /—] = [ π x: C[—] [ e /—] ]→ T
_[_/—] {suc m} {n} {tag₁} (λx, C[—]) e = λx, C[—] [ e' /—]
  where e' = transport (ap (expr-of-type tag₁) $ sym $ +-suc m n) e
⌊ C[—] ⌋ [ e /—] = ⌊ C[—] [ e /—] ⌋
(f ` C[—] ↓) [ e /—] = f ` C[—] [ e /—]
(C[—] ↓` s) [ e /—] = C[—] [ e /—] ` s
(s ∶ C[—] ↓) [ e /—] = s ꞉ C[—] [ e /—]
(C[—] ↓∶ S) [ e /—] = C[—] [ e /—] ꞉ S

infix 36 _⇝_
data _⇝_ : ∀ {n} {tag}
    (s t : expr-of-type tag n) → 𝒰 ⁺ ⊔ 𝒱 ᵖ
  where
  β-exact : ∀ {n} {s t : Elim n}
    (β : s ⇝β t)
    → -------------
    s ⇝ t

  v-exact : ∀ {n} {s t : Term n}
    (v : s ⇝v t)
    → -------------
    s ⇝ t

  hole : ∀ {m n} {tag₁ tag₂} {s t}
    (C[—] : 1-hole-ctx tag₁ m tag₂ n)
    (reduct : s ⇝ t)
    → --------------------
    C[—] [ s /—] ⇝ C[—] [ t /—]

open import Foundation.Relation.Binary.ReflexiveTransitiveClosure
  using (refl-trans-close)

infix 36 _↠_
_↠_ : ∀ {n} {tag}
  (e₁ : expr-of-type tag n)
  (e₂ : expr-of-type tag n)
  → --------------------
  𝒰 ⁺ ⊔ 𝒱 ᵖ
_↠_ = refl-trans-close _⇝_
