{-# OPTIONS --exact-split --prop --safe #-}
open import TypeTheory.Basic using (Rig; wfs)
open import Foundation.PropUniverses

module TypeTheory.Substitution
  {𝑅 : 𝒰 ˙} ⦃ r : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import TypeTheory.Syntax as Syntax
  using (Var; Elim; Term; ExprTag; expr-of-type)
open Var; open Elim; open Term; open ExprTag
open import Foundation.Data.Nat as Nat
  using (ℕ; zero; suc; _+_)

-- types that take and return variable-indexed objects
-- which can be lifted to operate on more variables
-- while being identity on the newly introduced ones
record Liftable (f : (m n : ℕ) → 𝒵 ˙) : 𝒵 ˙ where
  field
    lift : ∀ {m n} (ρ : f m n) → f (suc m) (suc n)

open Liftable ⦃ … ⦄ public

lift-many : ∀ {m n}
  (f : (m n : ℕ) → 𝒵 ˙)
  ⦃ _ : Liftable f ⦄
  (k : ℕ)
  (e : f m n)
  → -----------------------
  f (k + m) (k + n)
lift-many f zero e = e
lift-many f (suc k) e = lift (lift-many f k e)

-- type  of renamings of variables
Ren : (m n : ℕ) → 𝒰₀ ˙
Ren m n = (v : Var m) → Var n

instance
  LiftableRen : Liftable Ren
  lift ⦃ LiftableRen ⦄ ρ new = new
  lift ⦃ LiftableRen ⦄ ρ (old v) = old (ρ v)

-- identity renaming allowing the result to have more variables
idRen1 : (m : ℕ) → Ren m (suc m)
idRen1 (suc m) new = new
idRen1 (suc m) (old v) = old (idRen1 m v)

-- rename variables in an expression according to Ren
-- (capture avoiding)
rename : ∀ {m n} (ρ : Ren m n) {tag}
  (e : expr-of-type tag m) → expr-of-type tag n
rename ρ {term} (⋆ i) = ⋆ i
rename ρ {term} ([ ρ₁ x: S ]→ T) = [ ρ₁ x: rename ρ S ]→ rename (lift ρ) T
rename ρ {term} (λx, t) = λx, rename (lift ρ) t
rename ρ {term} ⌊ e ⌋ = ⌊ rename ρ e ⌋
rename ρ {elim} (var x) = var (ρ x)
rename ρ {elim} (f ` s) = rename ρ f ` rename ρ s
rename ρ {elim} (s ꞉ S) = rename ρ s ꞉ rename ρ S

open import Foundation.Type.Identity using (transport; transport==)

record Weakenable (f : (m : ℕ) → 𝒵 ˙) : 𝒵 ˙ where
  field
    wk1 : ∀ {m} (e : f m) → f (suc m)    

  wk-left : ∀ n {m} (e : f m) → f (n + m)
  wk-left zero e = e
  wk-left (suc n) e = wk1 (wk-left n e)

  wk-right : ∀ n {m} (e : f m) → f (m + n)
  wk-right n {m} e = transport (Nat.comm-transport n m f) (wk-left n e)

open Weakenable ⦃ … ⦄ public

instance
  WeakenableVar : Weakenable Var
  wk1 ⦃ WeakenableVar ⦄ new = new
  wk1 ⦃ WeakenableVar ⦄ (old v) = old (wk1 v)

  WeakenableTerm : Weakenable Term
  WeakenableElim : Weakenable Elim

  wk1 ⦃ WeakenableTerm ⦄ (⋆ i) = ⋆ i
  wk1 ⦃ WeakenableTerm ⦄ ([ ρ x: S ]→ T) = [ ρ x: wk1 S ]→ wk1 T
  wk1 ⦃ WeakenableTerm ⦄ (λx, t) = λx, wk1 t
  wk1 ⦃ WeakenableTerm ⦄ ⌊ e ⌋ = ⌊ wk1 e ⌋

  wk1 ⦃ WeakenableElim ⦄ (var v) = var (wk1 v)
  wk1 ⦃ WeakenableElim ⦄ (f ` s) = wk1 f ` wk1 s
  wk1 ⦃ WeakenableElim ⦄ (s ꞉ S) = (wk1 s) ꞉ (wk1 S)

shift-by : ∀ {m} {tag}
  (n : ℕ)
  (e : expr-of-type tag m)
  → ------------------------------
  expr-of-type tag (n + m)
shift-by zero e = e
shift-by (suc n) e = rename old (shift-by n e)

Sub : (m n : ℕ) → 𝒰 ⁺ ⊔ 𝒱 ˙
Sub m n = (v : Var m) → Elim n

instance
  LiftableSub : Liftable Sub
  lift ⦃ LiftableSub ⦄ σ new = var new
  lift ⦃ LiftableSub ⦄ σ (old v) = shift-by 1 (σ v)
  
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

newSub : ∀ {n} (f : Elim n) → Sub (suc n) n
newSub f new = f
newSub f (old v) = var v

infix 180 _[_/new]
_[_/new] : {n : ℕ} {tag : ExprTag}
  → -------------------------------------------------------------
  (e : expr-of-type tag (suc n)) (f : Elim n) → expr-of-type tag n
_[_/new] {n} e f = sub (newSub f) e

open import Foundation.Prop'.Identity as Identity
  renaming (Idₚ to Id) using (_==_; ap)
open Identity.Id renaming (sym to Id-sym) using ()
open import Foundation.Relation.Binary.Property using (refl; sym)
open import Foundation.Proof
open import Foundation.Prop'.Function using (_$_)

open Nat using (_≤_)
open Syntax using (nth-var)

-- rename-sub-new : ∀ {m n} k {tag}
--   (ρ : Ren m n)
--   (e : expr-of-type tag (k + suc m))
--   (f : Elim m)
--   → --------------------------------------------------------------
--   rename (lift-many Ren k ρ)
--          (sub (lift-many Sub k (newSub f))
--               e)
--   ==
--   sub (newSub (wk-left k (rename ρ f)))
--       (rename (lift-many Ren (suc k) ρ)
--               (transport (Nat.+-suc-transport k m (expr-of-type tag)) e))
-- rename-sub-new {m} {n} k {term} ρ (⋆ i) f =
--   proof ⋆ i
--     〉 _==_ 〉 sub (newSub (wk-left k (rename ρ f)))
--                 (rename (Liftable.lift LiftableRen (lift-many Ren k ρ)) (⋆ i))
--       :by: refl (⋆ i)
--     〉 _==_ 〉 sub (newSub (wk-left k (rename ρ f)))
--                 (rename (Liftable.lift LiftableRen (lift-many Ren k ρ))
--                         (transport (Nat.+-suc-transport k m Term) (⋆ i)))
--       :by: {! ap stuff (Id-sym $ transport== (⋆ i) (Nat.+-suc-transport k m Term))!}
--   qed
--   where stuff : (— : Term (suc k + m)) → Term (k + n)
--         stuff — = sub (newSub (wk-left k (rename ρ f)))
--                       (rename (lift-many Ren (suc k) ρ) —)
-- rename-sub-new k {term} ρ ([ ρ₁ x: e ]→ e₁) f = {!!}
-- rename-sub-new k {term} ρ (λx, e) f = {!!}
-- rename-sub-new k {term} ρ ⌊ e ⌋ f = {!!}
-- rename-sub-new k {elim} ρ e f = {!!}

-- rename-[-/new] : ∀ {m n} {tag}
--   (ρ : Ren m n)
--   (e : expr-of-type tag (suc m))
--   (f : Elim m)
--   → --------------------------------------------------------------
--   rename ρ (e [ f /new])
--   ==
--   (rename (lift ρ) e) [ rename ρ f /new]
-- rename-[-/new] = rename-sub-new 0
