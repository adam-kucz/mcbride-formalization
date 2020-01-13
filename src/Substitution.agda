{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import Basic using (Rig; wfs)
open import PropUniverses

module Substitution
  {𝑅 : 𝒰 ˙} ⦃ r : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Syntax
open import Liftable
open import Renaming

open import Data.Nat
open import Type.Identity using (transport; transport==)

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

newSub : ∀ {n} (f : Elim n) → Sub (suc n) n
newSub f new = f
newSub f (old v) = var v

open import Proposition.Empty

nthSub : ∀ {n} m (p : m < suc n)(f : Elim n) → Sub (suc n) n
nthSub {n} m p f = go m p
  where go : (m : ℕ) (p : m < suc n) → Sub (suc n) n
        go zero p = newSub f
        go (suc m) p = ?


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

open import Proposition.Identity as Identity
  renaming (Idₚ to Id) using (_==_; ap)
open Identity.Id renaming (sym to Id-sym) using ()
open import Proof

-- postulate
--   rename-sub-new : ∀ {m n} k {tag}
--     (ρ : Ren m n)
--     (e : expr-of-type tag (k + suc m))
--     (f : Elim m)
--     → --------------------------------------------------------------
--     rename (lift-many Ren k ρ)
--            (sub (lift-many Sub k (newSub f))
--                 e)
--     ==
--     sub (newSub (extend-by k (rename ρ f)))
--         (rename (lift-many Ren (suc k) ρ)
--                 (transport (Nat.+-suc-transport k m (expr-of-type tag)) e))
-- rename-sub-new {m} {n} k {term} ρ (⋆ i) f =
--   proof ⋆ i
--     〉 _==_ 〉 sub (newSub (wk-left k (rename ρ f)))
--                 (rename (lift-many Ren (suc k) ρ)
--                         (⋆ i))
--       :by: refl (⋆ i)
--     〉 _==_ 〉 sub (newSub (wk-left k (rename ρ f)))
--                 (rename (lift-many Ren (suc k) ρ)
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
--   rename (lift ρ) e [ rename ρ f /new]
-- rename-[-/new] = rename-sub-new 0

open import Data.Collection
open import Data.List

private
  ℕ-cases :
    (A : (m : ℕ) → 𝒳 ˙)
    (x : A 0)
    (f : (m : ℕ) → A (suc m))
    (m : ℕ)
    → -------------------------
    A m
  ℕ-cases _ x _ zero = x
  ℕ-cases _ _ f (suc m) = f m

open import Logic hiding (⊥-recursion)

[-/new]-trivial : ∀ {m} {tag}
  (e : expr-of-type tag (suc m))
  (f : Elim m)
  (p : new {n = m} ∉ fv e)
  → ------------------------------
  e [ f /new] == del-nth 0 e z<s p
[-/new]-trivial {tag = term} (⋆ i) f p = refl (⋆ i)
[-/new]-trivial {tag = term} ([ ρ x: S ]→ T) f p = {!!}
[-/new]-trivial {tag = term} (λx, e) f p = ap λx,_ {!!}
[-/new]-trivial {tag = term} ⌊ e ⌋ f p = ap ⌊_⌋ ([-/new]-trivial e f p)
[-/new]-trivial {tag = elim} (var new) f p = ⊥-recursionₚ _ (p (x∈x∷ []))
[-/new]-trivial {tag = elim} (var (old v)) f p = refl (var v)
[-/new]-trivial {tag = elim} (f ` s) f' p = -`-eq
  ([-/new]-trivial f f' λ p' → p $ ⟵ (++-prop {l' = fv s}) $ ∨left p')
  ([-/new]-trivial s f' λ p' → p $ ⟵ (++-prop {l = fv f}) $ ∨right p')
  where -`-eq : ∀ {m} {f f' : Elim m} {s s'} (p : f == f') (q : s == s')
          → -----------------------------------------------------------
          f ` s == f' ` s'
        -`-eq (Id.refl f) (Id.refl s) = refl (f ` s)
[-/new]-trivial {tag = elim} (s ꞉ S) f p = -꞉-eq
  ([-/new]-trivial s f λ p' → p $ ⟵ (++-prop {l' = fv S}) $ ∨left p')
  ([-/new]-trivial S f λ p' → p $ ⟵ (++-prop {l = fv s}) $ ∨right p')
  where -꞉-eq : ∀ {m} {s s' S S' : Term m} (p : s == s') (q : S == S')
          → -----------------------------------------------------------
          s ꞉ S == s' ꞉ S'
        -꞉-eq (Id.refl s) (Id.refl S) = refl (s ꞉ S)

sub-commute : ∀ {m n} {tag}
  (σ : Sub m n)
  (e : expr-of-type tag (suc m))
  (f : Elim m)
  → ------------------------------------------------------
  (sub (lift σ) e) [ sub σ f /new] == sub σ (e [ f /new])
sub-commute {tag = term} σ (⋆ i) f = refl (⋆ i)
sub-commute {tag = term} σ ([ ρ x: S ]→ T) f = {!!}
sub-commute {tag = term} σ (λx, e) f = {!!}
sub-commute {tag = term} σ ⌊ e ⌋ f = ap ⌊_⌋ $ sub-commute σ e f
sub-commute {tag = elim} σ (var new) f = refl (sub σ f)
sub-commute {n = n} {elim} σ (var (old v)) f = {!!}
sub-commute {tag = elim} σ (f ` s) f' =
  proof (sub (lift σ) (f ` s)) [ sub σ f' /new]
    〉 _==_ 〉 sub (lift σ) f [ sub σ f' /new] ` sub (lift σ) s [ sub σ f' /new] 
      :by: Id.refl _
    〉 _==_ 〉 sub σ (f [ f' /new]) ` sub (lift σ) s [ sub σ f' /new] 
      :by: ap (_` sub (lift σ) s [ sub σ f' /new] ) $
           sub-commute σ f f'
    〉 _==_ 〉 sub σ (f [ f' /new]) ` sub σ (s [ f' /new])
      :by: ap (sub σ (f [ f' /new]) `_) $ sub-commute σ s f'
    〉 _==_ 〉 sub σ ((f ` s) [ f' /new])
      :by: Id.refl _
  qed
sub-commute {tag = elim} σ (s ꞉ S) f = 
  proof (sub (lift σ) (s ꞉ S)) [ sub σ f /new]
    〉 _==_ 〉 sub (lift σ) s [ sub σ f /new] ꞉ sub (lift σ) S [ sub σ f /new] 
      :by: Id.refl _
    〉 _==_ 〉 sub σ (s [ f /new]) ꞉ sub (lift σ) S [ sub σ f /new] 
      :by: ap (_꞉ sub (lift σ) S [ sub σ f /new] ) $
           sub-commute σ s f
    〉 _==_ 〉 sub σ (s [ f /new]) ꞉ sub σ (S [ f /new])
      :by: ap (sub σ (s [ f /new]) ꞉_) $ sub-commute σ S f
    〉 _==_ 〉 sub σ ((s ꞉ S) [ f /new])
      :by: Id.refl _
  qed
