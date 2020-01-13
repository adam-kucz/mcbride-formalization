{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import Basic using (Rig; wfs)
open import PropUniverses

module Substitution
  {𝑅 : 𝒰 ˙} ⦃ r : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Syntax
open import Liftable
open import Renaming ⦃ r ⦄ ⦃ 𝑤𝑓𝑠 ⦄

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

open import Proposition.Empty
open import Proposition.Comparable
open import Relation.Binary hiding (_~_)
open import Logic hiding (⊥-recursion)
open import Proof
open import Data.Nat.Proof

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

open import Function hiding (_$_)

lift-nthSub~ : ∀ {n} m (p : m < suc n) (f : Elim n)
  → -----------------------------------------------------
  lift (nthSub m p f) ~ nthSub (suc m) (s<s p) (shift f)
lift-nthSub~ m p f new = refl (var new)
lift-nthSub~ m p f (old v) with compare (index v) _<_ m ⦃ Comparableℕ ⦄
lift-nthSub~ m p f (old v) | lt _ = refl (var (old (contract v _)))
lift-nthSub~ m p f (old v) | eq _ = refl (shift f)
lift-nthSub~ m p f (old (old v)) | gt _ = refl (var (old v))

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

postulate
  rename-[-/new] : ∀ {m n} {tag}
    (ρ : Ren m n)
    (e : expr-of-type tag (suc m))
    (f : Elim m)
    → --------------------------------------------------------------
    rename ⦃ RenameableExpr ⦄ ρ (e [ f /new])
    ==
    rename (lift ρ) e [ rename ρ f /new]
-- rename-[-/new] = rename-sub-new 0

open import Proposition.Identity renaming (Idₚ to Id) hiding (refl)
open import Data.Collection
open import Data.List hiding (index)
open import Data.Functor
open import Axiom.FunctionExtensionality

nthSub-trivial : ∀ {m n} {tag}
  (e : expr-of-type tag (suc m))
  (f : Elim m)
  (p : n < suc m)
  (q : nth-var n p ∉ fv e)
  → ------------------------------
  sub (nthSub n p f) e == del-nth n e p q
nthSub-trivial {tag = term} (⋆ i) f p q = refl (⋆ i)
nthSub-trivial {n = n}{term} ([ ρ x: S ]→ T) f p q =
  proof [ ρ x: sub (nthSub n p f) S ]→ sub (lift (nthSub n p f)) T
    〉 _==_ 〉 [ ρ x: del-nth n S p _ ]→ sub (lift (nthSub n p f)) T
      :by: ap ([ ρ x:_]→ sub (lift (nthSub n p f)) T) $
           nthSub-trivial S f p (λ q' → q $
             ⟵ (++-prop {l' = prevRenUnsafe <$> remove new (fv T)}) $
             ∨left q')
    〉 _==_ 〉 [ ρ x: del-nth n S p _ ]→ sub (nthSub (suc n) _ (shift f)) T
      :by: ap (λ — → [ ρ x: del-nth n S p q₁ ]→ sub — T) $
           fun-ext $
           lift-nthSub~ n p f
    〉 _==_ 〉 [ ρ x: del-nth n S p _ ]→ del-nth (suc n) T (s<s p) _
      :by: ap ([ ρ x: del-nth n S p q₁ ]→_) $
           nthSub-trivial T (shift f) (s<s p) q'           
  qed
  where q₁ : nth-var n p ∉ fv S
        q₁ q' = q $
          ⟵ (++-prop {l' = prevRenUnsafe <$> remove new (fv T)}) $
          ∨left q'
        q' : old (nth-var n p) ∉ fv T
        q' v∈T = q $
          ⟵ (++-prop {l = fv S}) $
          ∨right $
          ∈fmap prevRenUnsafe $
          ⟵ remove-valid (v∈T , λ ())
nthSub-trivial {n = n}{term} (λx, t) f p q =
  ap λx,_ (
    proof sub (lift (nthSub n p f)) t
      〉 _==_ 〉 sub (nthSub (suc n) _ (shift f)) t
        :by: ap (λ — → sub — t) $ fun-ext $ lift-nthSub~ n p f
      〉 _==_ 〉 del-nth (suc n) t (s<s p) _
        :by: nthSub-trivial t (shift f) (s<s p) q'
    qed)
  where q' : old (nth-var n p) ∉ fv t
        q' v∈t = q $ ∈fmap prevRenUnsafe $ ⟵ remove-valid (v∈t , λ ())
nthSub-trivial {tag = term} ⌊ e ⌋ f p q = ap ⌊_⌋ (nthSub-trivial e f p q)
nthSub-trivial {n = n}{elim} (var v) f p q
  with compare (index v) _<_ n  ⦃ Comparableℕ ⦄
nthSub-trivial {n = n} {elim} (var v) f p q | lt p₁ = refl (var (contract v _))
nthSub-trivial {n = n} {elim} (var v) f p q | eq (Id.refl _) =
  ⊥-recursionₚ (f == _) $
    q $
    Id.transport (_∈ [ v ]) (⟵ Var== $ sym $ index-nth-var (index v) p) $
    x∈x∷ []
nthSub-trivial {n = n} {elim} (var (old v)) f p q | gt _ = refl (var v)
nthSub-trivial {tag = elim} (f ` s) f' p q = -`-eq
  (nthSub-trivial f f' p λ p' → q $ ⟵ (++-prop {l' = fv s}) $ ∨left p')
  (nthSub-trivial s f' p λ p' → q $ ⟵ (++-prop {l = fv f}) $ ∨right p')
  where -`-eq : ∀ {m} {f f' : Elim m} {s s'} (p : f == f') (q : s == s')
          → -----------------------------------------------------------
          f ` s == f' ` s'
        -`-eq (Id.refl f) (Id.refl s) = refl (f ` s)
nthSub-trivial {tag = elim} (s ꞉ S) f p q =  -꞉-eq
  (nthSub-trivial s f p λ p' → q $ ⟵ (++-prop {l' = fv S}) $ ∨left p')
  (nthSub-trivial S f p λ p' → q $ ⟵ (++-prop {l = fv s}) $ ∨right p')
  where -꞉-eq : ∀ {m} {s s' S S' : Term m} (p : s == s') (q : S == S')
          → -----------------------------------------------------------
          s ꞉ S == s' ꞉ S'
        -꞉-eq (Id.refl s) (Id.refl S) = refl (s ꞉ S)

-- lift (nthSub m p f) ~ nthSub (suc m) (s<s p) (shift f)
-- sub (lift (nthSub 0 z<s (sub σ f))) (sub (lift (lift σ)) e)
--   == sub (lift σ) (sub (lift (nthSub 0 z<s f)) e)

-- (sub (nthSub 1 (s<s z<s) (shift-by 1 (sub σ f))) ∘ (sub (lift-by 2 σ)) e
--   == (sub (lift-by 1 σ) ∘ sub (nthSub 1 (s<s z<s) (shift-by 1 f))) e

-- Hypothesis:
-- (sub (nthSub n (s<s z<s) (shift-by n (sub σ f))) ∘ (sub (lift-by (suc n) σ)) e
--   == (sub (lift-by n σ) ∘ sub (nthSub n (s<s z<s) (shift-by n f))) e

open import Function.Proof

sub-commute : ∀ {m n k : ℕ} {tag}
  (σ : Sub m n)
  (e : expr-of-type tag (suc k + m))
  (f : Elim m)
  → ------------------------------------------------------
  let p = λ m → (proof k
          〉 _≤_ 〉 k + m     :by: postfix (_+ m) k
          〉 _<_ 〉 suc k + m :by: postfix suc (k + m)
        qed) in
  (sub (nthSub k (p n) (shift-by k (sub σ f))) ∘ sub (lift-by (suc k) σ)) e
    == (sub (lift-by k σ) ∘ sub (nthSub k (p m) (shift-by k f))) e
  -- (sub (nthSub k (p n) (shift-by k (sub σ f))) ∘ sub (lift-by (suc k) σ)) e : E (k + n)
  -- (sub (lift-by (suc k) σ)) e : E (suc k+ n)

  -- == (sub (lift-by k σ) ∘ sub (nthSub k p (shift-by k f))) e

  -- (sub (nthSub k p (shift-by k (sub σ f))) ∘ sub (lift-by (suc k) σ)) e
  --   == (sub (lift-by k σ) ∘ sub (nthSub k p (shift-by k f))) e
 -- (sub (nthSub 0 z<s (sub σ f)) ∘ sub (lift σ)) e == (sub σ ∘ sub (nthSub 0 z<s f)) e
-- sub-commute {tag = term} σ (⋆ i) f = refl (⋆ i)
-- sub-commute {tag = term} σ ([ ρ x: S ]→ T) f = {!!}
-- sub-commute {tag = term} σ (λx, e) f = ap λx,_ {!!}
-- sub-commute {tag = term} σ ⌊ e ⌋ f = ap ⌊_⌋ $ sub-commute σ e f
-- sub-commute {tag = elim} σ (var new) f = refl (sub σ f)
-- sub-commute {n = n} {tag = elim} σ (var (old v)) f = {!!}
-- sub-commute {tag = elim} σ (f ` s) f' =
--   proof (sub (lift σ) (f ` s)) [ sub σ f' /new]
--     〉 _==_ 〉 sub (lift σ) f [ sub σ f' /new] ` sub (lift σ) s [ sub σ f' /new] 
--       :by: Id.refl _
--     〉 _==_ 〉 sub σ (f [ f' /new]) ` sub (lift σ) s [ sub σ f' /new] 
--       :by: ap (_` sub (lift σ) s [ sub σ f' /new] ) $
--            sub-commute σ f f'
--     〉 _==_ 〉 sub σ (f [ f' /new]) ` sub σ (s [ f' /new])
--       :by: ap (sub σ (f [ f' /new]) `_) $ sub-commute σ s f'
--     〉 _==_ 〉 sub σ ((f ` s) [ f' /new])
--       :by: Id.refl _
--   qed
-- sub-commute {tag = elim} σ (s ꞉ S) f = 
--   proof (sub (lift σ) (s ꞉ S)) [ sub σ f /new]
--     〉 _==_ 〉 sub (lift σ) s [ sub σ f /new] ꞉ sub (lift σ) S [ sub σ f /new] 
--       :by: Id.refl _
--     〉 _==_ 〉 sub σ (s [ f /new]) ꞉ sub (lift σ) S [ sub σ f /new] 
--       :by: ap (_꞉ sub (lift σ) S [ sub σ f /new] ) $
--            sub-commute σ s f
--     〉 _==_ 〉 sub σ (s [ f /new]) ꞉ sub σ (S [ f /new])
--       :by: ap (sub σ (s [ f /new]) ꞉_) $ sub-commute σ S f
--     〉 _==_ 〉 sub σ ((s ꞉ S) [ f /new])
--       :by: Id.refl _
--   qed

