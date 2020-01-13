{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import Basic using (Rig; wfs)
open import PropUniverses

module Substitution.Property
  {𝑅 : 𝒰 ˙} ⦃ r : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Substitution.Definition

open import Syntax
open import Liftable
open import Renaming ⦃ r ⦄ ⦃ 𝑤𝑓𝑠 ⦄
open import Data.Nat
open import Data.Nat.Proof
open import Proposition.Comparable
open import Function using (_~_; _∘_)
open import Logic
open import Proof

lift-nthSub~ : ∀ {n} m (p : m < suc n) (f : Elim n)
  → -----------------------------------------------------
  lift (nthSub m p f) ~ nthSub (suc m) (s<s p) (shift f)
lift-nthSub~ m p f new = refl (var new)
lift-nthSub~ m p f (old v) with compare (index v) _<_ m ⦃ Comparableℕ ⦄
lift-nthSub~ m p f (old v) | lt _ = refl (var (old (contract v _)))
lift-nthSub~ m p f (old v) | eq _ = refl (shift f)
lift-nthSub~ m p f (old (old v)) | gt _ = refl (var (old v))

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
  ⊥-recursion (f == _) $
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

sub-lift-shift : ∀ {m n} k {tag}
  (e : expr-of-type tag m)
  (σ : Sub m n)
  → -------------------------------------------------------
  sub (lift-by k σ) (shift-by k e) == shift-by k (sub σ e)
sub-lift-shift k {term} (⋆ i) σ =
  proof sub (lift-by k σ) (shift-by k (⋆ i))
    〉 _==_ 〉 ⋆ i :by: ap (sub (lift-by k σ)) $ lemma k
    〉 _==_ 〉 shift-by k (⋆ i) :by: Id.sym $ lemma k
  qed
  where lemma : ∀ {n} k → shift-by k (⋆ {n = n} i) == ⋆ {n = k + n} i
        lemma zero = refl (⋆ i)
        lemma (suc k) = ap shift (lemma k)
sub-lift-shift k {term} ([ ρ x: e ]→ e₁) σ = {!!}
sub-lift-shift k {term} (λx, e) σ = {!!}
sub-lift-shift k {term} ⌊ e ⌋ σ = {!!}
sub-lift-shift k {elim} (e ` s) σ = {!!}
sub-lift-shift k {elim} (s ꞉ S) σ = {!!}
sub-lift-shift 0 {elim} (var v) σ = refl (σ v)
sub-lift-shift 1 {elim} (var v) σ = refl (shift (σ v))
sub-lift-shift (k +2) {elim} (var v) σ =
  proof sub (lift-by (k +2) σ) (shift-by (k +2) (var v))
    〉 _==_ 〉 shift-by (k +2) (σ v)
      :by: {!!}
  qed
-- sub (lift (lift-by k σ)) (shift (shift-by k (var v))) == shift (shift-by k (σ v))

sub-commute : ∀ {m n k : ℕ} {tag}
  (σ : Sub m n)
  (e : expr-of-type tag (suc k + m))
  (f : Elim m)
  (p : (x : ℕ) → k < suc k + x)
  → ------------------------------------------------------
  let shft-exp-by = λ {m} {tag} → shift-by {m = m} ⦃ RenameableExpr {tag} ⦄ in
  sub (nthSub k (p n) (shft-exp-by k (sub σ f)))
    (sub (lift-by (suc k) σ) e)
      ==
  sub (lift-by k σ)
    (sub (nthSub k (p m) (shft-exp-by k f)) e)
sub-commute {tag = term} σ (⋆ i) f p = refl (⋆ i)
sub-commute {tag = term} σ ([ ρ x: S ]→ T) f p = {!!}
sub-commute {tag = term} σ (λx, t) f p = {!!}
sub-commute {tag = term} σ ⌊ e ⌋ f p = {!!}
sub-commute {tag = elim} σ (var v) f p = {!!}
--  sub (nthSub k (p n) (shift-by k (sub σ f)))
--    (lift-by (suc k) σ v)
--    == sub (lift-by k σ) (nthSub k (p m) (shift-by k f) v)

-- case index v == k
--   sub (nthSub k (p n) (shift-by k (sub σ f)))
--    (lift-by (suc k) σ v)
--    == sub (lift-by k σ) (shift-by k f)


sub-commute {tag = elim} σ (f' ` s) f p = {!!}
sub-commute {tag = elim} σ (s ꞉ S) f p = {!!}

-- p = λ m → (proof k
--           〉 _≤_ 〉 k + m     :by: postfix (_+ m) k
--           〉 _<_ 〉 suc k + m :by: postfix suc (k + m)
--         qed)
        
