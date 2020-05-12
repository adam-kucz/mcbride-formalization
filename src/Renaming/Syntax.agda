{-# OPTIONS --exact-split --prop #-}
open import Basic using (Rig; wfs)
open import PropUniverses

module Renaming.Syntax
  {𝑅 : 𝒰 ˙} ⦃ rig : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Renaming.Definition

open import Syntax.Definition
open import Data.Nat
open import Liftable.Definition

prevRenUnsafe : ∀ {m} → Ren (suc (suc m)) (suc m)
prevRenUnsafe new = new
prevRenUnsafe (old v) = v

open import Data.List hiding (index; _++_)
open import Data.List.Functor
open import Collection
open import Data.Functor

fv : ∀ {m} {tag}
  (e : expr-of-type tag m)
  → -----------------------
  List (Var m)
fv {tag = term} (⋆ i) = []
fv {zero} {term} ([ _ x: S ]→ T) = fv S
fv {suc m} {term} ([ _ x: S ]→ T) =
  fv S ++ (prevRenUnsafe <$> remove new (fv T))
fv {zero} {term} (λx, e) = []
fv {suc m} {term} (λx, e) =
  prevRenUnsafe <$> remove new (fv e)
fv {tag = term} ⌊ e ⌋ = fv e
fv {tag = elim} (var v) = [ v ]
fv {tag = elim} (f ` s) = fv f ++ fv s
fv {tag = elim} (s ꞉ S) = fv s ++ fv S

open import Proposition.Empty
open import Proposition.Identity hiding (refl)
open import Logic hiding (⊥-recursion)
open import Proof

-- shift-var : ∀ k {m} (v : Var m) →
--   shift-by k (var v) == var (shift-by k v)
-- shift-var zero v = refl (var v)
-- shift-var (k +1) v = ap shift $ shift-var k v

-- shift-star : ∀ k {n} i  →
--   shift-by k (⋆ {n} i) == ⋆ {k + n} i
-- shift-star zero i = refl (⋆ i)
-- shift-star (k +1) i = ap shift $ shift-star k i

del-nth : ∀ {m} n {tag}
  (e : expr-of-type tag (suc m))
  (p : n < suc m)
  (q : nth-var n p ∉ fv e)
  → ------------------------------
  expr-of-type tag m

private
  del-nth-aux :
    ∀ {m n p} {l : List (Var (m +2))}
    (q : old (nth-var n p) ∈ l)
    → ---------------------------------------------------
    nth-var n p ∈ (prevRenUnsafe <$> remove new l)
  del-nth-aux (x∈x∷ _) = x∈x∷ _
  del-nth-aux {m}{n}{p}(x∈tail new q) = del-nth-aux {n = n}{p} q
  del-nth-aux {m}{n}{p}(x∈tail (old h) q) =
    x∈tail h (del-nth-aux {n = n}{p} q)

del-nth n {term} (⋆ i) p q = ⋆ i
del-nth n {term} ([ ρ x: S ]→ T) p q =
  [ ρ x:
  del-nth n S p (λ q' → q $ ⟵ (++-prop {l' = lₜ}) $ ∨left q') ]→
  del-nth (suc n) T (s<s p)
    (λ q' → q $ ⟵ (++-prop {l = fv S}) $ ∨right $ del-nth-aux {n = n}{p} q')
  where lₜ = prevRenUnsafe <$> remove new (fv T)
del-nth n {term} (λx, t) p q =
  λx, del-nth (suc n) t (s<s p)
    λ q' → q $ del-nth-aux {n = n}{p} q'
del-nth n {term} ⌊ e ⌋ p q = ⌊ del-nth n e p q ⌋
del-nth n {elim} (f ` s) p q =
  del-nth n f p (λ q' → q $ ⟵ (++-prop {l' = fv s}) $ ∨left q') `
  del-nth n s p (λ q' → q $ ⟵ (++-prop {l = fv f}) $ ∨right q')
del-nth n {elim} (s ꞉ S) p q =
  del-nth n s p (λ q' → q $ ⟵ (++-prop {l' = fv S}) $ ∨left q') ꞉
  del-nth n S p (λ q' → q $ ⟵ (++-prop {l = fv s}) $ ∨right q')
del-nth n {elim} (var v) p q =
  var (delVar n v p
    λ nth==v → q $ Id.subst (_∈ [ v ]) (sym nth==v) $ x∈x∷ [])
  where open import Proposition.Comparable
        open import Data.Nat.Proof
        delVar : ∀ {m}
          (n : ℕ)
          (v : Var (m +1))
          (p : n < m +1)
          (q : nth-var n p ≠ v)
          → --------------------
          Var m
        delVar n v p q with compare (index v) _<_ n
        delVar {m} n v p q | lt p₁ = contract v (
          proof index v
            〉 _<_ 〉 n :by: p₁
            〉 _≤_ 〉 m :by: ap pred $ ⟶ -<-↔s≤- p
          qed)
        delVar {m} n v p q | eq p₁ = ⊥-recursion (Var m) (q $ ⟵ Var== (
            proof index (nth-var n p)
              〉 _==_ 〉 n       :by: index-nth-var n p
              〉 _==_ 〉 index v :by: sym p₁
            qed))
        delVar n new p q | gt r = ⊥-recursion _ (irrefl 0 (
          proof 0
            〉 _≤_ 〉 n :by: z≤ n
            〉 _<_ 〉 0 :by: r
          qed))
          where open import Relation.Binary
        delVar n (old v) p q | gt _ = v
