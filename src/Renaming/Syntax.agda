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

prevRenUnsafe : ∀ {m} → Ren (m +2) (m +1)
prevRenUnsafe new = new
prevRenUnsafe (old v) = v

open import Data.List hiding (index; _++_)
open import Data.List.Functor
open import Collection
open import Data.Monad

prevSafe : Var (m +1) → List (Var m)
prevSafe new = []
prevSafe (old v) = [ v ]

fv : ∀ {m} {tag}
  (e : expr-of-type tag m)
  → -----------------------
  List (Var m)
fv {tag = term} (⋆ i) = []
fv {tag = term} ([ _ x: S ]→ T) = fv S ++ (fv T >>= prevSafe)
fv {tag = term} (λx, t) = fv t >>= prevSafe
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
  (e : expr-of-type tag (m +1))
  (p : n < m +1)
  (q : nth-var n p ∉ fv e)
  → ------------------------------
  expr-of-type tag m

open import Data.Functor

del-nth-aux :
  ∀ {m n p} {l : List (Var (m +2))}
  (q : old (nth-var n p) ∈ l)
  → ---------------------------------------------------
  nth-var n p ∈ (l >>= prevSafe)
del-nth-aux (x∈x∷ _) = x∈x∷ _
del-nth-aux {m}{n}{p}(x∈tail new q) = del-nth-aux {n = n}{p} q
del-nth-aux {m}{n}{p}(x∈tail (old h) q) =
  x∈tail h (del-nth-aux {n = n}{p} q)

open import Proposition.Comparable
open import Data.Nat.Proof
delVar : ∀ {m}
  (n : ℕ)
  (v : Var (m +1))
  (p : n < m +1)
  (q : nth-var n p ≠ v)
  → --------------------
  Var m
delVar zero new p q = ⊥-recursion _ (q (Id-refl new))
delVar zero (old v) p q = v
delVar {zero}(n +1) new p q = ⊥-recursion _ (¬-<0 n $ s<s→-<- p)
delVar {m +1}(n +1) new p q = new
delVar {m +1}(n +1) (old v) p q =
  old (delVar n v (s<s→-<- p) λ x → q $ ap old x)

del-nth n {term} (⋆ i) p q = ⋆ i
del-nth n {term} ([ ρ x: S ]→ T) p q =
  [ ρ x:
  del-nth n S p (λ q' → q $ ⟵ (++-prop {l' = lₜ}) $ ∨left q') ]→
  del-nth (suc n) T (s<s p)
    (λ q' → q $ ⟵ (++-prop {l = fv S}) $ ∨right $ del-nth-aux {n = n}{p} q')
  where lₜ = fv T >>= prevSafe
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
  var (delVar n v p λ nth==v → q $ Id.subst (_∈ [ v ]) (sym nth==v) $ x∈x∷ [])

del-nth== : ∀ {tag tag' m m' n n'}
  {e : expr-of-type tag (m +1)}
  {e' : expr-of-type tag' (m' +1)}
  {p q}
  (eq₀ : tag == tag')
  (eq₁ : m == m')
  (eq₂ : n == n')
  (eq₃ : e Het.== e')
  → ------------------------------
  let p' = Id.coe (ap2 _<_ eq₂ $ ap suc eq₁) p
      q' :
        (eq₀ : tag == tag')
        (eq₁ : m == m')
        (eq₂ : n == n')
        (eq₃ : e Het.== e')
        → --------------------
        nth-var n' p' ∉ fv e'
      q' = λ {(Id-refl tag)(Id-refl m)(Id-refl n)(Het.refl e) → q}
  in
  del-nth n e p q
  Het.==
  del-nth n' e' p' (q' eq₀ eq₁ eq₂ eq₃)
del-nth== (Id-refl tag)(Id-refl m)(Id-refl n)(Het.refl e) =
  Het.refl (del-nth n e _ _)
