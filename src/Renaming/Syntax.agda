{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import Basic using (Rig; wfs)
open import PropUniverses

module Renaming.Syntax
  {𝑅 : 𝒰 ˙} ⦃ r : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Renaming.Definition

open import Syntax
open import Data.Nat
open import Liftable

instance
  RenameableVar : Renameable Var
  rename ⦃ RenameableVar ⦄ ρ v = ρ v

  RenameableTerm : Renameable Term
  RenameableElim : Renameable Elim
  rename ⦃ RenameableTerm ⦄ ρ (⋆ i) = ⋆ i
  rename ⦃ RenameableTerm ⦄ ρ ([ π x: S ]→ T) =
    [ π x: rename ρ S ]→ rename (lift ρ) T
  rename ⦃ RenameableTerm ⦄ ρ (λx, t) = λx, rename (lift ρ) t
  rename ⦃ RenameableTerm ⦄ ρ ⌊ e ⌋ = ⌊ rename ρ e ⌋
  rename ⦃ RenameableElim ⦄ ρ (var v) = var (rename ρ v)
  rename ⦃ RenameableElim ⦄ ρ (f ` s) = rename ρ f ` rename ρ s
  rename ⦃ RenameableElim ⦄ ρ (s ꞉ S) = rename ρ s ꞉ rename ρ S

  RenameableExpr : ∀ {tag} → Renameable (expr-of-type tag)
  RenameableExpr {term} = RenameableTerm
  RenameableExpr {elim} = RenameableElim

prevRenUnsafe : ∀ {m} → Ren (suc (suc m)) (suc m)
prevRenUnsafe new = new
prevRenUnsafe (old v) = v

open import Data.List hiding (index)
open import Data.Collection
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

del-nth : ∀ {m} n {tag}
  (e : expr-of-type tag (suc m))
  (p : n < suc m)
  (q : nth-var n p ∉ fv e)
  → ------------------------------
  expr-of-type tag m

private
  del-nth-aux :
    ∀ {m n p} {l : List (Var (suc (suc m)))}
    (q : old (nth-var n p) ∈ l)
    → ---------------------------------------------------
    nth-var n p ∈ (prevRenUnsafe <$> remove new l)
  del-nth-aux (x∈x∷ _) = x∈x∷ _
  del-nth-aux (x∈tail new q) = del-nth-aux q
  del-nth-aux (x∈tail (old h) q) = x∈tail h (del-nth-aux q)

del-nth n {term} (⋆ i) p q = ⋆ i
del-nth n {term} ([ ρ x: S ]→ T) p q =
  [ ρ x:
  del-nth n S p (λ q' → q $ ⟵ (++-prop {l' = lₜ}) $ ∨left q') ]→
  del-nth (suc n) T (s<s p)
    (λ q' → q $ ⟵ (++-prop {l = fv S}) $ ∨right $ del-nth-aux q')
  where lₜ = prevRenUnsafe <$> remove new (fv T)
del-nth n {term} (λx, t) p q =
  λx, del-nth (suc n) t (s<s p)
    λ q' → q $ del-nth-aux q'
del-nth n {term} ⌊ e ⌋ p q = ⌊ del-nth n e p q ⌋
del-nth n {elim} (f ` s) p q =
  del-nth n f p (λ q' → q $ ⟵ (++-prop {l' = fv s}) $ ∨left q') `
  del-nth n s p (λ q' → q $ ⟵ (++-prop {l = fv f}) $ ∨right q')
del-nth n {elim} (s ꞉ S) p q =
  del-nth n s p (λ q' → q $ ⟵ (++-prop {l' = fv S}) $ ∨left q') ꞉
  del-nth n S p (λ q' → q $ ⟵ (++-prop {l = fv s}) $ ∨right q')
del-nth n {elim} (var v) p q =
  var (delVar n v p
    λ nth==v → q $ Id.transport (_∈ [ v ]) (Id.sym nth==v) $ x∈x∷ [])
  where open import Proposition.Comparable
        open import Data.Nat.Proof
        delVar : ∀ {m}
          (n : ℕ)
          (v : Var (suc m))
          (p : n < suc m)
          (q : nth-var n p ≠ v)
          → --------------------
          Var m
        delVar n v p q with compare (index v) _<_ n
        delVar {m} n v p q | lt p₁ = contract v (
          proof index v
            〉 _<_ 〉 n :by: p₁
            〉 _≤_ 〉 m :by: ⟵ -≤-↔-<s p
          qed)
        delVar {m} n v p q | eq p₁ = ⊥-recursion (Var m) (q $ ⟵ Var== (
            proof index (nth-var n p)
              〉 _==_ 〉 n       :by: index-nth-var n p
              〉 _==_ 〉 index v :by: sym p₁
            qed))
        delVar n (old v) p q | gt _ = v
