{-# OPTIONS --exact-split #-}
open import Basic using (Rig; wfs)
open import Universes

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

open import Logic
open import Proof

-- shift-var : ∀ k {m} (v : Var m) →
--   shift-by k (var v) == var (shift-by k v)
-- shift-var zero v = refl (var v)
-- shift-var (k +1) v = ap shift $ shift-var k v

-- shift-star : ∀ k {n} i  →
--   shift-by k (⋆ {n} i) == ⋆ {k + n} i
-- shift-star zero i = refl (⋆ i)
-- shift-star (k +1) i = ap shift $ shift-star k i

private
  ap-suc = ap suc ⦃ Relating-+-left-≤ ⦄

open import Data.Maybe
open import Data.Maybe.Functor

-- (p : n ≤ m)
-- (q : nth-var n (ap-suc p) ∉ fv e)
del-nth : ∀{m}(n : ℕ){tag}
  (e : expr-of-type tag (m +1))
  → ------------------------------
  Maybe (expr-of-type tag m)

open import Data.Functor

-- del-nth-aux :
--   ∀ {m n p} {l : List (Var (m +2))}
--   (q : old (nth-var n p) ∈ l)
--   → ---------------------------------------------------
--   nth-var n p ∈ (l >>= prevSafe)
-- del-nth-aux (x∈x∷ _) = x∈x∷ _
-- del-nth-aux {m}{n}{p}(x∈tail new q) = del-nth-aux {n = n}{p} q
-- del-nth-aux {m}{n}{p}(x∈tail (old h) q) =
--   x∈tail h (del-nth-aux {n = n}{p} q)

delVar : ∀ {m}
  (n : ℕ)
  (v : Var (m +1))
  → --------------------
  Maybe (Var m)
delVar zero new = nothing
delVar zero (old v) = just v
delVar {zero}(n +1) new = nothing
delVar {m +1}(n +1) new = just new
delVar {m +1}(n +1) (old v) = old <$> delVar n v

open import Data.Applicative

del-nth n {term} (⋆ i) = just $ ⋆ i
del-nth n {term} ([ ρ x: S ]→ T) = [ ρ x:_]→_ <$> del-nth n S ⍟ del-nth (n +1) T
del-nth n {term} (λx, t) = λx,_ <$> del-nth (n +1) t
del-nth n {term} ⌊ e ⌋ = ⌊_⌋ <$> del-nth n e
del-nth n {elim} (f ` s) = _`_ <$> del-nth n f ⍟ del-nth n s
del-nth n {elim} (s ꞉ S) = _꞉_ <$> del-nth n s ⍟ del-nth n S
del-nth n {elim} (var v) = var <$> delVar n v

del-nth== : ∀ {tag tag' m m' n n'}
  {e : expr-of-type tag (m +1)}
  {e' : expr-of-type tag' (m' +1)}
  (eq₀ : tag == tag')
  (eq₁ : m == m')
  (eq₂ : n == n')
  (eq₃ : e Het.== e')
  → ------------------------------
  del-nth n e Het.== del-nth n' e'
del-nth== (Id.refl tag)(Id.refl m)(Id.refl n)(Het.refl e) = refl (del-nth n e)
