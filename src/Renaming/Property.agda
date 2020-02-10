{-# OPTIONS --exact-split --prop #-}
open import Basic
open import Universes

module Renaming.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {𝑆 : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Renaming.Definition
open import Renaming.Syntax

open import Syntax.Definition
open import Liftable

open import Data.Nat
open import Proposition.Identity hiding (refl)
open import Proposition.Identity.Coercion
open import Function hiding (_$_)
open import Proof

private
  ap-ren : ∀ {m m' : ℕ}
    (F : (m : ℕ) → 𝒳 ˙)
    ⦃ _ : Renameable F ⦄
    {K : ℕ → ℕ}
    (ρ : ∀ {m} → Ren m (K m))
    (e : F m)
    (p : m == m')
    → -----------------------
    rename ρ (coe (ap F p) e) == rename ρ e
  ap-ren F ρ e (Id.refl m) =
    ap (rename ρ) $ coe-eval (Id.refl _) e



-- shift-inside : ∀ k {m}
--   {F : (m : ℕ) → 𝒮 ˙}
--   ⦃ _ : Renameable F ⦄
--   (x : F m)
--   → ------------------------------
--   shift-by (k +1) x == shift-by k (shift x)
-- shift-inside zero x = refl (shift x)
-- shift-inside (k +1){m}{F} x =
--   proof shift-by (k +2) x
--     === shift (coe (ap F $ +-suc k m) (shift-by k (shift x)))
--       :by: ap shift $ go
--     === shift-by (k +1) (shift x)
--       :by: ap-ren F old (shift-by k (shift x)) (+-suc k m)
--   qed
--   where go = proof shift-by (k +1) x
--                === shift-by k (shift x)
--                  :by: shift-inside k x
--                === coe (ap F $ +-suc k m) (shift-by k (shift x))
--                  :by: Id.sym $
--                       coe-eval (ap F $ +-suc k m) (shift-by k (shift x))
--              qed

-- rename-shift : ∀ {m n} k {tag}
--   (ρ : Ren m n)
--   (e : expr-of-type tag m)
--   → ---------------------------------------------
--   rename (lift-by k ρ) (shift-by k e)
--   ==
--   shift-by k (rename ⦃ RenameableExpr ⦄ ρ e)
-- rename-shift k {term} ρ (⋆ i) = refl (⋆ i)
-- rename-shift k {term} ρ ([ π x: S ]→ T) = {!!}
-- rename-shift k {term} ρ (λx, t) = {!!}
-- rename-shift k {term} ρ ⌊ e ⌋ = ap ⌊_⌋ (rename-shift k ρ e)
-- rename-shift k {elim} ρ (var v) =
--   proof
--   rename (lift-by k ρ) (shift-by k e)
--   ==
--   shift-by k (rename ⦃ RenameableExpr ⦄ ρ e)
--   qed
-- rename-shift k {elim} ρ (f ` s) = {!!}
-- rename-shift k {elim} ρ (s ꞉ S) = {!!}
-- rename-shift 0 ρ e = refl (rename ρ e)
-- rename-shift (k +1){term} ρ ([ π x: S ]→ T) = {!!}
-- rename-shift (k +1){term} ρ (λx, t) = {!!}
-- rename-shift {m}(k +1){term} ρ ⌊ e ⌋ =
--   proof rename (lift-by (k +1) ρ) (shift-by (k +1) ⌊ e ⌋)
--     === rename (lift-by (k +1) ρ)
--           (coe (ap Term $ +-suc k m) (shift-by k ⌊ shift e ⌋))
--       :by: ap (rename (lift-by (k +1) ρ)) (
--         proof (shift-by (k +1) ⌊ e ⌋)
--           === shift-by k ⌊ shift e ⌋
--             :by: shift-inside k ⌊ e ⌋
--           === coe (ap Term $ +-suc k m) (shift-by k ⌊ shift e ⌋)
--             :by: Id.sym $ coe-eval (ap Term $ +-suc k m) (shift-by k ⌊ shift e ⌋)
--         qed)
--     === shift-by (k +1) (⌊ rename ρ e ⌋)
--       :by: {!rename-shift (k +1) ρ e!}
--   qed
-- rename-shift (k +1){elim} ρ (f ` s) = {!!}
-- rename-shift (k +1){elim} ρ (s ꞉ S) = {!!}
-- rename-shift (k +1){elim} ρ (var v) = go k ρ v
--   where go : ∀ {m n} k
--           (ρ : Ren m n)
--           (v : Var m)
--           → -------------------------------------------
--           rename (lift-by (k +1) ρ) (shift-by (k +1) (var v))
--           ==
--           shift-by (k +1) (rename ρ (var v))
--         go 0 ρ v = refl (var (old (ρ v)))
--         go (k +1) ρ v =
--           proof rename (lift-by (k +2) ρ) (shift-by (k +2) (var v))
--             === rename (lift-by (k +2) ρ) (shift (var (shift-by (k +1) v)))
--               :by: ap (λ — → rename (lift-by (k +2) ρ) (shift —)) $
--                    shift-var (k +1) v
--             === shift (rename (lift-by (k +1) ρ) (var (shift-by (k +1) v)))
--               :by: go 0 (lift-by (k +1) ρ) (shift-by (k +1) v)
--             === shift (rename (lift-by (k +1) ρ) (shift-by (k +1) (var v)))
--               :by: ap (λ — → shift (rename (lift-by (k +1) ρ) —)) $
--                    Id.sym $ shift-var (k +1) v
--             === shift (shift-by (k +1) (var (ρ v)))
--               :by: ap shift $ go k ρ v
--           qed
-- rename-shift (k +1) {term} ρ (⋆ i) =
--   proof rename (lift-by (k +1) ρ) (shift-by (k +1) (⋆ i))
--     === rename (lift-by (k +1) ρ) (⋆ i)
--       :by: ap (rename (lift-by (k +1) ρ)) $ shift-star (k +1) i
--     === ⋆ i
--       :by: Id.refl (⋆ i)
--     === shift-by (k +1) (⋆ i)
--       :by: Id.sym $ shift-star (k +1) i
--     === shift-by (k +1) (rename ρ (⋆ i))
--       :by: Id.refl (shift-by (k +1) (⋆ i))
--   qed
