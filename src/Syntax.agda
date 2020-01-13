{-# OPTIONS --exact-split --prop  #-}
open import Basic
open import Universes

module Syntax
  {R : 𝒰 ˙} ⦃ r : Rig R ⦄
  {𝑆 : 𝒱 ˙} ⦃ _ : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Data.Nat

-- Definition 4 (term, elimination)

data Var : (n : ℕ) → 𝒰₀ ˙ where
  new : {n : ℕ} → Var (suc n)
  old : {n : ℕ} (a : Var n) → Var (suc n)

index : ∀ {m} (v : Var m) → ℕ
index new = 0
index (old v) = suc (index v)

open import Proof

index< : ∀ {m} (v : Var m) → index v < m
index< new = z<s
index< (old v) = ap suc (index< v)

open import Logic hiding (_,_)
open import Function using (inj)

Var== : ∀ {m} {u v : Var m}
  → --------------------------
  u == v ↔ index u == index v
⟶ Var== = ap index
⟵ (Var== {u = new} {new}) q = refl new
⟵ (Var== {u = old u} {old v}) q = ap old $ ⟵ Var== $ inj q

nth-var : ∀ {m} (n : ℕ) (p : n < m) → Var m
nth-var {suc m} zero p = new
nth-var {suc m} (suc n) p = old (nth-var n (s<s→-<- p))

index-nth-var : ∀ {m} n
  (p : n < m)
  → ----------------------
  index (nth-var n p) == n
index-nth-var {suc m} zero p = refl 0
index-nth-var {suc m} (suc n) (s<s p) = ap suc (index-nth-var n p)

contract : ∀ {m n} (v : Var m) (p : index v < n) → Var n
contract {suc m}{suc n} new p = new
contract {suc m}{suc n}(old v) p = old (contract v (s<s→-<- p))

data Term (n : ℕ) : 𝒰 ⁺ ⊔ 𝒱 ˙
data Elim (n : ℕ) : 𝒰 ⁺ ⊔ 𝒱 ˙

infix 170 [_x:_]→_ λx,_
data Term n where
  ⋆ : (i : 𝑆) → Term n
  [_x:_]→_ : (ρ : R) (S : Term n) (T : Term (suc n)) → Term n
  λx,_ : (t : Term (suc n)) → Term n
  ⌊_⌋ : (e : Elim n) → Term n

infix 160 _`_ _꞉_
data Elim n where
  var : (x : Var n) → Elim  n
  _`_ : (f : Elim n) (s : Term n) → Elim n
  _꞉_ : (s : Term n) (S : Term n) → Elim n

data ExprTag : 𝒰₀ ˙ where
  term elim : ExprTag

expr-of-type : (e : ExprTag) (n : ℕ) → 𝒰 ⁺ ⊔ 𝒱 ˙
expr-of-type term = Term
expr-of-type elim = Elim

open import Type.Sum using (Σ; _,_)

Expr : (n : ℕ) → 𝒰 ⁺ ⊔ 𝒱 ˙
Expr n = Σ λ e → expr-of-type e n

type-of-expr : {n : ℕ} (e : Expr n) → ExprTag
type-of-expr (tag , _) = tag

open import Proposition.Identity
  renaming (Idₚ to Id) hiding (refl)
open import Proposition.Decidable
open import Function

instance
  DecidableVar== : ∀ {n} {v v' : Var n} → Decidable (v == v')
  DecidableVar== {v = new} {new} = true (refl new)
  DecidableVar== {v = new} {old _} = false λ ()
  DecidableVar== {v = old _} {new} = false λ ()
  DecidableVar== {v = old v} {old v'} with decide (v == v')
  DecidableVar== | true p = true (ap old p)
  DecidableVar== | false ¬p = false λ { (Id.refl (old v)) → ¬p (refl v) }

  Injective-old : ∀ {m} → Injective (old {m})
  inj ⦃ Injective-old ⦄ (Id.refl (old v)) = refl v
