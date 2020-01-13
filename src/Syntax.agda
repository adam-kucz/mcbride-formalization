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

nth-var : ∀ {m} (n : ℕ) (p : n < m) → Var m
nth-var {suc m} zero p = new
nth-var {suc m} (suc n) p = old (nth-var n (s<s→-<- p))

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
open import Proposition.Decidable
open import Function

instance
  Var== : ∀ {n} {v v' : Var n} → Decidable (v == v')
  Var== {v = new} {new} = true (refl new)
  Var== {v = new} {old _} = false λ ()
  Var== {v = old _} {new} = false λ ()
  Var== {v = old v} {old v'} with decide (v == v')
  Var== | true p = true (ap old p)
  Var== | false ¬p = false λ { (refl (old v)) → ¬p (refl v) }

  Injective-old : ∀ {m} → Injective (old {m})
  inj ⦃ Injective-old ⦄ (refl (old v)) = refl v
