{-# OPTIONS --exact-split --safe --prop  #-}
open import TypeTheory.Basic
open import Foundation.Universes

module TypeTheory.Syntax
  {R : 𝒰 ˙} ⦃ r : Rig R ⦄
  {𝑆 : 𝒱 ˙} ⦃ _ : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Foundation.Data.Nat using (ℕ; suc; zero)

-- Definition 4 (term, elimination)

data Var : (n : ℕ) → 𝒰₀ ˙ where
  new : {n : ℕ} → Var (suc n)
  old : {n : ℕ} (a : Var n) → Var (suc n)

nth-var : (n : ℕ) → Var (suc n)
nth-var zero = new
nth-var (suc n) = old (nth-var n)

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

open import Foundation.Type.Sum as Sum
open Sum using (_,_)

Expr : (n : ℕ) → 𝒰 ⁺ ⊔ 𝒱 ˙
Expr n = Σ λ e → expr-of-type e n

type-of-expr : {n : ℕ} (e : Expr n) → ExprTag
type-of-expr (tag , _) = tag
