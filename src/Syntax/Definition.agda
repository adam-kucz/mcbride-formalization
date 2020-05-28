{-# OPTIONS --exact-split --prop --safe  #-}
open import Basic
open import Universes

module Syntax.Definition
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Data.Nat hiding (_⊔_)

-- Definition 4 (term, elimination)

data Var : (n : ℕ) → 𝒰₀ ˙ where
  new : {n : ℕ} → Var (n +1)
  old : {n : ℕ} (a : Var n) → Var (n +1)

index : ∀ {m} (v : Var m) → ℕ
index new = 0
index (old v) = index v +1

open import Proposition.Empty
open import Logic hiding (⊥-recursion)
open import Proof

index< : ∀ {m} (v : Var m) → index v < m
index< {m +1} new = ⟵ -<-↔s≤- $ ap suc $ z≤ m
index< (old v) = ap suc (index< v)

open import Function using (inj)
open import Relation.Binary

Var== : ∀ {m} {u v : Var m}
  → --------------------------
  u == v ↔ index u == index v
⟶ Var== = ap index
⟵ (Var== {u = new} {new}) q = refl new
⟵ (Var== {u = old u} {old v}) q = ap old $ ⟵ Var== $ ap pred q

nth-var : ∀ {m} (n : ℕ) (p : n < m) → Var m
nth-var {zero} zero p = ⊥-recursion (Var 0) (irrefl 0 p)
nth-var {m +1} zero _ = new
nth-var {m +1} (n +1) p = old (nth-var n (s<s→-<- p))

index-nth-var : ∀ {m} n
  (p : n < m)
  → ----------------------
  index (nth-var n p) == n
index-nth-var {zero} zero p = ⊥-recursionₚ _ $ irrefl 0 p
index-nth-var {m +1} zero p = refl 0
index-nth-var {m +1} (n +1) p = ap suc (index-nth-var n (s<s→-<- p))

contract : ∀ {m n} (v : Var m) (p : index v < n) → Var n
contract {m +1}{zero} new p = ⊥-recursion (Var 0) (irrefl 0 p)
contract {m +1}{n +1} new p = new
contract {m +1}{n +1}(old v) p = old (contract v (s<s→-<- p))

data Term (n : ℕ) : 𝒰 ⁺ ⊔ 𝒱 ˙
data Elim (n : ℕ) : 𝒰 ⁺ ⊔ 𝒱 ˙

infix 170 [_x:_]→_ λx,_
data Term n where
  ⋆ : (i : S) → Term n
  [_x:_]→_ : (ρ : R) (S : Term n) (T : Term (n +1)) → Term n
  λx,_ : (t : Term (n +1)) → Term n
  ⌊_⌋ : (e : Elim n) → Term n

infix 160 _`_ _꞉_
data Elim n where
  var : (v : Var n) → Elim  n
  _`_ : (f : Elim n) (s : Term n) → Elim n
  _꞉_ : (s : Term n) (S : Term n) → Elim n

data ExprTag : 𝒰₀ ˙ where
  term elim : ExprTag

variable
  tag : ExprTag

expr-of-type : (e : ExprTag) (n : ℕ) → 𝒰 ⁺ ⊔ 𝒱 ˙
expr-of-type term = Term
expr-of-type elim = Elim

open import Type.Sum hiding (_,_)

Expr : (n : ℕ) → 𝒰 ⁺ ⊔ 𝒱 ˙
Expr n = Σ λ e → expr-of-type e n

type-of-expr : (e : Expr n) → ExprTag
type-of-expr (tag Σ., _) = tag

RelOnExpr : (𝒲 : Universe) → 𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲 ⁺ ˙
RelOnExpr 𝒲 = ∀ {n} {tag} → BinRel 𝒲 (expr-of-type tag n)

open import Proposition.Identity
  renaming (Idₚ to Id) hiding (refl)
open import Proposition.Decidable
open import Function hiding (_$_)

instance
  DecidableVar== : {v v' : Var n} → Decidable (v == v')
  Injective-old : Injective (old {m})
  Injective-index : Injective (index {m})

DecidableVar== {v = new} {new} = true (refl new)
DecidableVar== {v = new} {old _} = false λ ()
DecidableVar== {v = old _} {new} = false λ ()
DecidableVar== {v = old v} {old v'} with decide (v == v')
DecidableVar== | true p = true (ap old p)
DecidableVar== | false ¬p = false λ { (Id.refl (old v)) → ¬p (refl v) }

inj ⦃ Injective-old ⦄ (Het.refl (old v)) = refl v

inj ⦃ Injective-index ⦄ {new} {new} p = Id-refl _
inj ⦃ Injective-index ⦄ {old v} {old v'} p =
  ap old $ inj ⦃ Injective-index ⦄ {v}{v'} (ap pred p)

old==old→== : {v : Var m}{v' : Var n}
  (p : m == n)
  (q : old v Het.== old v')
  → -----------------
  v Het.== v'
old==old→== (Id-refl m) (Het.refl (old v)) = Het.refl v

nth-var-index== : ∀ (v : Var m) →
  nth-var (index v) (index< v) == v
nth-var-index== v = inj $ subrel $ index-nth-var (index v) (index< v)

index==→var== :
  {v : Var m}
  {v' : Var n}
  (p : m == n)
  (q : index v == index v')
  →
  v Het.== v'
index==→var== (Id-refl x) q = subrel $ inj $ subrel q

