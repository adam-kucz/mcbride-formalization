{-# OPTIONS --exact-split --safe --prop  #-}
module TypeTheory.Syntax where

open import TypeTheory.Basic

open import Foundation.Universes

-- Definition 4 (term, elimination)

data Var {𝒰} : 𝒰 ˙ where
  avar : Var
  -- TODO: decide on var representation

data Term {R : 𝒰 ˙} ⦃ r : Rig R ⦄ {S : 𝒱 ˙} ⦃ _ : wfs 𝒲 𝒯 S ⦄ : 𝒰 ⁺ ⊔ 𝒱 ˙
data Elim {R : 𝒰 ˙} ⦃ r : Rig R ⦄ {S : 𝒱 ˙} ⦃ _ : wfs 𝒲 𝒯 S ⦄ : 𝒰 ⁺ ⊔ 𝒱 ˙

infix 32 [_x:_]→_ λx,_
data Term {R = R} {S = 𝑆} where
  ⋆ : (i : 𝑆) → Term
  [_x:_]→_ : (r : R) (S : Term) (T : Term) → Term
  λx,_ : (t : Term) → Term
  ⌊_⌋ : (e : Elim) → Term

infix 30 _`_ _꞉_
data Elim {𝒰} where
  var : (x : Var {𝒰}) → Elim
  _`_ : (f : Elim) → (s : Term) → Elim
  _꞉_ : (s : Term) → (S : Term) → Elim

data Expr : Set where
  term elim : Expr

Expr-2-Set :
  (e : Expr)
  {R : 𝒰 ˙}
  ⦃ _ : Rig R ⦄
  {S : 𝒱 ˙}
  ⦃ _ : wfs 𝒲 𝒯 S ⦄
  → --------------------
  𝒰 ⁺ ⊔ 𝒱 ˙
Expr-2-Set term = Term
Expr-2-Set elim = Elim
