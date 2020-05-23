{-# OPTIONS --exact-split --prop #-}
open import Basic using (Rig; wfs)
open import PropUniverses

module Substitution.Definition
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax ⦃ rig ⦄ ⦃ wfs ⦄
open import Renaming

open import Data.Nat hiding (_⊔_)
open import Function hiding (_$_)
open import Proof

open import Substitution.Basic using (Sub; _⍟_) public

record Substitutable (F : (m : ℕ) → 𝒮 ˙) : 𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒮 ˙ where
  field
    ⦃ ren ⦄ : Renameable F
    sub : (σ : Sub m n)(e : F m) → F n
    rename-as-sub : (ρ : Ren m n) → rename ρ == sub (var ∘ ρ)
    sub-id : sub {m} var == id
    sub-∘ :
      (σ : Sub n k)
      (τ : Sub m n)
      → ------------------------------------
      sub σ ∘ sub τ == sub (σ ⍟ τ)

  open import Type.BinarySum renaming (_+_ to _⊹_)
  open import Function hiding (_$_)
  open import Proposition.Empty

  aux-nthSub : ∀ (x : X){k}
    (m : ℕ)
    (p : m < k +1)
    (v : Var (k +1))
    → --------------------
    X ⊹ Elim k
  aux-nthSub x 0 _ new = inl x
  aux-nthSub x 0 _ (old v) = inr (var v)
  aux-nthSub x {zero} (m +1) p new = ⊥-recursion _ (¬-<0 m $ s<s→-<- p)
  aux-nthSub x {k +1} (m +1) _ new = inr (var new)
  aux-nthSub x {k +1} (m +1) p (old v) =
    [ id + shift ] (aux-nthSub x m (s<s→-<- p) v)
    
  nthSub : ∀ m (p : m < n +1)(f : Elim n) → Sub (n +1) n
  nthSub {n} m p f v = [ id , id ] (aux-nthSub f m p v)
  
  newSub : (f : Elim n) → Sub (n +1) n
  newSub {n} = nthSub 0 (z<s n)
  
  infix 180 _[_/new] _[_/_[_]]
  _[_/new] : (e : F (n +1))(f : Elim n) → F n
  e [ f /new] = sub (newSub f) e
  
  _[_/_[_]] :
    (e : F (n +1))
    (f : Elim n)
    (m : ℕ)
    (p : m < n +1)
    → -------------------------------------------------------------
    F n
  e [ f / m [ p ]] = sub (nthSub m p f) e

open Substitutable ⦃ … ⦄ public

