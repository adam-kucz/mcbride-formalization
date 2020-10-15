{-# OPTIONS --exact-split #-}
open import Basic using (Rig; wfs)
open import Universes

module Substitution.Basic
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax ⦃ rig ⦄ ⦃ wfs ⦄
open import Liftable

open import Data.Nat hiding (_⊔_)
open import Function hiding (_$_)
open import Proof

Sub : (m n : ℕ) → 𝒰 ⁺ ⊔ 𝒱 ˙
Sub m n = (v : Var m) → Elim n

subTerm : (σ : Sub m n)(t : Term m) → Term n
subElim : (σ : Sub m n)(e : Elim m) → Elim n

subTerm σ (⋆ i) = ⋆ i
subTerm σ ([ π x: S ]→ T) = [ π x: subTerm σ S ]→ subTerm (lift σ) T
subTerm σ (λx, t) = λx, subTerm (lift σ) t
subTerm σ ⌊ e ⌋ = ⌊ subElim σ e ⌋

subElim σ (var v) = σ v
subElim σ (f ` s) = subElim σ f ` subTerm σ s
subElim σ (s ꞉ S) = subTerm σ s ꞉ subTerm σ S

_⍟_ : 
  (σ : Sub n k)
  (τ : Sub m n)
  → -------------
  Sub m k
σ ⍟ τ = subElim σ ∘ τ

open import Renaming

open import Type.BinarySum renaming (_+_ to _⊹_)
open import Function

aux-nthSub : ∀(x : X){k}
  (m : ℕ)
  (v : Var (k +1))
  → --------------------
  X ⊹ Elim k
aux-nthSub x 0 new = inl x
aux-nthSub x 0 (old v) = inr (var v)
aux-nthSub x {0}(m +1) v = inl x
aux-nthSub x {k +1}(m +1) new = inr (var new)
aux-nthSub x {k +1}(m +1)(old v) =
  [ id + shift ] (aux-nthSub x m v)

nthSub : (m : ℕ)(f : Elim n) → Sub (n +1) n
nthSub {n} m f v = [ id , id ] (aux-nthSub f m v)

newSub : (f : Elim n) → Sub (n +1) n
newSub = nthSub 0

-- aux-nthSub : ∀ (x : X){k}
--   (m : ℕ)
--   (p : m ≤ k)
--   (v : Var (k +1))
--   → --------------------
--   X ⊹ Elim k
-- aux-nthSub x 0 _ new = inl x
-- aux-nthSub x 0 _ (old v) = inr (var v)
-- aux-nthSub x {k +1}(m +1) _ new = inr (var new)
-- aux-nthSub x {k +1}(m +1)(s≤s p)(old v) =
--   [ id + shift ] (aux-nthSub x m p v)
  
-- nthSub : ∀ m (p : m ≤ n)(f : Elim n) → Sub (n +1) n
-- nthSub {n} m p f v = [ id , id ] (aux-nthSub f m p v)

-- newSub : (f : Elim n) → Sub (n +1) n
-- newSub {n} = nthSub 0 (z≤ n)
