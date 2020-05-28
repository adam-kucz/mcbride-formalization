{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Syntax.Context.OneHole
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax
open import Syntax.Context.Arbitrary

open import Type.Sum hiding (_,_)
open import Data.Nat hiding (_⊔_)
open import Data.Vec

1-hole-ctx :
  (hole : ExprTag) -- required type of hole
  (m : ℕ) -- number of free variables in hole
  (result : ExprTag) -- type resulting from filling hole
  (n : ℕ) -- number of free variables of the context (n ≤ m)
  → 𝒰 ⁺ ⊔ 𝒱 ˙
1-hole-ctx hole m result n = context [ (hole Σ., m) ] result n

open import Type.Unit

infix 180 _[_/—]
_[_/—] : {m n : ℕ}
  {tag₀ tag₁ : ExprTag}
  (C[—] : 1-hole-ctx tag₀ m tag₁ n)
  (e : expr-of-type tag₀ m)
  → ----------------------
  expr-of-type tag₁ n
C[—] [ e /—] = fill-holes (e Σ., ↑type ⋆) C[—]

open import Function.Proof

1-ContextClosed : (R : RelOnExpr 𝒵) → 𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒵 ᵖ
1-ContextClosed R = ∀ {m n} {tag tag'}
  {C : 1-hole-ctx tag m tag' n}
  → ----------------------------
  Relating (C [_/—]) R R

1-ctx-closed : ∀ {_R'_ : RelOnExpr 𝒵}
  ⦃ 1-cc : 1-ContextClosed _R'_ ⦄
  {m n tag tag'}
  {e e' : expr-of-type tag m}
  (eRe' : e R' e')
  (C : 1-hole-ctx tag m tag' n)
  → ----------------------------
  C [ e /—] R' C [ e' /—]
1-ctx-closed ⦃ 1-cc ⦄ eRe' C = ap (C [_/—]) ⦃ 1-cc {C = C} ⦄ eRe'

instance
  1-CtxClosed-of-CtxClosed :
     {R : RelOnExpr 𝒵}
     ⦃ context-closed : ContextClosed R ⦄
     → ----------------------------------
     1-ContextClosed R

rel-preserv ⦃ 1-CtxClosed-of-CtxClosed {C = C} ⦄ rab =
  ctx-closed C λ { zero _ → rab ; (_ +1) (s≤s ())}
