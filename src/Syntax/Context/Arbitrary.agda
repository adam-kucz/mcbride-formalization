{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Syntax.Context.Arbitrary
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax

open import Type.Sum hiding (_,_)
open import Data.Nat hiding (_⊔_)
open import Data.Vec

Holes = Vec (ExprTag × ℕ)

data Context
  : --------------------------------------------------------------------------
  {m : ℕ} -- number of holes
  (holes : Holes m) -- required (type, number of free variables) of holes
  (result : ExprTag) -- type resulting from filling all holes
  (n : ℕ) -- number of free variables of the context (∀ m ∈ ms → n ≤ m)
  → 𝒰 ⁺ ⊔ 𝒱 ˙
  where
  term : (t : Term n)
    → -------------------
    Context [] term n

  elim : (e : Elim n)
    → -------------------
    Context [] elim n

  — : ∀ {tag n}
    → ------------------
    Context [ (tag Σ., n) ] tag n
  
  [_x:_]→_ : ∀ {n m₀ m₁}{v₀ : Holes m₀}{v₁ : Holes m₁}
    (π : R)
    (C₀ : Context v₀ term n)
    (C₁ : Context v₁ term (n +1))
    → ---------------------
    Context (v₀ ++ v₁) term n

  λx,_ : ∀ {n}{v : Holes m}
    (C : Context v term (n +1))
    → ----------------------
    Context v term n

  ⌊_⌋ : ∀ {n}{v : Holes m}
    (C : Context v elim n)
    → ---------------------
    Context v term n

  _`_ : ∀ {n m₀ m₁}{v₀ : Holes m₀}{v₁ : Holes m₁}
    (C₀ : Context v₀ elim n)
    (C₁ : Context v₁ term n)
    → ----------------------
    Context (v₀ ++ v₁) elim n

  _꞉_ : ∀ {n m₀ m₁}{v₀ : Holes m₀}{v₁ : Holes m₁}
    (C₀ : Context v₀ term n)
    (C₁ : Context v₁ term n)
    →  ----------------------
    Context (v₀ ++ v₁) elim n

open import Logic
open import Proof
open import Function hiding (_$_)

to-type : ExprTag × ℕ → 𝒰 ⁺ ⊔ 𝒱 ˙
all-types : Holes m → 𝒰 ⁺ ⊔ 𝒱 ˙
divide-types :
  (v₀ : Holes m)
  (v₁ : Holes n)
  (es : all-types (v₀ ++ v₁))
  → ---------------------------
  all-types v₀ × all-types v₁
get-nth : 
  (v : Holes m)
  (es : all-types v)
  (n : ℕ)
  (p : n +1 ≤ m)
  → ---------------------------
  to-type (v ! n [ p ])

open import Type.Unit
open import Collection

to-type = uncurry expr-of-type

all-types = foldr _×_ (Lift𝒰 𝟙) ∘ map to-type

divide-types [] v₁ es = ↑type ⋆ Σ., es
divide-types (h ∷ v₀) v₁ (eh Σ., es) = (eh Σ., pr₁ es') Σ., pr₂ es'
  where es' = divide-types v₀ v₁ es

get-nth (h ∷ _) (eh Σ., _) zero _ = eh
get-nth (_ ∷ v) (_ Σ., es) (n +1) p = get-nth v es n (ap pred p)

fill-holes : ∀
  {v : Holes m}
  (es : all-types v)
  {tag n}
  (C : Context v tag n)
  → ----------------------
  expr-of-type tag n
fill-holes es (term t) = t
fill-holes es (elim e) = e
fill-holes (e Σ., _) — = e
fill-holes es ([_x:_]→_ {v₀ = v₀}{v₁} π C₀ C₁) =
  [ π x: fill-holes (pr₁ es') C₀ ]→ fill-holes (pr₂ es') C₁
  where es' = divide-types v₀ v₁ es
fill-holes es (λx, C) = λx, fill-holes es C
fill-holes es ⌊ C ⌋ = ⌊ fill-holes es C ⌋
fill-holes es (_`_ {v₀ = v₀}{v₁} C₀ C₁) =
  fill-holes (pr₁ es') C₀ ` fill-holes (pr₂ es') C₁
  where es' = divide-types v₀ v₁ es
fill-holes es (_꞉_ {v₀ = v₀}{v₁} C₀ C₁) =
  fill-holes (pr₁ es') C₀ ꞉ fill-holes (pr₂ es') C₁
  where es' = divide-types v₀ v₁ es

as-expr : ∀{tag}
  (C : Context [] tag m)
  → ------------------------
  expr-of-type tag m
as-expr C = fill-holes (↑type ⋆) C

record ContextClosed (R : RelOnExpr 𝒵) : 𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒵 ᵖ where
  field
    ctx-closed : ∀
      {v : Holes m}{tag n}
      (C : Context v tag n)
      {es es' : all-types v}
      (p : ∀ i (q : i +1 ≤ m) → R (get-nth v es i q) (get-nth v es' i q))
      → -------------------------------------------------------------
      R (fill-holes es C) (fill-holes es' C)

open ContextClosed ⦃ … ⦄ public
