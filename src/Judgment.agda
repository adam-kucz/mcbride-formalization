{-# OPTIONS --exact-split --prop --safe  #-}
open import TypeTheory.Basic using (Rig; wfs; _≻_)
open import Foundation.PropUniverses

module TypeTheory.Judgment
  {R : 𝒰 ˙} ⦃ r : Rig R ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import TypeTheory.Syntax
open import TypeTheory.Computation using (wk1; _⇝_; _[_/new])
open import TypeTheory.Context

open import Foundation.Data.Nat using (ℕ; suc; _+_)
open import Foundation.Structure.Hemiring using (zero; _*_)

-- Definition 7 (prejudgment)

infix 152 _⊢_∋_ _⊢_∈_
_⊢_∋_ : ∀ {n}
  (Γ : Precontext n)
  (T : Term n)
  (t : Term n)
  → --------------------
  𝒰₀ ᵖ
_⊢_∋_ = {!!}

_⊢_∈_ : ∀ {n}
  (Γ : Precontext n)
  (e : Elim n)
  (S : Term n)
  → --------------------
  𝒰₀ ᵖ
_⊢_∈_ = {!!}

-- Definition 8 (judgment)

infix 152 _⊢_,_∋_ _⊢_,_∈_ _⊢₀_∋_
data _⊢_,_∋_ {n}
  : ------------------------------
  (Δ : Context n)
  (ρ : R)
  (T : Term n)
  (t : Term n)
  → 𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲 ˙

data _⊢_,_∈_
  : ------------------------------
  {n : ℕ}
  (Δ : Context n)
  (ρ : R)
  (e : Elim n)
  (S : Term n)
  → 𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲 ˙

_⊢₀_∋_ : ∀ {n}
  (Γ : Precontext n)
  (T : Term n)
  (t : Term n)
  → --------------------
  𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲 ˙
_⊢₀_∋_ Γ T t = ctx Γ zero ⊢ zero , T ∋ t

-- Definition 9 (type checking and synthesis)

_≼_ : ∀ {n} (T S : Term n) → 𝒰₀ ᵖ
_≼_ = {!!}

data _⊢_,_∋_ {n} where
  pre : ∀ {ρ} {Δ : Context n} {T R t : Term n}
    (Δ⊢ρT∋t : Δ ⊢ ρ , T ∋ t)
    (T⇝R : T ⇝ R)
    → ------------------------
    Δ ⊢ ρ , R ∋ t

  sort : ∀ {j i} {Γ : Precontext n}
    (j≻i : j ≻ i)
    → --------------
    Γ ⊢₀ ⋆ j ∋ ⋆ i
   
  fun : ∀ {i} {π} {Γ : Precontext n} {T S}
    (Γ⊢₀*ᵢ∋S : Γ ⊢₀ ⋆ i ∋ S)
    (Γ,x:S⊢₀*ᵢ∋T : Γ ∥x: S ⊢₀ ⋆ i ∋ T)
    → --------------------------------------
    Γ ⊢₀ ⋆ i ∋ [ π x: S ]→ T

  lam : ∀ {π ρ} {Δ : Context n} {T S t}
    (Δ,ρπx:S⊢ρT∋t : Δ ∥ ρ * π ,x: S ⊢ ρ , T ∋ t)
    → --------------------------------------
    Δ ⊢ ρ , [ π x: S ]→ T ∋ λx, t
  
  elim : ∀ {ρ} {Δ : Context n} {T S : Term n} {e : Elim n}
    (Δ⊢ρe∈S : Δ ⊢ ρ , e ∈ S)
    (S≼T : S ≼ T)
    → --------------------------------------
    Δ ⊢ ρ , T ∋ ⌊ e ⌋

-- used in alternative formulation of var
data var-in-ctx {n} (Γ : Precontext n) (ρ : R) (S : Term n)
  : {m : ℕ} (Δ : Context (m + suc n)) → 𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲 ˙
  where
  Γ'==∅ :
    (p : ctx Γ zero ∥ ρ ,x: S ⊢ ρ , var (nth-var n) ∈ wk1 S)
    → -------------------------------------------------------
    var-in-ctx Γ ρ S {0} (ctx Γ zero ∥ ρ ,x: S)

  Γ'-append : ∀ {m}
    (Δ : Context (m + suc n))
    (S' : Term (m + suc n))
    (p : var-in-ctx Γ ρ S Δ)
    → -------------------------------------------------------
    var-in-ctx Γ ρ S {suc m} (Δ ∥ zero ,x: S')

data _⊢_,_∈_ where
  post : ∀ {n} {ρ} {Δ : Context n} {S R} {e}
    (Δ⊢ρe∈S : Δ ⊢ ρ , e ∈ S)
    (S⇝R : S ⇝ R)
    → ------------------------
    Δ ⊢ ρ , e ∈ R

  -- modified compared to the paper to make the formulation simpler
  -- achieves the same result when weakening is added
  var : ∀ {n} {ρ : R} {Γ : Precontext n} {S : Term n}
    → ----------------------------------------------------
    ctx Γ zero ∥ ρ ,x: S ⊢ ρ , var (nth-var n) ∈ wk1 S

  -- necessary to make our version of var equivalent to mcbride's
  weaken : ∀ {n} {ρ} {Δ : Context (suc n)} {S S' : Term (suc n)}
    → let v = var (nth-var n) in (p : Δ ⊢ ρ , v ∈ S)
    → ----------------------------------------------------------
    Δ ∥ zero ,x: S' ⊢ ρ , wk1 v ∈ wk1 S

  -- -- alternative formulation of var (equivalent to that in the paper)
  -- var' : ∀ {m n} {ρ} {Γ : Precontext n}  {Δ : Context (m + suc n)}
  --          {S : Term n}
  --   (p : var-in-ctx Γ ρ S Δ)
  --   → ------------------------------------------------------------
  --   Δ ⊢ ρ , wk m (var (nth-var n)) ∈ wk m (wk1 S)

  app : ∀ {n} {π ρ} {Δ₀ Δ₁ : Context n} {T S s} {f}
    (p : compatible Δ₀ Δ₁)
    (Δ₀⊢ρf∈[πx:S]→T : Δ₀ ⊢ ρ , f ∈ [ π x: S ]→ T)
    (Δ₁⊢ρπS∋s : Δ₁ ⊢ ρ * π , S ∋ s)
    → --------------------------------------
    (Δ₀ pt+ Δ₁ [ p ]) ⊢ ρ , (f ` s) ∈ (T [ s ꞉ S /new])

  cut : ∀ {n} {i} {ρ} {Δ : Context n} {S s}
    (⌊Δ⌋⊢₀*ᵢ∋S : precont Δ ⊢₀ ⋆ i ∋ S)
    (Δ⊢₀ρS∋s : Δ ⊢ ρ , S ∋ s)
    → --------------------------------------
    Δ ⊢ ρ , s ꞉ S ∈ S

