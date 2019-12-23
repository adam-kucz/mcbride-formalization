{-# OPTIONS --exact-split --safe --prop  #-}
module TypeTheory.Judgement where

open import TypeTheory.Basic using (Rig; wfs; _≻_)
open import TypeTheory.Syntax
open import TypeTheory.Computation using (_⇝_; _[_/new])
open import TypeTheory.Context

open import Foundation.PropUniverses
open import Foundation.Structure.Hemiring using (zero; _*_)

-- Definition 7 (prejudgement)

_⊢_∋_ :
  ⦃ _ : Rig X ⦄
  ⦃ _ : wfs 𝒰 𝒱 Y ⦄
  (Γ : Precontext)
  (T : Term)
  (t : Term)
  → --------------------
  𝒰₀ ᵖ
_⊢_∋_ = {!!}

_⊢_∈_ :
  ⦃ _ : Rig X ⦄
  ⦃ _ : wfs 𝒰 𝒱 Y ⦄
  (Γ : Precontext)
  (e : Elim)
  (S : Term)
  → --------------------
  𝒰₀ ᵖ
_⊢_∈_ = {!!}

-- Definition 8 (judgment)

infix 17 _⊢_,_∋_
data _⊢_,_∋_
  {R : 𝒰 ˙}
  {S : 𝒱 ˙}
  ⦃ _ : Rig R ⦄
  ⦃ _ : wfs 𝒲 𝒯 S ⦄
  : ------------------------------
  (Δ : Ctx R S)
  (ρ : R)
  (T : Term)
  (t : Term)
  → 𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲 ˙

infix 17 _⊢_,_∈_
data _⊢_,_∈_
  {R : 𝒰 ˙}
  {S : 𝒱 ˙}
  ⦃ _ : Rig R ⦄
  ⦃ _ : wfs 𝒲 𝒯 S ⦄
  : ------------------------------
  (Δ : Ctx R S)
  (ρ : R)
  (e : Elim)
  (S : Term)
  → 𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲 ˙

infix 17 _⊢₀_∋_
_⊢₀_∋_ : 
  {R : 𝒰 ˙}
  {S : 𝒱 ˙}
  ⦃ r : Rig R ⦄
  ⦃ _ : wfs 𝒲 𝒯 S ⦄
  (Γ : PC R S)
  (T : Term)
  (t : Term)
  → --------------------
  𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲 ˙
_⊢₀_∋_ ⦃ r = r ⦄ Γ T t = ctx Γ zero ⊢ zero , T ∋ t

-- Definition 9 (type checking and synthesis)

_≼_ :
  {R : 𝒰 ˙} {S : 𝒱 ˙}
  ⦃ _ : Rig R ⦄ ⦃ _ : wfs 𝒲 𝒯 S ⦄
  (S T : Term)
  → --------------------------------
  𝒰₀ ᵖ
_≼_ = {!!}

data _⊢_,_∋_ {𝒰 = 𝒰} {R = R} {S = 𝑆} where
  pre : {ρ : R} {Δ : Ctx R 𝑆} {T R t : Term}
    (Δ⊢ρT∋t : Δ ⊢ ρ , T ∋ t)
    (T⇝R : T ⇝ R)
    → ------------------------
    Δ ⊢ ρ , R ∋ t

  sort : {j i : 𝑆} {Γ : PC R 𝑆}
    (j≻i : j ≻ i)
    → --------------
    Γ ⊢₀ ⋆ j ∋ ⋆ i
   
  fun : {i : 𝑆} {π : R} {Γ : PC R 𝑆} {T S : Term} {x : Var {𝒰}}
    (Γ⊢₀*ᵢ∋S : Γ ⊢₀ ⋆ i ∋ S)
    (Γ,x:S⊢₀*ᵢ∋T : Γ ∥ x ∶ S ⊢₀ ⋆ i ∋ T)
    → --------------------------------------
    Γ ⊢₀ ⋆ i ∋ [ π x: S ]→ T

  lam : {π ρ : R} {Δ : Ctx R 𝑆} {T S t : Term} {x : Var {𝒰}}
    (Δ,ρπx:S⊢ρT∋t : Δ ∥ ρ * π , x ∶ S ⊢ ρ , T ∋ t)
    → --------------------------------------
    Δ ⊢ ρ , [ π x: S ]→ T ∋ λx, t
  
  elim : {ρ : R} {Δ : Ctx R 𝑆} {T S : Term} {e : Elim}
    (Δ⊢ρe∈S : Δ ⊢ ρ , e ∈ S)
    (S≼T : S ≼ T)
    → --------------------------------------
    Δ ⊢ ρ , T ∋ ⌊ e ⌋


data _⊢_,_∈_ {𝒰 = 𝒰} {R = R} {S = 𝑆} where
  post : {ρ : R} {Δ : Ctx R 𝑆} {S R : Term} {e : Elim}
    (Δ⊢ρe∈S : Δ ⊢ ρ , e ∈ S)
    (S⇝R : S ⇝ R)
    → ------------------------
    Δ ⊢ ρ , e ∈ R

  var : {ρ : R} {Γ Γ' : PC R 𝑆} {S : Term} {x : Var {𝒰}}
    → -------------------------------------------------
    ctx Γ zero ∥ ρ , x ∶ S ++ ctx Γ' zero ⊢ ρ , var x ∈ S

  app : {π ρ : R} {Δ₀ Δ₁ : Ctx R 𝑆} {T S s : Term} {f : Elim}
    (Δ₀⊢ρf∈[πx:S]→T : Δ₀ ⊢ ρ , f ∈ [ π x: S ]→ T)
    (Δ₁⊢ρπS∋s : Δ₁ ⊢ ρ * π , S ∋ s)
    → --------------------------------------
    (Δ₀ pt+ Δ₁) ⊢ ρ , (f ` s) ∈ (T [ s ꞉ S /new])

  cut : {i : 𝑆} {ρ : R} {Δ : Ctx R 𝑆} {S s : Term}
    (⌊Δ⌋⊢₀*ᵢ∋S : precont Δ ⊢₀ ⋆ i ∋ S)
    (Δ⊢₀ρS∋s : Δ ⊢ ρ , S ∋ s)
    → --------------------------------------
    Δ ⊢ ρ , s ꞉ S ∈ S

