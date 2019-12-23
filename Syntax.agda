{-# OPTIONS --exact-split --safe --prop  #-}
module Syntax where

open import Foundation.PropUniverses
open import Foundation.Structure.Hemiring
open import Foundation.Data.Nat.Definition hiding (zero)
open import Foundation.Data.FinNat.Definition hiding (zero)

-- Definition 1 (rig)

open import Foundation.Prop'.Identity using (_==_; refl)

Rig : (X : 𝒰 ˙) → 𝒰 ˙
Rig = Hemiring

-- Definition 2 (none-one-tons)
None-one-tons : 𝒰₀ ˙
None-one-tons = Finℕ 3

q0 q1 qω : None-one-tons
q0 = 0
q1 = 1
qω = 2

-- Definition 3 (sort ordering)

record WellFoundedSorts (𝒰 𝒱 : Universe) (S : 𝒲 ˙) : (𝒰 ⊔ 𝒱) ⁺ ⊔ 𝒲 ˙ where
  field
    _≻_ : (i : S) → (j : S) → 𝒰 ˙
    
    trans : ∀ {i j k}
      (k≻j : k ≻ j) → (j≻i : j ≻ i)
      → --------------------------
      k ≻ i
    
    wf : ∀ {j} {P : S → 𝒱 ˙} →
      (all≺ : ∀ i { j≻i : j ≻ i } → P i)
      → ------------------------
      ∀ k → P k

open WellFoundedSorts ⦃ ... ⦄ public

wfs : ∀ 𝒰 𝒱 (S : 𝒲 ˙) → (𝒰 ⊔ 𝒱) ⁺ ⊔ 𝒲 ˙
wfs = WellFoundedSorts

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

-- Definition 5 (contraction, reduction, computation)

infix 4 _[_/new]
_[_/new] :
  ⦃ _ : Rig X ⦄
  ⦃ _ : wfs 𝒰 𝒱 Y ⦄
  {e' : Expr}
  → -----------------
  (e : Expr-2-Set e') (f : Elim) → Expr-2-Set e'
e [ f /new] = e

infix 2 _⇝β_ _⇝v_
data _⇝β_ ⦃ _ : Rig X ⦄ ⦃ _ : wfs 𝒰 𝒱 Y ⦄ : (e e' : Elim) → 𝒰₀ ᵖ where
  β : ∀ {π} {s t S T}
    → ----------------------------------------------------
    (λx, t ꞉ ([ π x: S ]→ T)) ` s ⇝β (t ꞉ T) [ s ꞉ S /new]

data _⇝v_ ⦃ _ : Rig X ⦄ ⦃ _ : wfs 𝒰 𝒱 Y ⦄ : (t T : Term) → 𝒰₀ ᵖ where
  v : ∀ {t T}
    → --------------
    ⌊ t ꞉ T ⌋ ⇝v t

data 1-hole-ctx
  {R : 𝒰 ˙}
  ⦃ _ : Rig R ⦄
  {S : 𝒱 ˙}
  ⦃ _ : wfs 𝒲 𝒯 S ⦄
  : ------------------------
  (e e' : Expr) → 𝒰 ⁺ ⊔ 𝒱 ˙
  where
  — : ∀ {e}
    → ------------
    1-hole-ctx e e
  
  [_x:_]→_↓ : ∀ {e}
    (r : R)
    (S : Term)
    (C[—] : 1-hole-ctx e term)
    → ---------------------
    1-hole-ctx e term

  [_x:_↓]→_ : ∀ {e}
    (r : R)
    (C[—] : 1-hole-ctx e term)
    (T : Term)
    → ----------------------
    1-hole-ctx e term

  λx,_ : ∀ {e}
    (C[—] : 1-hole-ctx e term)
    → ----------------------
    1-hole-ctx e term

  ⌊_⌋ : ∀ {e}
    (C[—] : 1-hole-ctx e elim)
    → ---------------------
    1-hole-ctx e term

  _`_↓ : ∀ {e}
    (f : Elim)
    (C[—] : 1-hole-ctx e term)
    → ----------------------
    1-hole-ctx e elim

  _↓`_ : ∀ {e}
    (C[—] : 1-hole-ctx e elim)
    (s : Term)
    → ---------------------
    1-hole-ctx e elim

  _∶_↓ : ∀ {e}
    (s : Term)
    (C[—] : 1-hole-ctx e term)
    → ----------------------
    1-hole-ctx e elim

  _↓∶_ : ∀ {e}
    (C[—] : 1-hole-ctx e term)
    (S : Term)
    → ----------------------
    1-hole-ctx e elim


infix 35 _[_/—]
_[_/—] : {R : 𝒰 ˙} ⦃ _ : Rig R ⦄ {S : 𝒱 ˙} ⦃ _ : wfs 𝒲 𝒯 S ⦄
  {e₁ e₂ : Expr}
  (C[—] : 1-hole-ctx e₁ e₂)
  (e : Expr-2-Set e₁)
  → ----------------------
  Expr-2-Set e₂
— [ e /—] = e
[ π x: S ]→ C[—] ↓ [ e /—] = [ π x: S ]→ C[—] [ e /—]
([ π x: C[—] ↓]→ T) [ e /—] = [ π x: C[—] [ e /—] ]→ T
(λx, C[—]) [ e /—] = λx, C[—] [ e /—]
⌊ C[—] ⌋ [ e /—] = ⌊ C[—] [ e /—] ⌋
(f ` C[—] ↓) [ e /—] = f ` C[—] [ e /—]
(C[—] ↓` s) [ e /—] = C[—] [ e /—] ` s
(s ∶ C[—] ↓) [ e /—] = s ꞉ C[—] [ e /—]
(C[—] ↓∶ S) [ e /—] = C[—] [ e /—] ꞉ S

infix 1 _⇝_
data _⇝_ {R : 𝒰 ˙} ⦃ _ : Rig R ⦄ {S : 𝒱 ˙} ⦃ _ : wfs 𝒲 𝒯 S ⦄ :
     {e' : Expr} (s t : Expr-2-Set e') → 𝒰 ⁺ ⊔ 𝒱 ᵖ where
  β-exact : ∀ {s t}
    (β : s ⇝β t)
    → -------------
    s ⇝ t

  v-exact : ∀ {s t}
    (v : s ⇝v t)
    → -------------
    s ⇝ t

  hole : ∀ {e₁ e₂} {s t}
    (C[—] : 1-hole-ctx e₁ e₂)
    (reduct : s ⇝ t)
    → --------------------
    C[—] [ s /—] ⇝ C[—] [ t /—]

open import Foundation.Relation.Binary.ReflexiveTransitiveClosure
  using (refl-trans-close)

infix 1 _↠_
_↠_ : ∀ {R : 𝒰 ˙} ⦃ _ : Rig R ⦄ {S : 𝒱 ˙} ⦃ _ : wfs 𝒲 𝒯 S ⦄ {e}
  (e₁ : Expr-2-Set e)
  (e₂ : Expr-2-Set e)
  → --------------------
  𝒰 ⁺ ⊔ 𝒱 ᵖ
_↠_ = refl-trans-close _⇝_

-- Definition 6 (precontext, context)

infix 19 _∥_∶_
data Precontext
  {R : 𝒰 ˙}
  ⦃ _ : Rig R ⦄
  {S : 𝒱 ˙}
  ⦃ _ : wfs 𝒲 𝒯 S ⦄
  : -----------------
  𝒰 ⁺ ⊔ 𝒱 ˙
  where
  · : Precontext
  _∥_∶_ :
    (Γ : Precontext)
    (x : Var {𝒰})
    (S : Term)
    → ----------------
    Precontext

infix 19 _∥_,_∶_
data Context
  {R : 𝒰 ˙}
  {S : 𝒱 ˙}
  ⦃ _ : Rig R ⦄
  ⦃ _ : wfs 𝒲 𝒯 S ⦄
  : -----------------
  𝒰 ⁺ ⊔ 𝒱 ˙
  where
  · : Context
  
  _∥_,_∶_ :
    (Δ : Context)
    (ρ : R)
    (x : Var {𝒰})
    (S : Term)
    → --------------
    Context

private
  PC : (R : 𝒰 ˙) (S : 𝒱 ˙) ⦃ _ : Rig R ⦄ ⦃ _ : wfs 𝒲 𝒯 S ⦄ → 𝒰 ⁺ ⊔ 𝒱 ˙
  PC R S = Precontext {R = R} {S = S}

  Ctx : (R : 𝒰 ˙) (S : 𝒱 ˙) ⦃ _ : Rig R ⦄ ⦃ _ : wfs 𝒲 𝒯 S ⦄ → 𝒰 ⁺ ⊔ 𝒱 ˙
  Ctx R 𝑆 = Context {R = R} {S = 𝑆}

precont : ⦃ _ : Rig X ⦄ ⦃ _ : wfs 𝒰 𝒱 Y ⦄
  (Δ : Ctx X Y)
  → ------------
  PC X Y
precont · = ·
precont (Δ ∥ _ , x ∶ S) = precont Δ ∥ x ∶ S

ctx :
  ⦃ _ : Rig X ⦄
  ⦃ _ : wfs 𝒰 𝒱 Y ⦄
  (Γ : PC X Y)
  (r : X)
  → ----------------
  Ctx X Y
ctx · _ = ·
ctx (Γ ∥ x ∶ S) ρ = (ctx Γ ρ) ∥ ρ , x ∶ S

infix 18 _++_
_++_ : ⦃ _ : Rig X ⦄ ⦃ _ : wfs 𝒰 𝒱 Y ⦄
  (Δ Δ' : Ctx X Y)
  → -----------------
  Ctx X Y
Δ ++ · = Δ
Δ ++ (Δ' ∥ ρ , x ∶ S) = (Δ ++ Δ') ∥ ρ , x ∶ S

infix 18 _pt+_
_pt+_ : ⦃ _ : Rig X ⦄ ⦃ _ : wfs 𝒰 𝒱 Y ⦄
  (Δ Δ' : Ctx X Y)
  → -----------------
  Ctx X Y
Δ pt+ Δ' = {!!}

-- Definition 7 (prejudgement)

_⊢_∋_ :
  ⦃ _ : Rig X ⦄
  ⦃ _ : wfs 𝒰 𝒱 Y ⦄
  (Γ : Precontext)
  (T : Term)
  (t : Term)
  → --------------------
  Prop
_⊢_∋_ = ?

_⊢_∈_ :
  ⦃ _ : Rig X ⦄
  ⦃ _ : wfs 𝒰 𝒱 Y ⦄
  (Γ : Precontext)
  (e : Elim)
  (S : Term)
  → --------------------
  Prop
_⊢_∈_ = ?

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
_≼_ = ?

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

