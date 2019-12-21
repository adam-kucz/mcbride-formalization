{-# OPTIONS --prop  #-}
module Syntax where

open import Foundations.Univ
  using (Level; lsuc; _⊔_)

private
  variable
    𝑙 𝑚 𝑛 𝑝 : Level
 

-- Definition 1 (rig)

open import Foundations.Equality.Core
  using (_==_; refl)

record Rig (𝑅 : Set 𝑙) : Set 𝑙  where
  infixl 20 _+_
  infixl 21 _*_
  field
    zero : 𝑅
    _+_ : (π : 𝑅) (ρ : 𝑅) → 𝑅
    _*_ : (π : 𝑅) (ρ : 𝑅) → 𝑅
    0+ : ∀ {ρ} → zero + ρ == ρ
    +assoc : ∀ {ρ π φ} → ρ + (π + φ) == ρ + π + φ
    +comm : ∀ {ρ π} → ρ + π == π + ρ
    *assoc : ∀ {ρ π φ} → ρ * (π * φ) == ρ * π * φ
    0* : ∀ {ρ} → zero * ρ == zero
    *0 : ∀ {ρ} → ρ * zero == zero
    *[+]==*+* : ∀ {ρ π φ} → φ * (ρ + π) == φ * ρ + φ * π
    [+]*==*+* : ∀ {ρ π φ} → (ρ + π) * φ  == ρ * φ + π * φ

private
  variable
    R : Set 𝑙

open Rig ⦃ ... ⦄ using (_+_; _*_)
r0 : ⦃ r : Rig R ⦄ → R
r0 ⦃ r ⦄ = Rig.zero r

open import Foundations.Functions.Core using (_$_)
open import Foundations.Data.Nat using (ℕ)
open import Foundations.Data.FinNat
open import Foundations.Algebra.GroupLike hiding (zero; _+_)
open import Foundations.Algebra.RingLike

fin-rig : ∀ {n} → Rig (Finℕ $ ℕ.suc n)
fin-rig = record
            { zero = zero
            ; _+_ = _+ₛ_
            ; _*_ = _*ₛ_
            ; 0+ = Monoid.zero+ MonoidFinℕ+
            ; +assoc = λ {ρ π ϕ} → +assoc {a = ρ} {π} {ϕ}
            ; +comm = λ {ρ π} → +comm {a = ρ} {π}
            ; *assoc = λ {ρ π ϕ} → +assoc {a = ρ} {π} {ϕ}
            ; 0* = λ {ρ} → 0* {a = ρ}
            ; *0 = λ {ρ} → *0 {a = ρ}
            ; *[+]==*+* = λ {ρ π ϕ} → *[+]==*+* {a = ϕ} {ρ} {π}
            ; [+]*==*+* = λ {ρ π ϕ} → [+]*==*+* {a = ρ} {π} {ϕ}
            }

-- Definition 2 (none-one-tons)
None-one-tons : Set
None-one-tons = Finℕ 3

q0 q1 qω : None-one-tons
q0 = 0
q1 = 1
qω = 2

-- Definition 3 (sort ordering)

record WellFoundedSorts (S : Set 𝑙) : Set (𝑙 ⊔ lsuc (𝑚 ⊔ 𝑛)) where
  field
    _≻_ : (i : S) → (j : S) → Set 𝑚
    
    trans : ∀ {i j k}
      (k≻j : k ≻ j) → (j≻i : j ≻ i)
      → --------------------------
      k ≻ i
    
    wf : ∀ {j} {P : S → Set 𝑛} →
      (all≺ : ∀ i { j≻i : j ≻ i } → P i)
      → ------------------------
      ∀ k → P k

open WellFoundedSorts ⦃ ... ⦄ public

wfs : (𝑚 𝑛 : Level) → Set 𝑙 → Set (𝑙 ⊔ lsuc 𝑚 ⊔ lsuc 𝑛)
wfs 𝑚 𝑛 S = WellFoundedSorts {𝑚 = 𝑚} {𝑛} S

private
  variable
    𝑆 : Set 𝑙

-- Definition 4 (term, elimination)

data Var {𝑙} : Set 𝑙 where
  avar : Var
  -- TODO: decide on var representation

data Term {R : Set 𝑙} ⦃ r : Rig R ⦄ {S : Set 𝑚} ⦃ _ : wfs 𝑛 𝑝 S ⦄ : Set (lsuc 𝑙 ⊔ 𝑚)
data Elim {R : Set 𝑙} ⦃ r : Rig R ⦄ {S : Set 𝑚} ⦃ _ : wfs 𝑛 𝑝 S ⦄ : Set (lsuc 𝑙 ⊔ 𝑚)

infix 32 [_x:_]→_ λx,_
data Term {R = R} {S = 𝑆} where
  ⋆ : (i : 𝑆) → Term
  [_x:_]→_ : (r : R) (S : Term) (T : Term) → Term
  λx,_ : (t : Term) → Term
  ⌊_⌋ : (e : Elim) → Term

infix 30 _`_ _꞉_
data Elim {𝑙} where
  var : (x : Var {𝑙}) → Elim
  _`_ : (f : Elim) → (s : Term) → Elim
  _꞉_ : (s : Term) → (S : Term) → Elim

data Expr : Set where
  term elim : Expr

Expr-2-Set :
  (e : Expr)
  {R : Set 𝑙}
  ⦃ _ : Rig R ⦄
  {S : Set 𝑚}
  ⦃ _ : wfs 𝑛 𝑝 S ⦄
  → --------------------
  Set (lsuc 𝑙 ⊔ 𝑚)
Expr-2-Set term = Term
Expr-2-Set elim = Elim

private
  variable
    e : Expr

-- Definition 5 (contraction, reduction, computation)

infix 4 _[_/new]
_[_/new] :
  ⦃ _ : Rig R ⦄
  ⦃ _ : wfs 𝑛 𝑝 𝑆 ⦄
  → -----------------
  Expr-2-Set e → Elim → Expr-2-Set e
e [ f /new] = e

infix 2 _⇝β_ _⇝v_
data _⇝β_ ⦃ _ : Rig R ⦄ ⦃ _ : wfs 𝑛 𝑝 𝑆 ⦄ : Elim → Elim → Prop where
  β : ∀ {π} {s t S T}
    → ----------------------------------------------------
    (λx, t ꞉ ([ π x: S ]→ T)) ` s ⇝β (t ꞉ T) [ s ꞉ S /new]

data _⇝v_ ⦃ _ : Rig R ⦄ ⦃ _ : wfs 𝑛 𝑝 𝑆 ⦄ : Term → Term → Prop where
  v : ∀ {t T}
    → --------------
    ⌊ t ꞉ T ⌋ ⇝v t

data 1-hole-ctx
  {R : Set 𝑙}
  ⦃ _ : Rig R ⦄
  {S : Set 𝑚}
  ⦃ _ : wfs 𝑛 𝑝 S ⦄
  : ------------------------
  Expr → Expr → Set (lsuc 𝑙 ⊔ 𝑚)
data 1-hole-ctx {R = R} where
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
_[_/—] : {R : Set 𝑙} ⦃ _ : Rig R ⦄ {𝑆 : Set 𝑚} ⦃ _ : wfs 𝑛 𝑝 𝑆 ⦄
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
data _⇝_ {R : Set 𝑙} ⦃ _ : Rig R ⦄ {𝑆 : Set 𝑚} ⦃ _ : wfs 𝑛 𝑝 𝑆 ⦄ :
     Expr-2-Set e → Expr-2-Set e → Prop (𝑚 ⊔ lsuc 𝑙) where
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

open import Foundations.Algebra.Relations.ReflexiveTransitiveClosure
  using (refl-trans-close)

infix 1 _↠_
_↠_ : ∀ {R : Set 𝑙} ⦃ _ : Rig R ⦄ {𝑆 : Set 𝑚} ⦃ _ : wfs 𝑛 𝑝 𝑆 ⦄ {e}
  (e₁ : Expr-2-Set e)
  (e₂ : Expr-2-Set e)
  → --------------------
  Prop (𝑚 ⊔ lsuc 𝑙)
_↠_ = refl-trans-close _⇝_

-- Definition 6 (precontext, context)

infix 19 _∥_∶_
data Precontext
  {R : Set 𝑙}
  ⦃ _ : Rig R ⦄
  {𝑆 : Set 𝑚}
  ⦃ _ : wfs 𝑛 𝑝 𝑆 ⦄
  : -----------------
  Set (𝑚 ⊔ lsuc 𝑙)
  where
  · : Precontext
  _∥_∶_ :
    (Γ : Precontext)
    (x : Var {𝑙})
    (S : Term)
    → ----------------
    Precontext

infix 19 _∥_,_∶_
data Context
  {R : Set 𝑙}
  {𝑆 : Set 𝑚}
  ⦃ _ : Rig R ⦄
  ⦃ _ : wfs 𝑛 𝑝 𝑆 ⦄
  : -----------------
  Set (lsuc 𝑙 ⊔ 𝑚)
  where
  · : Context
  
  _∥_,_∶_ :
    (Δ : Context)
    (ρ : R)
    (x : Var {𝑙})
    (S : Term)
    → --------------
    Context

private
  PC : (R : Set 𝑙) (𝑆 : Set 𝑚) ⦃ _ : Rig R ⦄ ⦃ _ : wfs 𝑛 𝑝 𝑆 ⦄ → Set (lsuc 𝑙 ⊔ 𝑚)
  PC R 𝑆 = Precontext {R = R} {𝑆 = 𝑆}

  Ctx : (R : Set 𝑙) (𝑆 : Set 𝑚) ⦃ _ : Rig R ⦄ ⦃ _ : wfs 𝑛 𝑝 𝑆 ⦄ → Set (lsuc 𝑙 ⊔ 𝑚)
  Ctx R 𝑆 = Context {R = R} {𝑆 = 𝑆}

precont : ⦃ _ : Rig R ⦄ ⦃ _ : wfs 𝑛 𝑝 𝑆 ⦄
  (Δ : Ctx R 𝑆)
  → ------------
  PC R 𝑆
precont · = ·
precont (Δ ∥ _ , x ∶ S) = precont Δ ∥ x ∶ S

ctx :
  ⦃ _ : Rig R ⦄
  ⦃ _ : wfs 𝑛 𝑝 𝑆 ⦄
  (Γ : PC R 𝑆)
  (r : R)
  → ----------------
  Ctx R 𝑆
ctx · _ = ·
ctx (Γ ∥ x ∶ S) ρ = (ctx Γ ρ) ∥ ρ , x ∶ S

infix 18 _++_
_++_ : ⦃ _ : Rig R ⦄ ⦃ _ : wfs 𝑛 𝑝 𝑆 ⦄
  (Δ Δ' : Ctx R 𝑆)
  → -----------------
  Ctx R 𝑆
Δ ++ · = Δ
Δ ++ (Δ' ∥ ρ , x ∶ S) = (Δ ++ Δ') ∥ ρ , x ∶ S

infix 18 _pt+_
_pt+_ : ⦃ _ : Rig R ⦄ ⦃ _ : wfs 𝑛 𝑝 𝑆 ⦄
  (Δ Δ' : Ctx R 𝑆)
  → -----------------
  Ctx R 𝑆
Δ pt+ Δ' = {!!}

-- Definition 7 (prejudgement)

_⊢_∋_ :
  ⦃ _ : Rig R ⦄
  ⦃ _ : wfs 𝑚 𝑛 𝑆 ⦄
  (Γ : Precontext)
  (T : Term)
  (t : Term)
  → --------------------
  Prop

_⊢_∈_ :
  ⦃ _ : Rig R ⦄
  ⦃ _ : wfs 𝑚 𝑛 𝑆 ⦄
  (Γ : Precontext)
  (e : Elim)
  (S : Term)
  → --------------------
  Prop

-- Definition 8 (judgment)

infix 17 _⊢_,_∋_
data _⊢_,_∋_
  {R : Set 𝑙}
  {𝑆 : Set 𝑚}
  ⦃ _ : Rig R ⦄
  ⦃ _ : wfs 𝑛 𝑝 𝑆 ⦄
  : ------------------------------
  (Δ : Ctx R 𝑆)
  (ρ : R)
  (T : Term)
  (t : Term)
  → Prop (lsuc 𝑙 ⊔ 𝑚 ⊔ 𝑛)

infix 17 _⊢_,_∈_
data _⊢_,_∈_
  {R : Set 𝑙}
  {𝑆 : Set 𝑚}
  ⦃ _ : Rig R ⦄
  ⦃ _ : wfs 𝑛 𝑝 𝑆 ⦄
  : ------------------------------
  (Δ : Ctx R 𝑆)
  (ρ : R)
  (e : Elim)
  (S : Term)
  → Prop (lsuc 𝑙 ⊔ 𝑚 ⊔ 𝑛)

infix 17 _⊢₀_∋_
_⊢₀_∋_ : 
  {R : Set 𝑙}
  {𝑆 : Set 𝑚}
  ⦃ r : Rig R ⦄
  ⦃ _ : wfs 𝑛 𝑝 𝑆 ⦄
  (Γ : PC R 𝑆)
  (T : Term)
  (t : Term)
  → --------------------
  Prop (lsuc 𝑙 ⊔ 𝑚 ⊔ 𝑛)
_⊢₀_∋_ ⦃ r = r ⦄ Γ T t = ctx Γ r0 ⊢ r0 , T ∋ t

-- Definition 9 (type checking and synthesis)

_≼_ :
  {R : Set 𝑙} {𝑆 : Set 𝑚}
  ⦃ _ : Rig R ⦄ ⦃ _ : wfs 𝑛 𝑝 𝑆 ⦄
  (S T : Term)
  → --------------------------------
  Prop

data _⊢_,_∋_ {𝑙 = 𝑙} {R = R} {𝑆 = 𝑆} where
  pre : {ρ : R} {Δ : Ctx R 𝑆} {T R t : Term}
    (Δ⊢ρT∋t : Δ ⊢ ρ , T ∋ t)
    (T⇝R : T ⇝ R)
    → ------------------------
    Δ ⊢ ρ , R ∋ t

  sort : {j i : 𝑆} {Γ : PC R 𝑆}
    (j≻i : j ≻ i)
    → --------------
    Γ ⊢₀ ⋆ j ∋ ⋆ i
   
  fun : {i : 𝑆} {π : R} {Γ : PC R 𝑆} {T S : Term} {x : Var {𝑙}}
    (Γ⊢₀*ᵢ∋S : Γ ⊢₀ ⋆ i ∋ S)
    (Γ,x:S⊢₀*ᵢ∋T : Γ ∥ x ∶ S ⊢₀ ⋆ i ∋ T)
    → --------------------------------------
    Γ ⊢₀ ⋆ i ∋ [ π x: S ]→ T

  lam : {π ρ : R} {Δ : Ctx R 𝑆} {T S t : Term} {x : Var {𝑙}}
    (Δ,ρπx:S⊢ρT∋t : Δ ∥ ρ * π , x ∶ S ⊢ ρ , T ∋ t)
    → --------------------------------------
    Δ ⊢ ρ , [ π x: S ]→ T ∋ λx, t
  
  elim : {ρ : R} {Δ : Ctx R 𝑆} {T S : Term} {e : Elim}
    (Δ⊢ρe∈S : Δ ⊢ ρ , e ∈ S)
    (S≼T : S ≼ T)
    → --------------------------------------
    Δ ⊢ ρ , T ∋ ⌊ e ⌋


data _⊢_,_∈_ {𝑙 = 𝑙} {R = R} {𝑆 = 𝑆} where
  post : {ρ : R} {Δ : Ctx R 𝑆} {S R : Term} {e : Elim}
    (Δ⊢ρe∈S : Δ ⊢ ρ , e ∈ S)
    (S⇝R : S ⇝ R)
    → ------------------------
    Δ ⊢ ρ , e ∈ R

  var : {ρ : R} {Γ Γ' : PC R 𝑆} {S : Term} {x : Var {𝑙}}
    → -------------------------------------------------
    ctx Γ r0 ∥ ρ , x ∶ S ++ ctx Γ' r0 ⊢ ρ , var x ∈ S

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

