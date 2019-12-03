{-# OPTIONS --prop  #-}
module Syntax where

open import Univ
  using (Level; lsuc; _⊔_; 𝑙; 𝑚; 𝑛)

-- Definition 1 (rig)

open import Equality
  using (_==_; refl)

record Rig (𝑅 : Set 𝑙) : Set 𝑙  where
  infixl 16 _+_
  infixl 17 _*_
  field
    zero : 𝑅
    _+_ : (π : 𝑅) (ρ : 𝑅) → 𝑅
    _*_ : (π : 𝑅) (ρ : 𝑅) → 𝑅
    0+ : ∀ {ρ} → zero + ρ == ρ
    +assoc : ∀ {ρ π φ} → ρ + (π + φ) == ρ + π + φ
    +comm : ∀ {ρ π} → ρ + π == π + ρ
    *assoc : ∀ {ρ π φ} → ρ * (π * φ) == ρ * π * φ
    0* : ∀ {ρ} → zero * ρ == ρ
    *0 : ∀ {ρ} → ρ * zero == ρ
    *[+]==*+* : ∀ {ρ π φ} → φ * (ρ + π) == φ * ρ + φ * π
    [+]*==*+* : ∀ {ρ π φ} → (ρ + π) * φ  == ρ * φ + π * φ

open import Funct using (_$_)
open import Nat using (ℕ)
open import FinNat
  using (Finℕ; zero; suc; _+s_; _*s_; +s-assoc; +s-comm; *s-assoc; *s-comm; *s-+s-distrib)

fin-rig : (n : ℕ) → Rig (Finℕ $ suc n)
fin-rig n = record
              { zero = zero
              ; _+_ = _+s_
              ; _*_ = _*s_
              ; 0+ = refl
              ; +assoc = +s-assoc
              ; +comm = +s-comm
              ; *assoc = *s-assoc
              ; 0* = refl
              ; *0 = *s-0
              ; *[+]==*+* = *s-+s-distrib
              ; [+]*==*+* = *s-comm ~ *[+]==*+* ~ *s-comm
              }

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

open WellFoundedSorts{{...}} public

wfs : (𝑚 𝑛 : Level) → Set 𝑙 → Set (𝑙 ⊔ lsuc 𝑚 ⊔ lsuc 𝑛)
wfs 𝑚 𝑛 S = WellFoundedSorts {𝑚 = 𝑚} {𝑛} S

-- Definition 4 (term, elimination)

data Var {𝑙} : Set 𝑙 where
  -- TODO: decide on var representation

data Term {S : Set 𝑙} {{_ : wfs 𝑚 𝑛 S}} : Set (lsuc 𝑙)
data Elim {S : Set 𝑙} {{_ : wfs 𝑚 𝑛 S}} : Set (lsuc 𝑙)

infix 7 [x:_]→_ λx,_
data Term {S = 𝑆} where
  ⋆ : (i : 𝑆) → Term
  [x:_]→_ : (S : Term) → (T : Term) → Term
  λx,_ : (t : Term) → Term
  ⌊_⌋ : (e : Elim) → Term

infix 5 _`_ _꞉_
data Elim {𝑙} where
  var : (x : Var {𝑙}) → Elim
  _`_ : (f : Elim) → (s : Term) → Elim
  _꞉_ : (s : Term) → (S : Term) → Elim

-- Definition 5 (contraction, reduction, computation)

infix 4 _[_/new]
_[_/new] : ∀ {𝑆 : Set 𝑙} {{_ : wfs 𝑚 𝑛 𝑆}} → Elim → Elim → Elim
e [ f /new] = e

infix 2 _⇝β_ _⇝v_
data _⇝β_ {𝑆 : Set 𝑙} {{_ : wfs 𝑚 𝑛 𝑆}} : Elim → Elim → Prop 𝑛 where
  β : ∀ {s t S T} → (λx, t ꞉ ([x: S ]→ T)) ` s ⇝β (t ꞉ T) [ s ꞉ S /new]

data _⇝v_ {𝑆 : Set 𝑙} {{_ : wfs 𝑚 𝑛 𝑆}} : Term → Term → Prop 𝑛 where
  v : ∀ {t T} → ⌊ t ꞉ T ⌋ ⇝v t

data Expr : Set where
  term elim : Expr

Expr-2-Set : Expr → ∀ {𝑆 : Set 𝑙} {{_ : wfs 𝑚 𝑛 𝑆}} → Set (lsuc 𝑙)
Expr-2-Set term = Term
Expr-2-Set elim = Elim

-- open import Nat
--   using (ℕ; zero; suc)

-- data 1-hole-ctx {𝑆 : Set 𝑙} {{_ : wfs 𝑚 𝑛 𝑆}} : Expr → Expr → Set (lsuc 𝑙)

-- open import Vec
--   using (Vec; _∷_; []; [_]; [_⸴_]; _!_)

-- [x:-]→[-] : ∀ {𝑆 : Set 𝑙} {{_ : wfs 𝑚 𝑛 𝑆}} {e} → Vec (Vec (Set (lsuc 𝑙)) 2) 2
-- [x:-]→[-] {e = e} = [ [ Term ⸴ 1-hole-ctx e term ] ⸴ [ 1-hole-ctx e term ⸴  Term ] ]


data 1-hole-ctx {𝑆 : Set 𝑙} {{_ : wfs 𝑚 𝑛 𝑆}} : Expr → Expr → Set (lsuc 𝑙) where
  — : ∀ {e}
    → ------------
    1-hole-ctx e e
  
  -- [x:_]→_ : ∀ {e} {n}
  --   (S : [x:-]→[-] {e = e} ! n ! 0)
  --   (T : [x:-]→[-] {e = e} ! n ! 1)
  --   → -----------------------------
  --   1-hole-ctx e term

  [x:_]→_↓ : ∀ {e}
    (S : Term)
    (C[—] : 1-hole-ctx e term)
    → ---------------------
    1-hole-ctx e term

  [x:_↓]→_ : ∀ {e}
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


_[_/—] : {𝑆 : Set 𝑙} {{_ : wfs 𝑚 𝑛 𝑆}}
  {e₁ e₂ : Expr}
  (C[—] : 1-hole-ctx e₁ e₂)
  (e : Expr-2-Set e₁)
  → ----------------------
  Expr-2-Set e₂
— [ e /—] = e
[x: S ]→ C[—] ↓ [ e /—] = [x: S ]→ C[—] [ e /—]
([x: C[—] ↓]→ T) [ e /—] = [x: C[—] [ e /—] ]→ T
(λx, C[—]) [ e /—] = λx, C[—] [ e /—]
⌊ C[—] ⌋ [ e /—] = ⌊ C[—] [ e /—] ⌋
(f ` C[—] ↓) [ e /—] = f ` C[—] [ e /—]
(C[—] ↓` s) [ e /—] = C[—] [ e /—] ` s
(s ∶ C[—] ↓) [ e /—] = s ꞉ C[—] [ e /—]
(C[—] ↓∶ S) [ e /—] = C[—] [ e /—] ꞉ S

infix 1 _⇝'_
data _⇝'_ {𝑆 : Set 𝑙} {{_ : wfs 𝑚 𝑛 𝑆}} :
     {e : Expr} → Expr-2-Set e → Expr-2-Set e → Prop (𝑛 ⊔ lsuc 𝑙) where
  β-exact : ∀ {s t}
    (β : s ⇝β t)
    → -------------
    s ⇝' t

  v-exact : ∀ {s t}
    (v : s ⇝v t)
    → -------------
    s ⇝' t

  hole : ∀ {e₁ e₂} {s t}
    (C[—] : 1-hole-ctx e₁ e₂)
    (reduct : s ⇝' t)
    → --------------------
    C[—] [ s /—] ⇝' C[—] [ t /—]

open import Relations
  using (refl-trans-close)

infix 1 _↠_
_↠_ : ∀ {𝑆 : Set 𝑙} {{_ : wfs 𝑚 𝑛 𝑆}} {e}
  (e₁ : Expr-2-Set e)
  (e₂ : Expr-2-Set e)
  → --------------------
  Prop (𝑛 ⊔ lsuc 𝑙)
_↠_ = refl-trans-close _⇝'_

-- Definition 6 (precontext, context)

data Context {𝑙} {𝑆 : Set 𝑙} {{_ : wfs 𝑚 𝑛 𝑆}} : Set (lsuc 𝑙) where
  ∙ : Context
  _||_ : Context → Var {𝑙} → Term → Context

-- Definition 7 (prejudgement)


