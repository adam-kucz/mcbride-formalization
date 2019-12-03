{-# OPTIONS --prop  #-}
module Foundations.Functions.Classes where

open import Foundations.Univ using (Level; lsuc; _⊔_; Setω; 𝑙; 𝑚)
open import Foundations.Equality.Core using (_==_; refl)
open import Foundations.Logic

record Injective
    {A : Set 𝑙}
    {B : A → Set 𝑚}
    (f : (x : A) → B x)
    : ------------------
    Set (𝑙 ⊔ 𝑚)
    where
  field
    inj :
      {x y : A}
      (fx==fy : f x == f y)
      → --------------------
      x == y

open Injective ⦃ ... ⦄ public

record Relating
    {𝑙 𝑚 𝑛 𝑝}
    {A : Set 𝑙}
    {B : A → Set 𝑚}
    (f : (x : A) → B x)
    (r : A → A → Prop 𝑛)
    (r' : {x y : A} → B x → B y → Prop 𝑝)
    : --------------------
    Set (𝑙 ⊔ 𝑛 ⊔ 𝑝)
    where
  field
    rel-preserv :
      {a b : A}
      (rab : r a b)
      → -------------
      r' (f a) (f b)

open Relating ⦃ ... ⦄ public

private
  variable
    𝑙₀ 𝑙₁ 𝑙₂ 𝑚₀ 𝑚₁ 𝑚₂ : Level
    A : Set 𝑙
    B : A → Set 𝑚
    f : (x : A) → B x

Congruence :
  ∀ {𝑙 𝑚 𝑛}
  {I : Set 𝑙} {F : I → Set 𝑚} {j : I → I}
  (f : ∀ {i} → F i → F (j i))
  (r : ∀ {i} → F i → F i → Prop 𝑛)
  → --------------------
  Set (𝑙 ⊔ 𝑚 ⊔ 𝑛)
Congruence f r = ∀ i → Relating (f {i}) (r {i}) r

-- a b : F i
-- f {i} : (x : F i) → F (i' x)
-- f : {i} (x : F i) → F (i' x)
-- r : {i} → F i → F i → Prop m

-- a > b
-- →
-- f a > f b

-- TODO: allow heterogenous `a` and `b`
cong : 
  ∀ {𝑙 𝑚 𝑛}
  {I : Set 𝑙}
  {F : I → Set 𝑚}
  {i' : I → I}
  (f : ∀ {i} (x : F i) → F (i' i))
  {r : ∀ {i} → F i → F i → Prop 𝑛}
  {cng : Congruence {F = F} f r}
  {i : I}
  {a b : F i}
  (rab : r a b)
  → ----------------
  r (f a) (f b)
cong f {cng = cong} {i} rab = rel-preserv ⦃ cong i ⦄ rab

infixr 5 _`_
_`_ :
  ∀ {𝑙 𝑚 𝑛}
  {I : Set 𝑙}
  {F : I → Set 𝑚}
  {i' : I → I}
  (f : ∀ {i} (x : F i) → F (i' i))
  {r : ∀ {i} → F i → F i → Prop 𝑛}
  {cng : Congruence {F = F} f r}
  {i : I}
  {a b : F i}
  (rab : r a b)
  → ----------------
  r (f a) (f b)
_`_ = cong

-- infixr 0 _`_
-- _`_ :
--   (f : A → A)
--   {r : A → A → Prop 𝑙}
--   ⦃ _ : Relating f r r ⦄
--   {a b : A}
--   (rab : r a b)
--   → ----------------
--   r (f a) (f b)
-- _`_ = cong

-- infixr 0 _`[_]_
-- _`[_]_ :
--   (f : A → A)
--   (r : A → A → Prop 𝑙)
--   ⦃ _ : Relating f r r ⦄
--   {a b : A}
--   (rab : r a b)
--   → ----------------
--   r (f a) (f b)
-- f `[ r ] rab = cong f {r} rab

instance
  Relating-all-== : Relating f _==_ _==_
  rel-preserv ⦃ Relating-all-== ⦄ refl = refl

  -- TODO (low priority): think of a different approach, this produces too many choice points
  -- Relating-∧-intro :
  --   {A : Set 𝑙₀}
  --   {B : A → Set 𝑙₁}
  --   {C : A → Set 𝑙₂}
  --   {f : (x : A) → B x}
  --   {r : A → A → Prop 𝑚₀}
  --   {r' : {x y : A} → B x → B y → Prop 𝑚₁}
  --   {r'' : {x y : A} → B x → B y → Prop 𝑚₂}
  --   ⦃ _ : Relating f r r' ⦄
  --   ⦃ _ : Relating f r r'' ⦄
  --   → -----------------------------------
  --   Relating f r (λ a b → r' a b ∧ r'' a b)
  -- rel-preserv ⦃ Relating-∧-intro ⦄ rab = rel-preserv rab , rel-preserv rab

  -- Relating-∧-elim-l :
  --   {A : Set 𝑙₀}
  --   {B : A → Set 𝑙₁}
  --   {C : A → Set 𝑙₂}
  --   {f : (x : A) → B x}
  --   {r : A → A → Prop 𝑚₀}
  --   {r' : A → A → Prop 𝑚₁}
  --   {r'' : {x y : A} → B x → B y → Prop 𝑚₂}
  --   ⦃ _ : Relating f r r'' ⦄
  --   → -----------------------------------
  --   Relating f (λ a b → r a b ∧ r' a b) r''
  -- rel-preserv ⦃ Relating-∧-elim-l ⦄ (left , _) = rel-preserv left

  -- Relating-∧-elim-r :
  --   {A : Set 𝑙₀}
  --   {B : A → Set 𝑙₁}
  --   {C : A → Set 𝑙₂}
  --   {f : (x : A) → B x}
  --   {r : A → A → Prop 𝑚₀}
  --   {r' : A → A → Prop 𝑚₁}
  --   {r'' : {x y : A} → B x → B y → Prop 𝑚₂}
  --   ⦃ _ : Relating f r r'' ⦄
  --   → -----------------------------------
  --   Relating f (λ a b → r' a b ∧ r a b) r''
  -- rel-preserv ⦃ Relating-∧-elim-r ⦄ (_ , right) = rel-preserv right

  -- Relating-∨-intro :
  --   {A : Set 𝑙₀}
  --   {B : A → Set 𝑙₁}
  --   {C : A → Set 𝑙₂}
  --   {f : (x : A) → B x}
  --   {r : A → A → Prop 𝑚₀}
  --   {r' : A → A → Prop 𝑚₁}
  --   {r'' : {x y : A} → B x → B y → Prop 𝑚₂}
  --   ⦃ _ : Relating f r r'' ⦄
  --   ⦃ _ : Relating f r' r'' ⦄
  --   → -----------------------------------
  --   Relating f (λ a b → r a b ∨ r' a b) r''
  -- rel-preserv ⦃ Relating-∨-intro ⦄ (rab ∨∅) = rel-preserv rab
  -- rel-preserv ⦃ Relating-∨-intro ⦄ (∅∨ r'ab) = rel-preserv r'ab

  -- Relating-∨-elim-l :
  --   {A : Set 𝑙₀}
  --   {B : A → Set 𝑙₁}
  --   {C : A → Set 𝑙₂}
  --   {f : (x : A) → B x}
  --   {r : A → A → Prop 𝑚₀}
  --   {r' : {x y : A} → B x → B y → Prop 𝑚₁}
  --   {r'' : {x y : A} → B x → B y → Prop 𝑚₂}
  --   ⦃ _ : Relating f r r' ⦄
  --   → -----------------------------------
  --   Relating f r (λ a b → r' a b ∨ r'' a b)
  -- rel-preserv ⦃ Relating-∨-elim-l ⦄ rab = rel-preserv rab ∨∅

  -- Relating-∨-elim-r :
  --   {A : Set 𝑙₀}
  --   {B : A → Set 𝑙₁}
  --   {C : A → Set 𝑙₂}
  --   {f : (x : A) → B x}
  --   {r : A → A → Prop 𝑚₀}
  --   {r' : {x y : A} → B x → B y → Prop 𝑚₁}
  --   {r'' : {x y : A} → B x → B y → Prop 𝑚₂}
  --   ⦃ _ : Relating f r r' ⦄
  --   → -----------------------------------
  --   Relating f r (λ a b → r'' a b ∨ r' a b)
  -- rel-preserv ⦃ Relating-∨-elim-r ⦄ rab = ∅∨ rel-preserv rab

