{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Function.Proof where

open import Foundation.PropUniverses
open import Foundation.Prop'.Identity.Definition using (_==_; refl)
open import Foundation.Logic
open import Foundation.Relation.Binary using (Rel)

record Relating {X : 𝒰 ˙} {A : (x : X) → 𝒱 ˙}
    (f : (x : X) → A x)
    (r : Rel 𝒲 X X)
    (r' : {x y : X} → Rel 𝒯 (A x) (A y))
    : --------------------
    𝒰 ⊔ 𝒲 ⊔ 𝒯 ᵖ
    where
  field
    rel-preserv :
      {a b : X}
      (rab : r a b)
      → -------------
      r' (f a) (f b)

open Relating ⦃ ... ⦄ public

Congruence :
  {I : 𝒰 ˙} {F : (i : I) → 𝒱 ˙} {j : (i : I) → I}
  (f : ∀ {i} → F i → F (j i))
  (r : ∀ {i} → Rel 𝒲 (F i) (F i))
  → --------------------
  𝒰 ⊔ 𝒱 ⊔ 𝒲 ᵖ
Congruence f r = ∀ i → Relating (f {i}) (r {i}) r

-- TODO: allow heterogenous `a` and `b`
cong : {I : 𝒰 ˙} {F : (i : I) → 𝒱 ˙} {i' : (i : I) → I}
  (f : ∀ {i} (x : F i) → F (i' i))
  {r : ∀ {i} → Rel 𝒲 (F i) (F i)}
  {cng : Congruence {F = F} f r}
  {i : I}
  {a b : F i}
  (rab : r a b)
  → ------------
  r (f a) (f b)
cong f {cng = cong} {i} rab = rel-preserv ⦃ cong i ⦄ rab

ap : {I : 𝒰 ˙} {F : (i : I) → 𝒱 ˙} {i' : (i : I) → I}
  (f : ∀ {i} (x : F i) → F (i' i))
  {r : ∀ {i} → Rel 𝒲 (F i) (F i)}
  {cng : Congruence {F = F} f r}
  {i : I}
  {a b : F i}
  (rab : r a b)
  → ----------------
  r (f a) (f b)
ap = cong

instance
  Relating-all-== : {f : (x : X) → A x} → Relating f _==_ _==_
  rel-preserv ⦃ Relating-all-== {f = f} ⦄ (refl x) = refl (f x)

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
