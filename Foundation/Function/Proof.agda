{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Function.Proof where

open import Foundation.PropUniverses
open import Foundation.Prop'.Identity.Definition using (_==_; refl)
open import Foundation.Logic
open import Foundation.Relation.Binary.Definition using (Rel)

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
      → --------------
      r' (f a) (f b)

open Relating ⦃ ... ⦄ public

ap :
  (f : (x : X) → A x)
  {r : Rel 𝒰 X X}
  {r' : ∀ {a b} → Rel 𝒱 (A a) (A b)}
  ⦃ _ : Relating f r r' ⦄
  {a b : X}
  (rab : r a b)
  → ----------------
  r' (f a) (f b)
ap f = rel-preserv

apₚ :
  (𝐴 : (x : X) → 𝒰 ᵖ)
  {B : (x : X) (p : 𝐴 x) → 𝒱 ˙}
  (f : (x : X) (p : 𝐴 x) → B x p)
  {x y : X}
  (q : x == y)
  {p : 𝐴 x} {p' : 𝐴 y}
  → --------------------------------
  f x p == f y p'
apₚ 𝐴 f (refl x) {p} = refl (f x p)

record ReindexingRelating
  {I : 𝒰 ˙} (F : (i : I) → 𝒱 ˙) {j : (i : I) → I}
  (f : ∀ {i} → F i → F (j i))
  (r : ∀ {i} → Rel 𝒲 (F i) (F i))
  : --------------------
  𝒰 ⊔ 𝒱 ⊔ 𝒲 ᵖ
    where
  field
    reindexed : ∀ i → Relating (f {i}) (r {i}) (r {j i})

open ReindexingRelating ⦃ ... ⦄ public

ap' :
  {I : 𝒰 ˙}  {j : (i : I) → I}
  (F : (i : I) → 𝒱 ˙)
  (f : ∀ {i} → F i → F (j i))
  {r : ∀ {i} → Rel 𝒲 (F i) (F i)}
  ⦃ rr : ReindexingRelating F f r ⦄
  {i : I}
  {a b : F i}
  (rab : r a b)
  → ----------------
  r (f a) (f b)
ap' F f ⦃ rr ⦄ {i} = rel-preserv
  where instance _ = reindexed ⦃ rr ⦄ i

record UniversalPostfix {X : 𝒰 ˙} {Y : 𝒱 ˙}
    (f : (x : X) → Y)
    (_⊑_ : Rel 𝒲 X Y)
    : --------------------
    𝒰 ⊔ 𝒲 ᵖ where
  field
    postfix : ∀ x → x ⊑ f x

postfix :
  (f : (x : X) → Y)
  {_⊑_ : Rel 𝒲 X Y}
  ⦃ post : UniversalPostfix f _⊑_ ⦄
  (x : X)
  → --------------------------------
  x ⊑ f x
postfix f ⦃ post ⦄ = UniversalPostfix.postfix post

record UniversalPrefix {X : 𝒰 ˙} {Y : 𝒱 ˙}
    (f : (x : X) → Y)
    (_⊑_ : Rel 𝒲 Y X)
    : --------------------
    𝒰 ⊔ 𝒲 ᵖ where
  field
    prefix : ∀ x → f x ⊑ x

prefix :
  (f : (x : X) → Y)
  {_⊑_ : Rel 𝒲 Y X}
  ⦃ post : UniversalPrefix f _⊑_ ⦄
  (x : X)
  → --------------------------------
  f x ⊑ x
prefix f ⦃ pre ⦄ = UniversalPrefix.prefix pre

instance
  Relating-all-== : {f : (x : X) → A x} → Relating f _==_ _==_
  rel-preserv ⦃ Relating-all-== {f = f} ⦄ (refl x) = refl (f x)

  RRelating-all-== :
    {I : 𝒰 ˙} {F : (i : I) → 𝒱 ˙} {j : (i : I) → I}
    {f : ∀ {i} → F i → F (j i)}
    → ----------------------------
    ReindexingRelating F f _==_
  reindexed ⦃ RRelating-all-== {f = f} ⦄ i = Relating-all-==
  
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
