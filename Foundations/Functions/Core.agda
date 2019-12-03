{-# OPTIONS --prop  #-}
module Foundations.Functions.Core where

open import Foundations.Univ
  using (Level; _⊔_; 𝑙; 𝑚; 𝑛)

id : {A : Set 𝑙} (x : A) → A
id x = x

idₚ : {P : Prop 𝑙} (p : P) → P
idₚ p = p

∏-syntax : (A : Set 𝑙) (B : A → Set 𝑚) → Set (𝑙 ⊔ 𝑚)
∏-syntax A B = (x : A) → B x

syntax ∏-syntax A (λ x →  B) = ∏ x ∶ A , B

infixr 16 _$_
_$_ : {A : Set 𝑙} {B : A → Set 𝑚} (f : (x : A) → B x) (x : A) → B x
f $ x = f x

infixl 25 _∘_
_∘_ :
  {A : Set 𝑙}
  {B : A → Set 𝑚}
  {C : (x : A) → B x → Set 𝑛}
  (f : {x : A} (y : B x) → C x y)
  (g : (x : A) → B x)
  → ----------------------------
  (x : A) → C x (g x)
(f ∘ g) x = f (g x)

infixl 25 _∘ₚ_
_∘ₚ_ :
  {A : Prop 𝑙}
  {B : A → Prop 𝑚}
  {C : (x : A) → B x → Prop 𝑛}
  (f : {x : A} (y : B x) → C x y)
  (g : (x : A) → B x)
  → ----------------------------
  (x : A) → C x (g x)
(f ∘ₚ g) x = f (g x)

