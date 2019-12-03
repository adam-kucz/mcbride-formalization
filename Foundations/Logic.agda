{-# OPTIONS --prop  #-}
module Foundations.Logic where

open import Foundations.Univ using (_⊔_; 𝑙; 𝑚)

record ⊤ : Prop 𝑙 where

instance
  tt : ⊤ {𝑙}
  tt = record {}

data ⊥ {𝑙} : Prop 𝑙 where

⊥elim : {P : Prop 𝑙} → ⊥ {𝑚} → P
⊥elim = λ ()

⊥elimₛ : {A : Set 𝑙} → ⊥ {𝑚} → A
⊥elimₛ = λ ()

infix 10 ¬_
¬_ : (P : Prop 𝑙) → Prop 𝑙
¬_ {𝑙} P = (p : P) → ⊥ {𝑙}

infixl 8 _∨_
data _∨_ (P : Prop 𝑙) (Q : Prop 𝑚) : Prop (𝑙 ⊔ 𝑚) where
  _∨∅ : (l : P) → P ∨ Q
  ∅∨_ : (r : Q) → P ∨ Q

infixl 9 _∧_
record _∧_ (P : Prop 𝑙) (Q : Prop 𝑚) : Prop (𝑙 ⊔ 𝑚) where
  constructor _,_
  field
    left : P
    right : Q

data ∃ (A : Set 𝑙) (Q : A → Prop 𝑚) : Prop (𝑙 ⊔ 𝑚) where
  _,_ : (x : A) (p : Q x) → ∃ A Q

infix 7 ∃
syntax ∃ A (λ x →  Q) = ∃ x ∶ A , Q

open import Foundations.Equality.Core using (_==_)

∃! : (A : Set 𝑙) (Q : A → Prop 𝑚) → Prop (𝑙 ⊔ 𝑚)
∃! A Q = ∃ x ∶ A , (Q x ∧ ∀ y → Q y → y == x)

infix 7 ∃!
syntax ∃! A (λ x →  Q) = ∃! x ∶ A , Q

infixl 5 _↔_
record _↔_ (P : Prop 𝑙) (Q : Prop 𝑚) : Prop (𝑙 ⊔ 𝑚) where
  constructor _,_
  field
    -→ : (p : P) → Q
    ←- : (q : Q) → P
