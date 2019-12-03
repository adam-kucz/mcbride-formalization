module Sum where

open import Agda.Primitive
  using (Level; lsuc; _⊔_)

private
  variable
    𝑙 𝑚 𝑛 : Level

infix 1 _⊎_
data _⊎_ (A : Set 𝑙) (B : Set 𝑚) : Set (𝑙 ⊔ 𝑚) where
  inl : (x : A) → A ⊎ B
  inr : (x : B) → A ⊎ B

⊎-type : {A B : Set 𝑙} → A ⊎ B → Set 𝑙
⊎-type {A = A} (inl _) = A
⊎-type {B = B} (inr _) = B
