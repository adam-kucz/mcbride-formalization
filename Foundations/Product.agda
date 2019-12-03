{-# OPTIONS --prop #-}
module Product where

open import Univ
  using (Level; lsuc; _⊔_; 𝑙; 𝑚)

infix 2 _,_
data ∑ (A : Set 𝑙) (B : A → Set 𝑚) : Set (𝑙 ⊔ 𝑚) where
  _,_ : (x : A) (y : B x) → ∑ A B

-- {-# BUILTIN SIGMA ∑ #-}

infix 2 ∑
syntax ∑ A (λ x → B) = ∑ x ∶ A , B

_×_ : (A : Set 𝑙) (B : Set 𝑚) → Set (𝑙 ⊔ 𝑚)
A × B = ∑ _ ∶ A , B
