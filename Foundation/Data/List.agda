{-# OPTIONS --prop  #-}
module List where

open import Univ
  using (Level; lsuc; _⊔_; 𝑙)

infixr 8 _∷_
data List (A : Set 𝑙) : Set 𝑙 where
  []  : List A
  _∷_ : (h : A) (t : List A) → List A

open import Nat
  using (ℕ; zero; suc; _+_; _<_; s<s→-<-)

len : {A : Set 𝑙} (l : List A) → ℕ
len [] = 0
len (x ∷ l) = 1 + len l

infixr 5 _!_[_]
_!_[_] : {A : Set 𝑙} (l : List A) (n : ℕ) (p : n < len l) → A
h ∷ _ ! zero [ _ ] = h
_ ∷ l ! suc n [ p ] = l ! n [ s<s→-<- p ]

pattern [_] a₀ = a₀ ∷ []
pattern [_⸴_] a₀ a₁ = a₀ ∷ a₁ ∷ []
pattern [_⸴_⸴_] a₀ a₁ a₂ = a₀ ∷ a₁ ∷ a₂ ∷ []
pattern [_⸴_⸴_⸴_] a₀ a₁ a₂ a₃ = a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []
