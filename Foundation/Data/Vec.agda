{-# OPTIONS --prop  #-}
module Vec where

open import Univ
  using (Level; lsuc; _⊔_; 𝑙)

open import Nat
  using (ℕ; Finℕ; suc; zero; _+_; _<_; s<s→-<-)

infixr 8 _∷_
data Vec (A : Set 𝑙) : (n : ℕ) → Set 𝑙 where
  []  : Vec A 0
  _∷_ : ∀ {n} (h : A) (t : Vec A n) → Vec A (suc n)

infixr 5 _!_[_]
_!_[_] : ∀ {A : Set 𝑙} {n} (v : Vec A n) (m : ℕ) (p : m < n) → A
h ∷ _ ! zero [ _ ] = h
_ ∷ l ! suc n [ p ] = l ! n [ s<s→-<- p ]

infixl 5 _!_
_!_ : ∀ {A : Set 𝑙} {n} (v : Vec A n) (m : Finℕ n) → A
h ∷ _ ! zero = h
_ ∷ t ! suc n = t ! n

pattern [_] a₀ = a₀ ∷ []
pattern [_⸴_] a₀ a₁ = a₀ ∷ a₁ ∷ []
pattern [_⸴_⸴_] a₀ a₁ a₂ = a₀ ∷ a₁ ∷ a₂ ∷ []
pattern [_⸴_⸴_⸴_] a₀ a₁ a₂ a₃ = a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []
