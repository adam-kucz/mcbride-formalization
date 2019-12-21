{-# OPTIONS --exact-split --safe --prop  #-}
module Foundation.Prop'.Decidable where

open import Foundation.PropUniverses
open import Foundation.Logic
open import Foundation.Prop'.Function using (_$_)

data Decidable (𝑋 : 𝒰 ᵖ) : 𝒰 ˙ where
  true : (p : 𝑋) → Decidable 𝑋
  false : (¬p : ¬ 𝑋) → Decidable 𝑋

decide : (𝑋 : 𝒰 ᵖ) ⦃ d : Decidable 𝑋 ⦄ → Decidable 𝑋
decide 𝑋 ⦃ d ⦄ = d

instance
  ¬Decidable : ⦃ p : Decidable 𝑋 ⦄ → Decidable (¬ 𝑋)
  ¬Decidable ⦃ true p ⦄ = false λ ¬p → ¬p p
  ¬Decidable ⦃ false ¬p ⦄ = true ¬p

  ∨Decidable : ⦃ p : Decidable 𝑋 ⦄ ⦃ q : Decidable 𝑌 ⦄ → Decidable (𝑋 ∨ 𝑌)
  ∨Decidable ⦃ true p ⦄ ⦃ q ⦄ = true (∨left p)
  ∨Decidable ⦃ false ¬p ⦄ ⦃ true q ⦄ = true (∨right q)
  ∨Decidable ⦃ false ¬p ⦄ ⦃ false ¬q ⦄ =
    false λ { (∨left p) → ¬p p ; (∨right q) → ¬q q}

  ∧Decidable : ⦃ p : Decidable 𝑋 ⦄ ⦃ q : Decidable 𝑌 ⦄ → Decidable (𝑋 ∧ 𝑌)
  ∧Decidable ⦃ false ¬p ⦄ ⦃ q ⦄ = false λ p∧q → ¬p $ ∧left p∧q
  ∧Decidable ⦃ true p ⦄ ⦃ false ¬q ⦄ = false λ p∧q → ¬q $ ∧right p∧q
  ∧Decidable ⦃ true p ⦄ ⦃ true q ⦄ = true (p , q)

  →Decidable : ⦃ p : Decidable 𝑋 ⦄ ⦃ q : Decidable 𝑌 ⦄ → Decidable (𝑋 → 𝑌)
  →Decidable {𝑌 = 𝑌} ⦃ false ¬p ⦄ ⦃ q ⦄ = true λ p → ⊥-recursion 𝑌 (¬p p)
  →Decidable ⦃ true p ⦄ ⦃ true q ⦄ = true λ _ → q
  →Decidable ⦃ true p ⦄ ⦃ false ¬q ⦄ = false λ p→q → ¬q $ p→q p

  ↔Decidable : ⦃ p : Decidable 𝑋 ⦄ ⦃ q : Decidable 𝑌 ⦄ → Decidable (𝑋 ↔ 𝑌)
  ↔Decidable ⦃ true p ⦄ ⦃ true q ⦄ = true ((λ p → q) , (λ q → p))
  ↔Decidable ⦃ true p ⦄ ⦃ false ¬q ⦄ = false (λ z → ¬q (_↔_.⟶ z p))
  ↔Decidable ⦃ false ¬p ⦄ ⦃ true q ⦄ = false (λ z → ¬p (_↔_.⟵ z q))
  ↔Decidable {𝑋 = 𝑋} {𝑌 = 𝑌} ⦃ false ¬p ⦄ ⦃ false ¬q ⦄ =
    true ((λ p → ⊥-recursion 𝑌 (¬p p)) ,
          (λ q → ⊥-recursion 𝑋 (¬q q)))
