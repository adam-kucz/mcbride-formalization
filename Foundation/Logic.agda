{-# OPTIONS --exact-split --safe --prop  #-}
module Foundation.Logic where

open import Foundation.PropUniverses
open import Foundation.Prop'.Identity.Definition using (_==_)

open import Foundation.Prop'.Unit using (⊤; ⋆ₚ) public
open import Foundation.Prop'.Empty
  using (⊥; ¬_) renaming (⊥-recursionₚ to ⊥-recursion) public
open import Foundation.Prop'.Sum
  using (∃; _∧_; _,_) renaming (left to ∧left; right to ∧right) public
open import Foundation.Prop'.BinarySum
  using (_∨_; ∨-contract) renaming (left to ∨left; right to ∨right) public

∃! : {X : 𝒰 ˙} (𝐴 : (x : X) → 𝒱 ᵖ) → 𝒰 ⊔ 𝒱 ᵖ
∃! {X = X} 𝐴 = ∃ λ (x : X) → 𝐴 x ∧ ∀ y (p : 𝐴 y) → y == x

infix 11 _↔_
infixl 11 _,_
record _↔_ (𝑋 : 𝒰 ᵖ) (𝑌 : 𝒱 ᵖ) : 𝒰 ⊔ 𝒱 ᵖ where
  constructor _,_
  field
    ⟶ : (p : 𝑋) → 𝑌
    ⟵ : (q : 𝑌) → 𝑋

open _↔_ public
