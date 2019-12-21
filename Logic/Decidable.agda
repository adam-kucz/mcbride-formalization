{-# OPTIONS --prop  #-}
module Foundations.Decidable where

open import Foundations.Univ using (_⊔_; 𝑙; 𝑚)
open import Foundations.Logic using (⊥elim; ¬_; _∨_; _∨∅; ∅∨_; _∧_; _,_; ∃)

data Decided (P : Prop 𝑙) : Set 𝑙 where
  true : (p : P) → Decided P
  false : (¬p : ¬ P) → Decided P

record Decidable (P : Prop 𝑙) : Set 𝑙 where
  field
    decide : Decided P

open Decidable ⦃ ... ⦄ public

private
  variable
    P : Prop 𝑙
    Q : Prop 𝑚

instance
  ¬Decidable : ⦃ _ : Decidable P ⦄ → Decidable (¬ P)
  decide ⦃ ¬Decidable {P = P} ⦄ with decide {P = P}
  decide ¬Decidable | false ¬p = true ¬p
  decide ¬Decidable | true p = false λ ¬p → ¬p p

  ∨Decidable : ⦃ _ : Decidable P ⦄ ⦃ _ : Decidable Q ⦄ → Decidable (P ∨ Q)
  decide ⦃ ∨Decidable {P = P} ⦄ with decide {P = P}
  decide ∨Decidable | true p = true (p ∨∅)
  decide (∨Decidable {Q = Q}) | false _ with decide {P = Q}
  decide ∨Decidable | false _ | true q = true (∅∨ q)
  decide ∨Decidable | false ¬p | false ¬q =
    false λ {
      (p ∨∅) → ⊥elim (¬p p) ;
      (∅∨ q) → ⊥elim (¬q q) }

  ∧Decidable : ⦃ _ : Decidable P ⦄ ⦃ _ : Decidable Q ⦄ → Decidable (P ∧ Q)
  decide ⦃ ∧Decidable {P = P} ⦄ with decide {P = P}
  decide ∧Decidable | false ¬p = false λ { (p , _) → ⊥elim (¬p p) }
  decide (∧Decidable {Q = Q}) | true _ with decide {P = Q}
  decide ∧Decidable | true p | true q = true (p , q)
  decide ∧Decidable | true _ | false ¬q = false λ { (_ , q) → ⊥elim (¬q q) }

  →Decidable : ⦃ _ : Decidable P ⦄ ⦃ _ : Decidable Q ⦄ → Decidable (P → Q)
  decide ⦃ →Decidable {P = P} ⦄ with decide {P = P}
  decide →Decidable | false ¬p = true λ p → ⊥elim (¬p p)
  decide (→Decidable {Q = Q}) | true _ with decide {P = Q}
  decide →Decidable | true _ | true q = true λ _ → q
  decide (→Decidable {𝑙} {P} {𝑚} {Q}) | true p | false ¬q = false λ p→q → ⊥elim (¬q (p→q p))
