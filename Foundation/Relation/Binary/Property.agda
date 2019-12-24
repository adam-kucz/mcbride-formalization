{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Relation.Binary.Property where

open import Foundation.PropUniverses
open import Foundation.Relation.Binary.Definition
open import Foundation.Prop'.Identity.Definition using (_==_; _≠_)
open import Foundation.Logic using (¬_; _∨_; _∧_; ⊥)

private
  module RelProp (property : RelProperty) where
    record Property {X : 𝒰 ˙} (R : Rel 𝒱 X X) : 𝒰 ⊔ 𝒱 ᵖ where
      field
        prop-name : property R

    open Property ⦃ … ⦄ public

open RelProp (λ _R_ → ∀ {x y z} (p : x R y) (q : y R z) → x R z)
  renaming (Property to Transitive; prop-name to trans) public
open RelProp (λ _R_ → ∀ x → x R x)
  renaming (Property to Reflexive; prop-name to refl) public
open RelProp (λ _R_ → ∀ x → ¬ x R x)
  renaming (Property to Irreflexive; prop-name to irrefl) public
open RelProp (λ _R_ → ∀ {x y} (p : x R y) → y R x)
  renaming (Property to Symmetric; prop-name to sym) public
open RelProp (λ _R_ → ∀ {x y} (p : x R y) (q : y R x) → x == y)
  renaming (Property to Antisymmetric; prop-name to antisym) public
open RelProp (λ _R_ → ∀ {x y} (p : x R y) → ¬ y R x)
  renaming (Property to Asymmetric; prop-name to asym) public
open RelProp (λ _R_ → ∀ x y → x R y ∨ y R x)
  renaming (Property to Connex; prop-name to total) public
open RelProp (λ _R_ → ∀ {x y} (p : x ≠ y) → x R y ∨ y R x)
  renaming (Property to Semiconnex; prop-name to semicon) public
open RelProp (λ _R_ → ∀ {x y} (p : x R y) → x R x) public
  renaming (Property to LeftQuasiReflexive; prop-name to left-quasirefl)
open RelProp (λ _R_ → ∀ {x y} (p : x R y) → y R y) public
  renaming (Property to RightQuasiReflexive; prop-name to right-quasirefl)

instance
  DefaultSemiconnex :
    {R : Rel 𝒰 X X}
    ⦃ _ : Connex R ⦄
    → -------------------------
    Semiconnex R
  semicon ⦃ DefaultSemiconnex ⦄ {x} {y} _ = total x y

record Equivalence {X : 𝒱 ˙} (R : Rel 𝒰 X X) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    ⦃ equiv-reflexive ⦄ : Reflexive R
    ⦃ equiv-symmetric ⦄ : Symmetric R
    ⦃ equiv-transitive ⦄ : Transitive R

open Equivalence ⦃ … ⦄ public

record QuasiReflexive {X : 𝒱 ˙} (R : Rel 𝒰 X X) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    ⦃ qr-left ⦄ : LeftQuasiReflexive R
    ⦃ qr-right ⦄ : RightQuasiReflexive R

open QuasiReflexive ⦃ … ⦄ public

instance
  DefaultEquivalence :
    {R : Rel 𝒰 X X}
    ⦃ _ : Reflexive R ⦄
    ⦃ _ : Symmetric R ⦄
    ⦃ _ : Transitive R ⦄
    → -------------------------
    Equivalence R
  DefaultEquivalence = record {}

  DefaultQuasiReflexive :
    {R : Rel 𝒰 X X}
    ⦃ _ : LeftQuasiReflexive R ⦄
    ⦃ _ : RightQuasiReflexive R ⦄
    → -------------------------
    QuasiReflexive R
  DefaultQuasiReflexive = record {}

record Minimal {X : 𝒰 ˙} (_≼_ : Rel 𝒱 X X) (⊥ : X) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    minimality : ∀ {x} (p : x ≼ ⊥) → x == ⊥

open Minimal ⦃ … ⦄ public

open import Foundation.Prop'.Sum using (Σₚ; _,_)

-- TODO: put in separate module
Subset : (X : 𝒰 ˙) (𝐴 : (x : X) → 𝒱 ᵖ) → 𝒰 ⊔ 𝒱 ˙ 
Subset X 𝐴 = Σₚ λ (x : X) → 𝐴 x

on-elems : {𝐴 : (x : X) → 𝒰 ᵖ}
  (R : Rel 𝒱 X X)
  → ------------------------------
  Rel 𝒱 (Subset X 𝐴) (Subset X 𝐴)
on-elems _R_ (x , _) (x' , _) = x R x'

open import Foundation.Prop'.Decidable using (Decidable)

record WellFounded {X : 𝒰 ˙}
  (_≼_ : Rel 𝒱 X X)
  (min : ∀ {𝒲}
    (𝐴 : (x : X) → 𝒲 ᵖ)
    ⦃ _ : ∀ {x} → Decidable (𝐴 x) ⦄
    (non-empty : Subset X 𝐴)
    → ------------------------
    Subset X 𝐴)
  : ---------------------------------
  𝒰ω
  where
  field
    well-founded :
      (𝐴 : (x : X) → 𝒲 ᵖ)
      ⦃ _ : ∀ {x} → Decidable (𝐴 x) ⦄
      (non-empty : Subset X 𝐴)
      → -----------------------
      Minimal (on-elems _≼_) (min 𝐴 non-empty)

open WellFounded ⦃ … ⦄ public

infix 21 _⊆_
record _⊆_ {X : 𝒰 ˙} {Y : 𝒱 ˙} (_R_ : Rel 𝒲 X Y) (_P_ : Rel 𝒯 X Y) : 𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ᵖ
  where
  field
    subrel : ∀ {x} {y} (xRy : x R y) → x P y

open _⊆_ ⦃ … ⦄ public

infix 19 _~_
record _~_ {X : 𝒰 ˙} {Y : 𝒱 ˙} (R : Rel 𝒲 X Y) (P : Rel 𝒯 X Y) : 𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ᵖ
  where
  field
    ⦃ ~-⊆ ⦄ : R ⊆ P
    ⦃ ~-⊇ ⦄ : P ⊆ R
