{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Relation.Binary where

open import Foundation.PropUniverses
open import Foundation.Prop'.Identity.Definition using (_==_; _≠_)
open import Foundation.Logic using (¬_; _∨_; _∧_)

Rel : (𝒰 : Universe) (X : 𝒱 ˙) (Y : 𝒲 ˙) → 𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲 ˙
Rel 𝒰 X Y = (x : X) (y : Y) → 𝒰 ᵖ

RelProperty : 𝒰ω
RelProperty = {𝒰 𝒱 : Universe} {X : 𝒱 ˙} (R : Rel 𝒰 X X) → 𝒰 ⊔ 𝒱 ᵖ

reflexive irreflexive : RelProperty
left-quasi-reflexive right-quasi-reflexive quasi-reflexive : RelProperty
symmetric antisymmetric asymmetric : RelProperty
transitive equivalence : RelProperty
connex semiconnex : RelProperty

transitive _R_ = ∀ {x y z} (p : x R y) (q : y R z) → x R z

reflexive _R_ = ∀ x → x R x

symmetric _R_ = ∀ {x y} (p : x R y) → y R x

equivalence R = transitive R ∧ reflexive R ∧ symmetric R

irreflexive _R_ = ∀ x → ¬ x R x

left-quasi-reflexive _R_ = ∀ {x y} (p : x R y) → x R x

right-quasi-reflexive _R_ = ∀ {x y} (p : x R y) → y R y

quasi-reflexive R = left-quasi-reflexive R ∧ right-quasi-reflexive R

antisymmetric _R_ = ∀ {x y} (p : x R y) (q : y R x) → x == y

asymmetric _R_ = ∀ {x y} (p : x R y) → ¬ y R x

connex _R_ = ∀ x y → x R y ∨ y R x

semiconnex _R_ = ∀ {x y} (p : x ≠ y) → x R y ∨ y R x
