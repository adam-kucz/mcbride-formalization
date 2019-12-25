{-# OPTIONS --exact-split --safe --prop  #-}
module Foundation.Proof where

open import Foundation.PropUniverses

open import Foundation.Type.Sum using (Σ; _,_; pr₁; pr₂; _×_)
open import Foundation.Prop'.Identity.Definition using (_==_; refl)
open import Foundation.Relation.Binary.Definition using (Rel)
open import Foundation.Relation.Binary.Property using (Transitive; trans)

record Composable 𝒵 (R : Rel 𝒯 X Y) (S : Rel 𝒮 Y Z) : 𝒰ω
  where
  field
      rel : Rel 𝒵 X Z
      compose : {x : X} {y : Y} {z : Z} (p : R x y) (q : S y z) → rel x z

instance
  Composable-trans-instance : {X : 𝒰 ˙}
    {R : Rel 𝒱 X X}
    ⦃ p : Transitive R ⦄
    → -----------------
    Composable 𝒱 R R
  Composable.rel (Composable-trans-instance {R = R}) = R
  Composable.compose Composable-trans-instance = trans

  trans-== : ∀ {X : 𝒰 ˙} → Transitive {X = X} _==_
  trans ⦃ trans-== ⦄ p (refl x) = p 

composable-R-== : {X : 𝒰 ˙} {Y : 𝒱 ˙}
  (R : Rel 𝒲 X Y)
  → ------------------
  Composable 𝒲 R _==_
Composable.rel (composable-R-== R) = R
Composable.compose (composable-R-== R) p (refl x) = p

composable-==-R : {X : 𝒰 ˙} {Y : 𝒱 ˙}
  (R : Rel 𝒲 X Y)
  → ------------------
  Composable 𝒲 _==_ R
Composable.rel (composable-==-R R) = R
Composable.compose (composable-==-R R) (refl x) q = q

infix 7 proof_
proof_ : {X : 𝒰 ˙} (x : X) → x == x
proof_ = refl

infix 5 _qed
_qed : {X : 𝒰 ᵖ} (x : X) → X
x qed = x

infixl 6 _〉_〉_:by:_
_〉_〉_:by:_ : {X : 𝒰 ˙} {Y : 𝒱 ˙} {Z : 𝒲 ˙}
  {x : X} {y : Y}
  {_R_ : Rel 𝒯 X Y}
  (p : x R y)
  (_S_ : Rel 𝒮 Y Z)
  (z : Z)
  (q : y S z)
  ⦃ c : Composable 𝒵 _R_ _S_ ⦄
  → -------------------------------------
  Composable.rel c x z
_〉_〉_:by:_ p r a q ⦃ c ⦄  = Composable.compose c p q
