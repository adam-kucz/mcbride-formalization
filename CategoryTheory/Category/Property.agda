{-# OPTIONS --exact-split --safe --prop #-}
module CategoryTheory.Category.Property where

open import CategoryTheory.Category.Definition

open import Foundation.Universes
open import Foundation.Prop'.Identity using (_==_)
open import Foundation.Logic

open import Foundation.Prop'.Function using (_$_)
open import Foundation.Relation.Binary.Property
open import Foundation.Proof
open import Foundation.Function.Proof

iso-uniq : ⦃ _ : Category 𝒰 𝒱 ⦄ {X Y : obj}
  (f : X ~> Y)
  (f-iso : iso f)
  → -------------------------------------------
  ∃! λ (g : Y ~> X) → f ∘ g == id Y ∧ g ∘ f == id X
iso-uniq {X = X} {Y} f (g , (fg=id , gf=id)) =
  g ,
  ((fg=id , gf=id) ,
    (λ { g' (fg'=id , g'f=id) →
      proof
        g' 〉 _==_ 〉 g' ∘ id Y    :by: sym $ right-unit g'
           〉 _==_ 〉 g' ∘ (f ∘ g) :by: ap (g' ∘_) (sym fg=id)
           〉 _==_ 〉 (g' ∘ f) ∘ g :by: assoc g' f g
           〉 _==_ 〉 id X ∘ g     :by: ap (_∘ g) g'f=id
           〉 _==_ 〉 g            :by: left-unit g
      qed}))
