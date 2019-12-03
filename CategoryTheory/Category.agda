{-# OPTIONS --prop  #-}
module CategoryTheory.Category where

open import Foundations.Univ using (_⊔_; 𝑙; 𝑚)
open import Foundations.Equality.Core using (_==_; proof_)
open import Foundations.Algebra.Relations.Classes using (_qed; _〉_〉_:by:_)
open import Foundations.Functions.Classes using (_`_)
open import Foundations.Logic using (∃; ∃!; _,_; _∧_)

private
  variable
    Obj : Set 𝑙
    _↝_ : Obj →  Obj → Set 𝑚
    X Y Z W : Obj

record Category
    (Obj : Set 𝑙)
    (_↝_ : Obj →  Obj → Set 𝑚)
    : ---------------------------
    Set (𝑙 ⊔ 𝑚)
  where
  infixl 25 _∘_
  field
    id : X ↝ X
    _∘_ : Y ↝ Z → X ↝ Y → X ↝ Z
    id∘ : (f : X ↝ Y) → id ∘ f == f
    ∘id : (f : X ↝ Y) → f ∘ id == f
    ∘assoc :
      (f : X ↝ Y)
      (g : Y ↝ Z)
      (h : Z ↝ W)
      → -----------------------------
      h ∘ (g ∘ f) == (h ∘ g) ∘ f

open Category ⦃ ... ⦄ public

dom : ⦃ _ : Category Obj _↝_ ⦄ → X ↝ Y → Obj
dom {X = X} _ = X

cod : ⦃ _ : Category Obj _↝_ ⦄ → X ↝ Y → Obj
cod {Y = Y} _ = Y

id'_ : ∀ ⦃ _ : Category Obj _↝_ ⦄ X → X ↝ X
id' x = id {X = x}

iso : ⦃ _ : Category {𝑚 = 𝑚} Obj _↝_ ⦄ (f : X ↝ Y) → Prop 𝑚
iso {_↝_ = _↝_} {X = X} {Y = Y} f = ∃ g ∶ Y ↝ X , f ∘ g == id' Y ∧ g ∘ f == id' X

iso-uniq : ⦃ _ : Category Obj _↝_ ⦄
  (f : X ↝ Y)
  (f-iso : iso f)
  → -------------------------------------------
  ∃! g ∶ Y ↝ X , f ∘ g == id' Y ∧ g ∘ f == id' X
iso-uniq f (g , (fg=id , gf=id)) =
  g ,
  ((fg=id , gf=id) ,
    (λ { g' (fg'=id , g'f=id) →
      proof
        g' 〉 _==_ 〉 g' ∘ id    :by: ← ∘id
           〉 _==_ 〉 g' ∘ f ∘ g :by: g' ∘_ ` ← fg=id
           〉 _==_ 〉 id ∘ g     :by: _∘ g ` g'f=id
           〉 _==_ 〉 g          :by: id∘
      qed}))
