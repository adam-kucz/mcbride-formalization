{-# OPTIONS --prop  #-}
module Foundations.Equality.Homogeneous where

open import Foundations.Univ using (𝑙; 𝑚)
open import Foundations.Logic
open import Foundations.Functions.Core using (id)
open import Foundations.Equality.Core

open import Foundations.Functions.Extensionality

private
  variable
    A : Set 𝑙
    a a' : A
    B : Set 𝑚
    b : B

infix 15 _≣_
_≣_ : {A : Set 𝑙} (a a' : A) → Prop 𝑙
_≣_ = _==_

≣→== : (a≣a' : a ≣ a') → a == a'
≣→== refl = refl

==→≣ : (a==a' : a == a') → a ≣ a'
==→≣ refl = refl

-- ==→≣ : {a : A} {b : B} (a==b : a == b) → ∃! f ∶ (B → A) , a ≣ f b
-- ==→≣ {b = a} refl = id , (refl , (λ f a==fa → f==id f (≣→== a==fa)))
--   where f==id : {a : A} (f : A → A) (a==fa : a == f a) → f == id {A = A}
--         f==id {a = a} f a==fa = fun-ext (λ x → {!!})

