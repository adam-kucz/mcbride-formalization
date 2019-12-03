{-# OPTIONS --prop  #-}
module Foundations.Equality.Core where

open import Foundations.Univ using (Level; lsuc; _⊔_; 𝑙; 𝑚; 𝑛)

private
  variable
    A A' : Set 𝑙
    a a' : A
    B : Set 𝑚
    b : B

infix 15 _==_
data _==_ {A : Set 𝑙} : A → A' → Prop 𝑙 where
  instance refl : {a : A} → a == a

==→type== :
  {a : A}
  {a' : A'}
  (eq : a == a')
  → ------------
  A == A'
==→type== refl = refl

open import Foundations.Algebra.Relations.Classes

instance
  Relation== : Relation {A = A} _==_
  Relation== = record {}

  ReflexiveRelation== : ReflexiveRelation {A = A} _==_
  rflx ⦃ ReflexiveRelation== ⦄ = refl

  SymmetricRelation== : SymmetricRelation {A = A} _==_
  sym ⦃ SymmetricRelation== ⦄ refl = refl

  TransitiveRelation== : TransitiveRelation {A = A} _==_
  trans ⦃ TransitiveRelation== ⦄ refl refl = refl

-- TODO: remove the need to manually call both of these for all desired relations
composable-r-== :
  (r : A → B → Prop 𝑛)
  → ------------------
  Composable r _==_
rel ⦃ composable-r-== r ⦄ = r
compose ⦃ composable-r-== r ⦄ {a₀ = a₀} p refl = p

composable-==-r :
  (r : A → B → Prop 𝑛)
  → ------------------
  Composable _==_ r
rel ⦃ composable-==-r r ⦄ = r
compose ⦃ composable-==-r r ⦄ {a₀ = a₀} refl p = p

-- infix 3 _qed
-- _qed : (a : A) → a == a
-- x qed = refl

infix 4 proof_
proof_ : (a : A) → a == a
proof _ = refl

