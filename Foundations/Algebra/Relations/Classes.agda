{-# OPTIONS --prop  #-}
module Foundations.Algebra.Relations.Classes where

open import Foundations.Univ using (Level; lsuc; _⊔_; Setω; 𝑙; 𝑚)

private
  variable
    A : Set 𝑙
    r : A → A → Prop 𝑚
    a b c : A

record Relation {A : Set 𝑙} (r : A → A → Prop 𝑚) : Set 𝑙 where

record TransitiveRelation {A : Set 𝑙} (r : A → A → Prop 𝑚) : Set (𝑙 ⊔ 𝑚) where
  field
    {{relation}} : Relation r
    trans :
      (p : r a b)
      (q : r b c)
      → ---------
      r a c

open TransitiveRelation ⦃ ... ⦄ public hiding (relation)

record ReflexiveRelation {A : Set 𝑙} (r : A → A → Prop 𝑚) : Set (𝑙 ⊔ 𝑚) where
  field
    {{relation}} : Relation r
    rflx : r a a

open ReflexiveRelation ⦃ ... ⦄ public hiding (relation)

record SymmetricRelation {A : Set 𝑙} (r : A → A → Prop 𝑚) : Set (𝑙 ⊔ 𝑚) where
  field
    {{relation}} : Relation r
    sym :
      (p : r a b)
      → ---------
      r b a

open SymmetricRelation ⦃ ... ⦄ public hiding (relation)

infix 4 ←_
←_ : ⦃ _ : SymmetricRelation r ⦄ (-→ : r a b) → r b a
←_ = sym
  
record EquivalenceRelation {A : Set 𝑙} (r : A → A → Prop 𝑚) : Set (𝑙 ⊔ 𝑚) where
  field
    {{reflexive}} : ReflexiveRelation r
    {{transitive}} : TransitiveRelation r
    {{symmetric}} : SymmetricRelation r

private
  variable
    𝑙₀ 𝑙₁ 𝑙₂ 𝑚₀ 𝑚₁ 𝑚₂ : Level
    A₀ : Set 𝑙₀
    A₁ : Set 𝑙₁
    A₂ : Set 𝑙₂
    B₀ : A₀ → A₁ → Set 𝑚₀
    B₁ : A₁ → A₂ → Set 𝑚₁
    B₂ : A₀ → A₂ → Set 𝑚₂
    a₀ : A₀
    a₁ : A₁
    a₂ : A₂

record Composable {𝑚₂}
  (r₀ : (a₀ : A₀) (a₁ : A₁) → Prop 𝑚₀)
  (r₁ : (a₁ : A₁) (a₂ : A₂) → Prop 𝑚₁)
  : -----------------------------------
  Setω
  where
  field
    rel : (a₀ : A₀) (a₂ : A₂) → Prop 𝑚₂
    compose : (p : r₀ a₀ a₁) (q : r₁ a₁ a₂) → rel a₀ a₂

open Composable ⦃ ... ⦄ public

instance
  ComposableTrans :
    {A : Set 𝑙}
    {r : A → A → Prop 𝑚}
    ⦃ _ : TransitiveRelation r ⦄
    → ----------------------------------------
    Composable {A₀ = A} {A₁ = A} {A₂ = A} r r
  rel ⦃ ComposableTrans {r = r} ⦄ = r
  compose ⦃ ComposableTrans ⦄ = trans

infixl 3 _〉_〉_:by:_
_〉_〉_:by:_ :
  {r₁ : (a₀ : A₀) (a₁ : A₁) → Prop 𝑚₀}
  (p : r₁ a₀ a₁)
  (r₂ : (a₁ : A₁) (a₂ : A₂) → Prop 𝑚₁)
  (a₂ : A₂)
  (q : r₂ a₁ a₂)
  ⦃ comp : Composable {𝑚₂ = 𝑚₂} r₁ r₂ ⦄
  → -------------------------------------
  rel a₀ a₂
p 〉 r 〉 a :by: q = compose p q

-- infix 4 proof_
-- proof_ : A → A
-- proof x = x

infix 2 _qed
_qed : A → A
x qed = x


-- infixr 2 _〈_〉-[_]_
-- _〈_〉-[_]_ :
--   (a₀ : A₀)
--   (r₁ : (a₀ : A₀) (a₁ : A₁) → Prop 𝑚₀)
--   (p : r₁ a₀ a₁)
--   {r₂ : (a₁ : A₁) (a₂ : A₂) → Prop 𝑚₁}
--   (q : r₂ a₁ a₂)
--   ⦃ comp : Composable {𝑚₂ = 𝑚₂} r₁ r₂ ⦄
--   → -------------------------------------
--   rel a₀ a₂
-- x 〈 r 〉-[ p ] q = compose p q

