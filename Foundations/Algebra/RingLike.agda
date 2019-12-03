{-# OPTIONS --prop  #-}
module Foundations.Algebra.RingLike where

open import Foundations.Univ using (𝑙)
open import Foundations.Equality.Core using (_==_)
open import Foundations.Algebra.GroupLike using (Semigroup; Monoid; Group; Commutative)
open Monoid using (zero)

private
  variable
    A : Set 𝑙
    a b c : A

record Hemiring (A : Set 𝑙) (_+_ : A → A → A) (_*_ : A → A → A) : Set 𝑙  where
  -- TODO: figure out why these seem to have no effect
  -- infixl 20 _+_
  -- infixl 21 _*_
  field
    {{monoid+}} : Monoid A _+_
    {{commutative+}} : Commutative A _+_
    {{semigroup*}} : Semigroup A _*_
    0* : zero monoid+ * a == zero monoid+
    *0 : a * zero monoid+ == zero monoid+
    *[+]==*+* : a * (b + c) == (a * b) + (a * c)
    [+]*==*+* : (a + b) * c  == (a * c) + (b * c)

open Hemiring {{...}} public

record Semiring (A : Set 𝑙) (_+_ : A → A → A) (_*_ : A → A → A) : Set 𝑙 where
  field
    {{hemiring}} : Hemiring A _+_ _*_
    {{monoid*}} : Monoid A _*_

record Rng (A : Set 𝑙) (_+_ : A → A → A) (_*_ : A → A → A) : Set 𝑙 where
  field
    {{hemiring}} : Hemiring A _+_ _*_
    {{group+}} : Group A _+_

record Ring (A : Set 𝑙) (_+_ : A → A → A) (_*_ : A → A → A) : Set 𝑙 where
  field
    {{semiring}} : Semiring A _+_ _*_
    {{group+}} : Group A _+_
