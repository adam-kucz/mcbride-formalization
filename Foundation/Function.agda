{-# OPTIONS --without-K --exact-split --safe #-}
module Foundation.Function where

open import Foundation.Universes
open import Foundation.Type.Product public

id : (x : X) → X
id x = x
  
𝑖𝑑 : (X : 𝒰 ˙) (x : X) → X
𝑖𝑑 X = id

domain : {X : 𝒰 ˙} {A : (x : X) → 𝒱 ˙}
  (f : (x : X) → A x)
  → -----------------
  𝒰 ˙
domain {X = X} _ = X

codomain : {X : 𝒰 ˙} {Y : 𝒱 ˙}
  (f : (x : X) → Y)
  → -----------------
  𝒱 ˙
codomain {Y = Y} _ = Y

type-of : {X : 𝒰 ˙} (x : X) → 𝒰 ˙
type-of {X = X} _ = X

infixr 16 _$_
_$_ : {A : 𝒰 ˙} {B : A → 𝒱 ˙}
  (f : (x : A) → B x)
  (x : A)
  → -----------------------
  B x
f $ x = f x

infixl 25 _∘_
_∘_ :
  {X : 𝒰 ˙}
  {A : (x : X) → 𝒱 ˙}
  {K : (x : X) (y : A x) → 𝒲 ˙}
  (f : {x : X} (y : A x) → K x y)
  (g : (x : X) → A x)
  → ----------------------------
  (x : X) → K x (g x)
(f ∘ g) x = f (g x)

