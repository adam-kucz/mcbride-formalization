{-# OPTIONS --exact-split --prop #-}
open import Basic
open import Universes

module Substitution.Property.RenameShift
  {R : 𝒰 ˙} ⦃ r : Rig R ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Renaming ⦃ r ⦄ ⦃ 𝑤𝑓𝑠 ⦄
open import Liftable
open import Substitution.Definition ⦃ r ⦄ ⦃ 𝑤𝑓𝑠 ⦄

open import Syntax
open import Data.Nat
open import Proof

