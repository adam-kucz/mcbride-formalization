{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic

module Computation.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Computation.Property.Simple ⦃ rig ⦄ ⦃ wfs ⦄ public
open import Computation.Property.General ⦃ rig ⦄ ⦃ wfs ⦄ public
open import Computation.Property.Alternative ⦃ rig ⦄ ⦃ wfs ⦄ public
-- open import Computation.Property.Equivalence ⦃ rig ⦄ ⦃ wfs ⦄ public
