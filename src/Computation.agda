{-# OPTIONS --exact-split #-}
open import Universes
open import Basic using (Rig; wfs)

module Computation
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Computation.Definition ⦃ rig ⦄ ⦃ wfs ⦄ public
open import Computation.Property ⦃ rig ⦄ ⦃ wfs ⦄ public
