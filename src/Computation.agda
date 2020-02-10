{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Computation
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Computation.Basic ⦃ rig ⦄ ⦃ wfs ⦄ public
open import Computation.Property ⦃ rig ⦄ ⦃ wfs ⦄ public
