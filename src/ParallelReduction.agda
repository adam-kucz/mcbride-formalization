{-# OPTIONS --exact-split --prop #-}
open import Basic using (Rig; wfs)
open import PropUniverses

module ParallelReduction
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import ParallelReduction.Definition ⦃ rig ⦄ ⦃ wfs ⦄ public
open import ParallelReduction.Property ⦃ rig ⦄ ⦃ wfs ⦄ public
open import ParallelReduction.Property.VectorizedSubstitution ⦃ rig ⦄ ⦃ wfs ⦄ public
