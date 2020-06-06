{-# OPTIONS --exact-split --prop #-}
open import Universes
open import Basic

module Renaming
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {𝑆 : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Renaming.Definition ⦃ rig ⦄ ⦃ wfs ⦄ public
open import Renaming.Syntax ⦃ rig ⦄ ⦃ wfs ⦄ public
open import Renaming.Property ⦃ rig ⦄ ⦃ wfs ⦄ public
open import Renaming.Instance ⦃ rig ⦄ ⦃ wfs ⦄ public
