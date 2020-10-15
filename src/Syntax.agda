{-# OPTIONS --exact-split  #-}
open import Basic using (Rig; wfs)
open import Universes

module Syntax
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax.Definition ⦃ rig ⦄ ⦃ wfs ⦄ public
open import Syntax.Property ⦃ rig ⦄ ⦃ wfs ⦄ public
open import Syntax.Function ⦃ rig ⦄ ⦃ wfs ⦄ public
