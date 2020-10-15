{-# OPTIONS --exact-split #-}
open import Basic using (Rig; wfs)
open import Universes

module Substitution
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Substitution.Definition ⦃ rig ⦄ ⦃ wfs ⦄ public
open WithInstanceArgs public 
open import Substitution.Instance ⦃ rig ⦄ ⦃ wfs ⦄ public
open import Substitution.Property ⦃ rig ⦄ ⦃ wfs ⦄ public
open import Substitution.Syntax ⦃ rig ⦄ ⦃ wfs ⦄ public
