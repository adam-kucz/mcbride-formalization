{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Syntax.Context.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax.Context.Property.Substitutable ⦃ rig ⦄ ⦃ wfs ⦄ public
open import Syntax.Context.Property.Substitution ⦃ rig ⦄ ⦃ wfs ⦄ public
open import Syntax.Context.Property.Relation ⦃ rig ⦄ ⦃ wfs ⦄ public
