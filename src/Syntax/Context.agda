{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Syntax.Context
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax.Context.Arbitrary ⦃ rig ⦄ ⦃ wfs ⦄ public
open import Syntax.Context.OneHole ⦃ rig ⦄ ⦃ wfs ⦄ public
open import Syntax.Context.Property ⦃ rig ⦄ ⦃ wfs ⦄ public
