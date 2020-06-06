{-# OPTIONS --exact-split --prop #-}
open import Basic
open import PropUniverses

module Subtyping
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Subtyping.Definition public
open import Subtyping.Property public
open import Subtyping.Preservation public
open import Subtyping.Stability public
