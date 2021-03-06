{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Syntax.Context.OneHole
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax.Context.OneHole.Definition public
open import Syntax.Context.OneHole.Equivalence public
open import Syntax.Context.OneHole.Property public
