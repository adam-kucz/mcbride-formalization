{-# OPTIONS --exact-split --prop #-}
open import Basic
open import PropUniverses

module Subtyping.Similarity
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Subtyping.Similarity.Definition ⦃ rig ⦄ ⦃ wfs ⦄ public
open import Subtyping.Similarity.Property ⦃ rig ⦄ ⦃ wfs ⦄ public
