{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import Basic
open import Universes

module Renaming
  {R : 𝒰 ˙} ⦃ r : Rig R ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Renaming.Definition ⦃ r ⦄ ⦃ 𝑤𝑓𝑠 ⦄ public
open import Renaming.Syntax ⦃ r ⦄ ⦃ 𝑤𝑓𝑠 ⦄ public
