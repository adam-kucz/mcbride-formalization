{-# OPTIONS --exact-split --prop #-}
open import Basic
open import Universes

module Liftable
  {R : 𝒰 ˙} ⦃ r : Rig R ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Liftable.Definition ⦃ r ⦄ ⦃ 𝑤𝑓𝑠 ⦄ public
open import Liftable.Property ⦃ r ⦄ ⦃ 𝑤𝑓𝑠 ⦄ public

