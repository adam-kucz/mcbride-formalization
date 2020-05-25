{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import PropUniverses
open import Basic using (Rig; wfs)

module Computation.Proof
  {𝑅 : 𝒰 ˙} ⦃ rig : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Proof

open import Computation.Definition ⦃ rig ⦄ ⦃ wfs ⦄

module comp-⇝ {n} {tag} where
  open MakeComposable (_⇝_ {n} {tag}) public
module comp-↠ {n} {tag} where
  open MakeTransComposable (_↠_ {n} {tag}) public
