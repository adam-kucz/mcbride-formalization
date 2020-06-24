{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import PropUniverses
open import Basic using (Rig; wfs)

module Computation.Proof
  {𝑅 : 𝒰 ˙} ⦃ rig : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Computation.Definition ⦃ rig ⦄ ⦃ wfs ⦄

open import Relation.Binary
open import Data.Nat
open import Proof

module comp-↠ {n} {tag} where
  open MakeTransComposable (_↠_ {n} {tag}) public

module comp-⇝ {n} {tag} where
  open MakeComposable (_⇝_ {n} {tag}) public
  instance
    Composable-⇝-⇝ = Composable-R-R (_⇝_ {n} {tag})
