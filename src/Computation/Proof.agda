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

module comp-⇝β {n} where
  open MakeComposable (_⇝β_ {n}) public
  instance
    ⇝β⊆⇝ : (_⇝β_ {n}) ⊆ _⇝_
    Composable⇝β-⇝ : Composable (𝒰 ⁺ ⊔ 𝒱) (_⇝β_ {n}) _⇝_
    Composable⇝-⇝β : Composable (𝒰 ⁺ ⊔ 𝒱) (_⇝_ {n}) _⇝β_
    Composable⇝β-↠ : Composable (𝒰 ⁺ ⊔ 𝒱) (_⇝β_ {n}) _↠_
    Composable↠-⇝β : Composable (𝒰 ⁺ ⊔ 𝒱) (_↠_ {n}) _⇝β_
  subrel ⦃ ⇝β⊆⇝ ⦄ = β-exact
  Composable⇝β-⇝ = Composable-sub-R-P _⇝_ _⇝β_ _⇝_
  Composable⇝-⇝β = Composable-R-sub-P _⇝_ _⇝_ _⇝β_
  Composable⇝β-↠ = Composable-sub-R-P _⇝_ _⇝β_ _↠_
  Composable↠-⇝β = Composable-R-sub-P _↠_ _⇝_ _⇝β_

module comp-⇝v {n} where
  open MakeComposable (_⇝v_ {n}) public
  instance
    ⇝v⊆⇝ : (_⇝v_ {n}) ⊆ _⇝_
    Composable⇝v-⇝ : Composable (𝒰 ⁺ ⊔ 𝒱) (_⇝v_ {n}) _⇝_
    Composable⇝-⇝v : Composable (𝒰 ⁺ ⊔ 𝒱) (_⇝_ {n}) _⇝v_
    Composable⇝v-↠ : Composable (𝒰 ⁺ ⊔ 𝒱) (_⇝v_ {n}) _↠_
    Composable↠-⇝v : Composable (𝒰 ⁺ ⊔ 𝒱) (_↠_ {n}) _⇝v_
  subrel ⦃ ⇝v⊆⇝ ⦄ = v-exact
  Composable⇝v-⇝ = Composable-sub-R-P _⇝_ _⇝v_ _⇝_
  Composable⇝-⇝v = Composable-R-sub-P _⇝_ _⇝_ _⇝v_
  Composable⇝v-↠ = Composable-sub-R-P _⇝_ _⇝v_ _↠_
  Composable↠-⇝v = Composable-R-sub-P _↠_ _⇝_ _⇝v_

