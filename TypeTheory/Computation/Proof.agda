{-# OPTIONS --exact-split --prop --safe #-}
open import Foundation.PropUniverses
open import TypeTheory.Basic using (Rig; wfs)

module TypeTheory.Computation.Proof
  {𝑅 : 𝒰 ˙} ⦃ r : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Foundation.Proof

open import Foundation.Prop'.Identity using (_==_)
open import TypeTheory.Computation ⦃ r ⦄ ⦃ 𝑤𝑓𝑠 ⦄

instance
  comp-⇝-== : ∀ {n} {tag} → Composable (𝒰 ⁺ ⊔ 𝒱) (_⇝_ {n} {tag}) _==_
  comp-⇝-== = composable-R-== _⇝_

  comp-==-⇝ : ∀ {n} {tag} → Composable (𝒰 ⁺ ⊔ 𝒱) _==_ (_⇝_ {n} {tag})
  comp-==-⇝ = composable-==-R _⇝_

  comp-↠-== : ∀ {n} {tag} → Composable (𝒰 ⁺ ⊔ 𝒱) (_↠_ {n} {tag}) _==_
  comp-↠-== = composable-R-== _↠_

  comp-==-↠ : ∀ {n} {tag} → Composable (𝒰 ⁺ ⊔ 𝒱) _==_ (_↠_ {n} {tag})
  comp-==-↠ = composable-==-R _↠_
