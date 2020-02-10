{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import PropUniverses
open import Basic using (Rig; wfs)

module Computation.Proof
  {𝑅 : 𝒰 ˙} ⦃ r : Rig 𝑅 ⦄
  {𝑆 : 𝒱 ˙} ⦃ 𝑤𝑓𝑠 : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Proof

open import Proposition.Identity using (_==_)
open import Computation.Basic ⦃ r ⦄ ⦃ 𝑤𝑓𝑠 ⦄

module comp-⇝ {n} {tag} where
  open MakeComposable (_⇝_ {n} {tag}) public
module comp-↠ {n} {tag} where
  open TransMakeComposable (_↠_ {n} {tag}) public
