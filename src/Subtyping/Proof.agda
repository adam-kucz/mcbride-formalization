{-# OPTIONS --exact-split --prop #-}
open import Basic
open import PropUniverses

module Subtyping.Proof
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Subtyping.Definition ⦃ rig ⦄ ⦃ wfs ⦄

open import Proof

module comp-~ {m}{tag} where
  open TransMakeComposable (_~_ {m}{tag}) public
module comp-≼ {m}{tag} where
  open TransMakeComposable (_≼_ {m}{tag}) public
