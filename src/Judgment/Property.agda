{-# OPTIONS --exact-split --prop  #-}
open import Basic using (Rig; wfs; _≻_)
open import PropUniverses

module Judgment.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Judgment.Definition

open import Relation.Binary
  hiding (_~_; Reflexive~; Transitive~; Symmetric~)
open import Data.Nat hiding (_⊔_)

open import Syntax ⦃ rig ⦄ ⦃ wfs ⦄

instance
  Reflexive~ : Reflexive (_~_ {n = n}{tag})
  Transitive~ : Transitive (_~_ {n = n}{tag})
  Symmetric~ : Symmetric (_~_ {n = n}{tag})

refl ⦃ Reflexive~ {tag = tag} ⦄ t = go tag t
  where go : ∀ tag (t : expr-of-type tag n) → t ~ t
        go term (⋆ i) = ⋆ i
        go term ([ π x: S ]→ T) = [ π x: refl S ]→ refl T
        go term (λx, t) = λx, refl t
        go term ⌊ e ⌋ = ⌊ refl e ⌋
        go elim (var v) = var v
        go elim (f ` s) = refl f ` refl s
        go elim (s ꞉ S) = ~annot (refl s) ? ?
sym ⦃ Symmetric~ ⦄ p = {!!}
trans ⦃ Transitive~ ⦄ p q = {!!}
