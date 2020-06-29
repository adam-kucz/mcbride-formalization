{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Computation.Property.Alternative
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Computation.Definition

open import Data.Nat hiding (_⊔_)
open import Relation.Binary
  renaming (refl-trans-close to rtc)
-- open import Relation.Binary.Pointwise
-- open import Proof

open import Syntax ⦃ rig ⦄ ⦃ wfs ⦄
-- open import Syntax.Context
-- open import Substitution
-- open import ParallelReduction
-- open import Computation.Property.General
-- open import Computation.Proof

-- instance
--   Reflexive↠-expl : Reflexive (_↠-expl_ {n = n}{tag})
--   Transitive↠-expl : Transitive (_↠-expl_ {n = n}{tag})

-- refl ⦃ Reflexive↠-expl {tag = term} ⦄ (⋆ i) = ⋆ i
-- refl ⦃ Reflexive↠-expl {tag = term} ⦄ ⌊ e ⌋ = ⌊ refl e ⌋
-- refl ⦃ Reflexive↠-expl {tag = term} ⦄ ([ π x: S ]→ T) = [ π x: refl S ]→ refl T
-- refl ⦃ Reflexive↠-expl {tag = term} ⦄ (λx, t) = λx, refl t
-- refl ⦃ Reflexive↠-expl {tag = elim} ⦄ (var x) = var x
-- refl ⦃ Reflexive↠-expl {tag = elim} ⦄ (f ` s) = refl f ` refl s
-- refl ⦃ Reflexive↠-expl {tag = elim} ⦄ (s ꞉ S) = refl s ꞉ refl S

-- open import Proof

-- trans ⦃ Transitive↠-expl ⦄ = go
--   where go : ∀{tag}{x y z : expr-of-type tag n}
--           (p : x ↠-expl y)(q : y ↠-expl z)
--           → ----------------------------------------
--           x ↠-expl z
--         go (β π p₀ p₁ p₂ p₃)(q₀ ꞉ q₁) = {!!}
--         go (v T p) q = v T $ trans p q
--         go (⋆ i) q = q
--         go (var x) q = q
--         go ([ π x: p₀ ]→ p₁) q = {!!}
--         go (λx, p) q = {!!}
--         go ⌊ p ⌋ (v T q) with p
--         go ⌊ β π p₀ p₁ p₂ p₃ ⌋ (v _ q) | _ = {!!}
--         go ⌊ p₀ ꞉ p₁ ⌋ (v _ q) | _ = v _ $ trans p₀ q
--         go ⌊ p ⌋ ⌊ q ⌋ = {!!}
--         go (p₀ ` p₁) q = {!!}
--         go (p₀ ꞉ p₁) q = {!!}
