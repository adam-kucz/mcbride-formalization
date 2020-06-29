{-# OPTIONS --exact-split --prop #-}
open import Basic
open import PropUniverses

module Subtyping.Similarity.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Subtyping.Similarity.Definition ⦃ rig ⦄ ⦃ wfs ⦄

open import Type.Sum renaming (_,_ to _Σ,_)
open import Data.Nat hiding (_⊔_)
open import Relation.Binary
  hiding (_~_; Reflexive~; Transitive~; Symmetric~)
open import Logic
open import Proof

open import Syntax
open import Syntax.Context
open import Computation

instance
  Reflexive-annot : Reflexive (annot-~ {n = n})
  Symmetric-annot : Symmetric (annot-~ {n = n})
  Transitive-annot : Transitive (annot-~ {n = n})
  postulate
    Reflexive~ : Reflexive (_~_ {n = n}{tag})
    Transitive~ : Transitive (_~_ {n = n}{tag})
  Symmetric~ : Symmetric (_~_ {n = n}{tag})

open import Computation.Equivalence

refl ⦃ Reflexive-annot ⦄ t = go t , go t
  where go : (t : Term n) → annot-~.one-side t t
        go t {π}{S}{T} p = π Σ, S Σ, T , (p , refl S , refl T)

sym ⦃ Symmetric-annot ⦄ (p , q) = q , p

instance
  Transitive-one-side-annot : Transitive (annot-~.one-side {n = n})

trans ⦃ Transitive-one-side-annot ⦄ = go
  where go : ∀{x y z}
          (p : annot-~.one-side x y)
          (p : annot-~.one-side y z)
          {π S T}
          (x↠[πx:S]→T : x ↠ [ π x: S ]→ T)
          → -------------------------------------------------
          ∃ {X = R × Term _ × Term _} λ { (π' Σ, S' Σ, T') →
          z ↠ [ π' x: S' ]→ T' ∧ S ~ S' ∧ T ~ T'}
        go p q x↠[πx:S]→T with p x↠[πx:S]→T
        ... | π' Σ, S' Σ, T' , (y↠[π'x:S']→T' , S~S' , T~T')
          with π″ Σ, S″ Σ, T″ , (z↠[π″x:S″]→T″ , S'~S″ , T'~T″) ←
               q y↠[π'x:S']→T' =
          π″ Σ, S″ Σ, T″ , (
          z↠[π″x:S″]→T″ , trans S~S' S'~S″ , trans T~T' T'~T″)

trans ⦃ Transitive-annot ⦄ (p₀ , p₁)(q₀ , q₁) =
  trans ⦃ Transitive-one-side-annot ⦄ p₀ q₀ ,
  trans ⦃ Transitive-one-side-annot ⦄ q₁ p₁

-- refl ⦃ Reflexive~ {tag = term} ⦄ (⋆ i) = ⋆ i
-- refl ⦃ Reflexive~ {tag = term} ⦄ ([ π x: S ]→ T) =
--   [ π x: refl S ]→ refl T
-- refl ⦃ Reflexive~ {tag = term} ⦄ (λx, t) = λx, refl t
-- refl ⦃ Reflexive~ {tag = term} ⦄ ⌊ e ⌋ = ⌊ refl e ⌋
-- refl ⦃ Reflexive~ {tag = elim} ⦄ (var x) = var x
-- refl ⦃ Reflexive~ {tag = elim} ⦄ (f ` s) = refl f ` refl s
-- refl ⦃ Reflexive~ {tag = elim} ⦄ (s ꞉ S) =
--   ~annot S S (refl s)
--     ({!!} , {!!})
--   where go : annot-~.one-side S S
--         go t {π}{S'}{T} p = π Σ, S' Σ, T , (p , refl S' , refl T)

-- trans ⦃ Transitive~ ⦄ (~annot S _ p p')(~annot _ S″ q q') =
--   ~annot S S″ (trans p q) (trans ⦃ Transitive-annot ⦄ p' q')
-- trans ⦃ Transitive~ ⦄ (⋆ _) q = q
-- trans ⦃ Transitive~ ⦄ (var _) q = q
-- trans ⦃ Transitive~ ⦄ ([ π x: p₀ ]→ p₁)([ π x: q₀ ]→ q₁) =
--   [ π x: trans p₀ q₀ ]→ trans p₁ q₁
-- trans ⦃ Transitive~ ⦄ (λx, p)(λx, q) = λx, trans p q
-- trans ⦃ Transitive~ ⦄ (p₀ ` p₁)(q₀ ` q₁) = trans p₀ q₀ ` trans p₁ q₁
-- trans ⦃ Transitive~ ⦄ ⌊ p ⌋ ⌊ q ⌋ = ⌊ trans p q ⌋

sym ⦃ Symmetric~ ⦄ (~annot S S' p p') =
  ~annot S' S (sym p) (sym ⦃ Symmetric-annot ⦄ p')
sym ⦃ Symmetric~ ⦄ (⋆ i) = ⋆ i
sym ⦃ Symmetric~ ⦄ (var x) = var x
sym ⦃ Symmetric~ ⦄ ([ π x: p₀ ]→ p₁) = [ π x: sym p₀ ]→ sym p₁
sym ⦃ Symmetric~ ⦄ (λx, p) = λx, sym p
sym ⦃ Symmetric~ ⦄ (p₀ ` p₁) = sym p₀ ` sym p₁
sym ⦃ Symmetric~ ⦄ ⌊ p ⌋ = ⌊ sym p ⌋
