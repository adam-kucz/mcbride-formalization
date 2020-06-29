{-# OPTIONS --exact-split --prop #-}
open import Basic
open import PropUniverses

module Subtyping.Similarity.Definition
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

-- Definition 17 (subtyping)

open import Data.Nat hiding (_⊔_)
open import Logic
open import Proof

open import Syntax
open import Computation

data _~_ {n} : ∀ {tag} (s t : expr-of-type tag n) → 𝒰 ⁺ ⊔ 𝒱 ᵖ

open import Type.Sum renaming (_,_ to _Σ,_)
open import Relation.Binary hiding (_~_)

module annot-~ where
  one-side : BinRel (𝒰 ⁺ ⊔ 𝒱) (Term n)
  one-side t t' = ∀{π S T}(t↠[πx:S]→T : t ↠ [ π x: S ]→ T) →
    ∃ {X = R × Term _ × Term _} λ { (π' Σ, S' Σ, T') →
    t' ↠ [ π' x: S' ]→ T' ∧ S ~ S' ∧ T ~ T'}

annot-~ : BinRel (𝒰 ⁺ ⊔ 𝒱) (Term n)
annot-~ t t' = annot-~.one-side t t' ∧ annot-~.one-side t' t

infix 36 _~_
data _~_ {n} where
  ~annot : {s s' : Term n}(S S' : Term n)
    (p : s ~ s')
    (q : annot-~ S S')
    → -------------------------------------
    _~_ {n}{elim}(s ꞉ S)(s' ꞉ S')

  ⋆ : ∀ i → ⋆ i ~ ⋆ i

  var : ∀ v → var v ~ var v

  [_x:_]→_ : ∀ π {S S' : Term n}{T T' : Term (n +1)}
    (S▷S' : S ~ S')
    (T▷T' : T ~ T')
    → ---------------
    _~_ {n}{term}([ π x: S ]→ T)([ π x: S' ]→ T')

  λx,_ : {t t' : Term (n +1)}
    (t▷t' : t ~ t')
    → ------------------------------------
    _~_ {n}{term}(λx, t)(λx, t')

  _`_ : {f f' : Elim n}{s s' : Term n}
    (f▷f' : f ~ f')
    (s▷s' : s ~ s')
    → ------------------------------------
    _~_ {n}{elim}(f ` s)(f' ` s')

  ⌊_⌋ : {e e' : Elim n}
    (e▷e' : e ~ e')
    → --------------------
    _~_ {n}{term} ⌊ e ⌋ ⌊ e' ⌋
