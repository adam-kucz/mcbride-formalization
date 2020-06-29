{-# OPTIONS --exact-split --prop #-}
open import Basic
open import PropUniverses

module Subtyping.Definition.ToPiType
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

-- Definition 17 (subtyping)

open import Data.Nat hiding (_⊔_)
open import Logic
open import Proof

open import Syntax
open import Computation

▷-to-pi-type : (S : Term n) → 𝒰 ⁺ ⊔ 𝒱 ᵖ
▷-to-pi-type {n = n} S = ∃ λ (T : Term n) → S ▷ T ∧ is-pi-type T
  where open import ParallelReduction

infix 36 _~_
data _~_ {n} : ∀ {tag} (s t : expr-of-type tag n) → 𝒰 ⁺ ⊔ 𝒱 ᵖ where
  ~annot : ∀{s s' : Term n}(S S' : Term n)
    (p : s ~ s')
    (q▷ : ▷-to-pi-type S ↔ ▷-to-pi-type S')
    → -------------------------------------
    s ꞉ S ~ s' ꞉ S'

  ⋆ : ∀ i → ⋆ i ~ ⋆ i

  var : ∀ v → var v ~ var v

  [_x:_]→_ : ∀ π {S S' T T'}
    (S▷S' : S ~ S')
    (T▷T' : T ~ T')
    → ---------------
    [ π x: S ]→ T ~ [ π x: S' ]→ T'

  λx,_ : ∀{t t'}
    (t▷t' : t ~ t')
    → ------------------------------------
    λx, t ~ λx, t'

  _`_ : ∀{f f' s s'}
    (f▷f' : f ~ f')
    (s▷s' : s ~ s')
    → ------------------------------------
    f ` s ~ f' ` s'

  ⌊_⌋ : ∀{e e'}
    (e▷e' : e ~ e')
    → --------------------
    ⌊ e ⌋ ~ ⌊ e' ⌋


open import Syntax.Context.Arbitrary

open import Relation.Binary
  hiding (_~_; Reflexive~; Transitive~; Symmetric~)

instance
  Reflexive~ : Reflexive (_~_ {n = n}{tag})
  Transitive~ : Transitive (_~_ {n = n}{tag})
  Symmetric~ : Symmetric (_~_ {n = n}{tag})
  -- ContextClosed~ : ContextClosed _~_

refl ⦃ Reflexive~ {tag = term} ⦄ (⋆ i) = ⋆ i
refl ⦃ Reflexive~ {tag = term} ⦄ ([ π x: S ]→ T) =
  [ π x: refl S ]→ refl T
refl ⦃ Reflexive~ {tag = term} ⦄ (λx, t) = λx, refl t
refl ⦃ Reflexive~ {tag = term} ⦄ ⌊ e ⌋ = ⌊ refl e ⌋
refl ⦃ Reflexive~ {tag = elim} ⦄ (var x) = var x
refl ⦃ Reflexive~ {tag = elim} ⦄ (f ` s) = refl f ` refl s
refl ⦃ Reflexive~ {tag = elim} ⦄ (s ꞉ S) =
  ~annot S S (refl s) (refl _)

trans ⦃ Transitive~ ⦄ (~annot S _ p p')(~annot _ S″ q q') =
  ~annot S S″ (trans p q) (trans p' q')
trans ⦃ Transitive~ ⦄ (⋆ _) q = q
trans ⦃ Transitive~ ⦄ (var _) q = q
trans ⦃ Transitive~ ⦄ ([ π x: p₀ ]→ p₁)([ π x: q₀ ]→ q₁) =
  [ π x: trans p₀ q₀ ]→ trans p₁ q₁
trans ⦃ Transitive~ ⦄ (λx, p)(λx, q) = λx, trans p q
trans ⦃ Transitive~ ⦄ (p₀ ` p₁)(q₀ ` q₁) = trans p₀ q₀ ` trans p₁ q₁
trans ⦃ Transitive~ ⦄ ⌊ p ⌋ ⌊ q ⌋ = ⌊ trans p q ⌋

sym ⦃ Symmetric~ ⦄ (~annot S S' p p') =
  ~annot S' S (sym p) (sym p')
sym ⦃ Symmetric~ ⦄ (⋆ i) = ⋆ i
sym ⦃ Symmetric~ ⦄ (var x) = var x
sym ⦃ Symmetric~ ⦄ ([ π x: p₀ ]→ p₁) = [ π x: sym p₀ ]→ sym p₁
sym ⦃ Symmetric~ ⦄ (λx, p) = λx, sym p
sym ⦃ Symmetric~ ⦄ (p₀ ` p₁) = sym p₀ ` sym p₁
sym ⦃ Symmetric~ ⦄ ⌊ p ⌋ = ⌊ sym p ⌋

open import Type.Sum renaming (_,_ to _Σ,_)
open import Data.Tree.Binary

{-
ctx-closed ⦃ ContextClosed~ ⦄ (term t) _ = refl t
ctx-closed ⦃ ContextClosed~ ⦄ (elim e) _ = refl e
ctx-closed ⦃ ContextClosed~ ⦄ — p = p
ctx-closed ⦃ ContextClosed~ ⦄ ([ π x: C₀ ]→ C₁)(p₀ , p₁) =
  [ π x: ctx-closed C₀ p₀ ]→ ctx-closed C₁ p₁
ctx-closed ⦃ ContextClosed~ ⦄ (λx, C) p = λx, ctx-closed C p
ctx-closed ⦃ ContextClosed~ ⦄ ⌊ C ⌋ p = ⌊ ctx-closed C p ⌋
ctx-closed ⦃ ContextClosed~ ⦄ (C₀ ` C₁)(p₀ , p₁) =
  ctx-closed C₀ p₀ ` ctx-closed C₁ p₁
ctx-closed ⦃ ContextClosed~ ⦄
  {_ /\ r}{n = n}(C₀ ꞉ C₁){_ Σ, er}{_ Σ, er'}(p₀ , p₁) =
  ~annot _ _ (ctx-closed C₀ p₀)
    (p' C₁ p₁ , p' C₁ (sym ⦃ Symmetric-all-related {t = r} ⦄ p₁))
    (p″ C₁ p₁ , p″ C₁ (sym ⦃ Symmetric-all-related {t = r} ⦄ p₁))
  where p' : ∀ (C : Context r term n){es es'}
             (q₀ : all-related _~_ r es es')
             (q₁ : is-pi-type (fill-holes es C))
             → ---------------------------------------
             is-pi-type (fill-holes es' C)
        p' (term ([ _ x: _ ]→ _)) _ _ = ⋆ₚ
        p' — ([ _ x: _ ]→ _) _ = ⋆ₚ
        p' ([ _ x: _ ]→ _) _ _ = ⋆ₚ
        p″ : ∀ (C : Context r term n){es es'}
             (q₀ : all-related _~_ r es es')
             (q₁ : ▷-to-pi-type (fill-holes es C))
             → ---------------------------------------
             ▷-to-pi-type (fill-holes es' C)
        open import ParallelReduction
        p″ (term _) _ q₁ = q₁
        p″ — q₀ (elem , (left , right)) = {!!}
        p″ ([ π x: C₀ ]→ C₁) q₀ q₁ =
          [ π x: fill-holes _ C₀ ]→ fill-holes _ C₁ , (refl _ , ⋆ₚ)
        p″ (λx, C) q₀ (_ , (λx, _ , ()))
        p″ ⌊ elim (t ꞉ T) ⌋ q₀ (t' , (elim-comp T t▷t' , pi-type-t')) =
          t' , (elim-comp T t▷t' , pi-type-t')
        p″ ⌊ — ⌋ q₀ (elem , (left , right)) = {!!}
        p″ ⌊ C ` C₁ ⌋ q₀ (elem , (left , right)) = {!!}
        p″ ⌊ C ꞉ C₁ ⌋ q₀ (elem , (left , right)) = {!!}
-}
        

data _≼_ : RelOnExpr (𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲) where
  similar : {S T : expr-of-type tag n}
    (p : S ~ T)
    → ----------
    S ≼ T

  sort : ∀{i j}
    (p : j ≻ i)
    → ------------
     _≼_ {n}{term} (⋆ i) (⋆ j)

  [_x:_]→_ : ∀ π {S S' T T'}
    (p : S' ≼ S)
    (q : T ≼ T')
    → ---------------------
    _≼_ {n}{term} ([ π x: S ]→ T)([ π x: S' ]→ T')

-- Lemma 18 (subtyping transitivity)

instance
  Reflexive≼ : Reflexive (_≼_ {n = n}{tag})
  Transitive≼ : Transitive (_≼_ {n = n}{tag})

refl ⦃ Reflexive≼ ⦄ t = similar (refl t)

trans ⦃ Transitive≼ ⦄ (similar p)(similar q) = similar $ trans p q
trans ⦃ Transitive≼ ⦄ (similar (⋆ i))(sort q) = sort q
trans ⦃ Transitive≼ ⦄ (similar ([ π x: p₀ ]→ p₁))([ π x: q₀ ]→ q₁) =
  [ π x: trans q₀ (similar (sym p₀)) ]→ trans (similar p₁) q₁
trans ⦃ Transitive≼ ⦄ (sort p)(similar (⋆ i)) = sort p
trans ⦃ Transitive≼ ⦄ (sort p)(sort q) = sort (trans q p)
trans ⦃ Transitive≼ ⦄ ([ π x: p₀ ]→ p₁)(similar ([ π x: q₀ ]→ q₁)) =
  [ π x: trans (similar (sym q₀)) p₀ ]→ trans p₁ (similar q₁)
trans ⦃ Transitive≼ ⦄ ([ π x: p₀ ]→ p₁)([ π x: q₀ ]→ q₁) =
  [ π x: trans q₀ p₀ ]→ trans p₁ q₁
