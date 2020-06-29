{-# OPTIONS --exact-split --prop #-}
open import Basic using (Rig; wfs)
open import PropUniverses

module ParallelReduction.Definition
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

-- Definition 12 (parallel reduction)

open import Syntax ⦃ rig ⦄ ⦃ wfs ⦄
import Substitution as Subs
open import Computation.Definition
open import Computation.Property.General

private
  _[_/new] = Subs._[_/new] ⦃ subst = Subs.SubstitutableElim ⦄
infix 180 _[_/new]

open import Data.Nat

infix 36 _▷_
data _▷_ {n} : ∀{tag : ExprTag}(s t : expr-of-type tag n) → 𝒰 ⁺ ⊔ 𝒱 ᵖ where
  elim-comp : ∀{t t' : Term n} T
    (t▷t' : t ▷ t')
    → ---------------
    ⌊ t ꞉ T ⌋ ▷ t'

  lam-comp : ∀ π {t t' S S' T T' s s'}
    (t▷t' : t ▷ t')
    (S▷S' : S ▷ S')
    (T▷T' : T ▷ T')
    (s▷s' : s ▷ s')
    → ---------------
    (λx, t ꞉ [ π x: S ]→ T) ` s ▷ (t' ꞉ T') [ (s' ꞉ S') /new]

  ⋆ : (i : S) → _▷_ {n}{term} (⋆ i)(⋆ i)

  var : ∀ v → var v ▷ var v

  [_x:_]→_ : (π : R){S S' : Term n}{T T' : Term (n +1)}
    (S▷S' : S ▷ S')
    (T▷T' : T ▷ T')
    → ---------------
    _▷_ {n}{term} ([ π x: S ]→ T)([ π x: S' ]→ T')

  λx,_ : {t t' : Term (n +1)}
    (t▷t' : t ▷ t')
    → ------------------------------------
    _▷_ {n}{term} (λx, t)(λx, t')

  _`_ : {f f' : Elim n}{s s' : Term n}
    (f▷f' : f ▷ f')
    (s▷s' : s ▷ s')
    → ------------------------------------
    _▷_ {n}{elim} (f ` s)(f' ` s')

  _꞉_ : {s s' S S' : Term n}
    (s▷s' : s ▷ s')
    (S▷S' : S ▷ S')
    → -----------------------
    _▷_ {n}{elim} (s ꞉ S)(s' ꞉ S')

  ⌊_⌋ : {e e' : Elim n}
    (e▷e' : e ▷ e')
    → --------------------
    _▷_ {n}{term} ⌊ e ⌋ ⌊ e' ⌋

-- open import Syntax.Context

-- data _▷_ {n} : ∀ {tag} (s t : expr-of-type tag n) → 𝒰 ⁺ ⊔ 𝒱 ᵖ where
--   elim-comp : ∀{t t' T : Term n}
--     (t▷t' : t ▷ t')
--     → ---------------
--     ⌊ t ꞉ T ⌋ ▷ t'

--   lam-comp : ∀ π {t t' S S' T T' s s'}
--     (t▷t' : t ▷ t')
--     (S▷S' : S ▷ S')
--     (T▷T' : T ▷ T')
--     (s▷s' : s ▷ s')
--     → ---------------
--     (λx, t ꞉ [ π x: S ]→ T) ` s ▷ (t' ꞉ T') [ (s' ꞉ S') /new]

--   ctx : ∀{t tag}
--     (C : Context t tag n)
--     (es es' : all-types t)
--     (p : all-related _▷_ t es es')
--     → ---------------------------------
--     fill-holes es C ▷ fill-holes es' C

-- open import Type.Unit
open import Relation.Binary.Property

instance
  Reflexive▷ : ∀ {n} {tag} → Reflexive (_▷_ {n} {tag})
  -- Reflexive▷' : ∀ {n} {tag} → Reflexive (_▷'_ {n} {tag})

-- refl ⦃ Reflexive▷ {tag = term} ⦄ t =
--   ctx (term t) (↑type ⋆) (↑type ⋆) (↑prop ⋆ₚ)
-- refl ⦃ Reflexive▷ {tag = elim} ⦄ e =
--   ctx (elim e) (↑type ⋆) (↑type ⋆) (↑prop ⋆ₚ)

refl ⦃ Reflexive▷ {tag = term} ⦄ (⋆ i) = ⋆ i
refl ⦃ Reflexive▷ {tag = term} ⦄ ([ π x: S ]→ T) =
  [ π x: refl S ]→ refl T
refl ⦃ Reflexive▷ {tag = term} ⦄ (λx, t) = λx, refl t
refl ⦃ Reflexive▷ {tag = term} ⦄ ⌊ e ⌋ = ⌊ refl e ⌋
refl ⦃ Reflexive▷ {tag = elim} ⦄ (var x) = var x
refl ⦃ Reflexive▷ {tag = elim} ⦄ (f ` s) = refl f ` refl s
refl ⦃ Reflexive▷ {tag = elim} ⦄ (s ꞉ S) = refl s ꞉ refl S

-- instance
--   ▷⊆▷ : (_▷_ {n}{tag}) ⊆ _▷_
--   ▷⊆▷ : (_▷_ {n}{tag}) ⊆ _▷_

-- open import Type.Sum hiding (_,_)
-- open import Logic

-- subrel ⦃ ▷⊆▷ ⦄ (elim-comp t▷t') = elim-comp (subrel t▷t')
-- subrel ⦃ ▷⊆▷ ⦄ (lam-comp π t▷t' S▷S' T▷T' s▷s') =
--   lam-comp π (subrel t▷t')(subrel S▷S')(subrel T▷T')(subrel s▷s')
-- subrel ⦃ ▷⊆▷ ⦄ (ctx (term t) es es' p) = refl t
-- subrel ⦃ ▷⊆▷ ⦄ (ctx (elim e) es es' p) = refl e
-- subrel ⦃ ▷⊆▷ ⦄ (ctx — es es' p) = subrel p
-- subrel ⦃ ▷⊆▷ ⦄ (ctx ([ π x: C₀ ]→ C₁)(l Σ., r)(l' Σ., r')(p₀ , p₁)) =
--   [ π x: subrel (ctx C₀ l l' p₀) ]→ subrel (ctx C₁ r r' p₁)
-- subrel ⦃ ▷⊆▷ ⦄ (ctx (λx, C) es es' p) = λx, subrel (ctx C es es' p)
-- subrel ⦃ ▷⊆▷ ⦄ (ctx ⌊ C ⌋ es es' p) = ⌊ subrel (ctx C es es' p) ⌋
-- subrel ⦃ ▷⊆▷ ⦄ (ctx (C₀ ` C₁)(l Σ., r)(l' Σ., r')(p₀ , p₁)) =
--   subrel (ctx C₀ l l' p₀) ` subrel (ctx C₁ r r' p₁)
-- subrel ⦃ ▷⊆▷ ⦄ (ctx (C₀ ꞉ C₁)(l Σ., r)(l' Σ., r')(p₀ , p₁)) =
--   subrel (ctx C₀ l l' p₀) ꞉ subrel (ctx C₁ r r' p₁)

-- subrel ⦃ ▷⊆▷ ⦄ (elim-comp t▷t') = elim-comp (subrel t▷t')
-- subrel ⦃ ▷⊆▷ ⦄ (lam-comp π t▷t' S▷S' T▷T' s▷s') =
--   lam-comp π (subrel t▷t')(subrel S▷S')(subrel T▷T')(subrel s▷s')
-- subrel ⦃ ▷⊆▷ ⦄ (⋆ i) = refl (⋆ i)
-- subrel ⦃ ▷⊆▷ ⦄ (var v) = refl (var v)
-- subrel ⦃ ▷⊆▷ ⦄ ([ π x: S▷S' ]→ T▷T') =
--   ctx ([ π x: — ]→ —) _ _ (subrel S▷S' , subrel T▷T')
-- subrel ⦃ ▷⊆▷ ⦄ (λx, t▷t') = ctx (λx, —) _ _ (subrel t▷t')
-- subrel ⦃ ▷⊆▷ ⦄ (f▷f' ` s▷s') =
--   ctx (— ` —) _ _ (subrel f▷f' , subrel s▷s')
-- subrel ⦃ ▷⊆▷ ⦄ (s▷s' ꞉ S▷S') =
--   ctx (— ꞉ —) _ _ (subrel s▷s' , subrel S▷S')
-- subrel ⦃ ▷⊆▷ ⦄ ⌊ e▷e' ⌋ = ctx ⌊ — ⌋ _ _ (subrel e▷e')

-- Lemma 13 (parallel reduction computes)

open import Syntax.Context

import Relation.Binary.ReflexiveTransitiveClosure
open import Function.Proof

instance
  ContextClosed▷ : ContextClosed _▷_
  OneContextClosed▷ : OneContextClosed _▷_

open import Logic

ctx-closed ⦃ ContextClosed▷ ⦄ (term t) p = refl t
ctx-closed ⦃ ContextClosed▷ ⦄ (elim e) p = refl e
ctx-closed ⦃ ContextClosed▷ ⦄ — p = p
ctx-closed ⦃ ContextClosed▷ ⦄ ([ π x: C₀ ]→ C₁)(p₀ , p₁) =
  [ π x: ctx-closed C₀ p₀ ]→ ctx-closed C₁ p₁
ctx-closed ⦃ ContextClosed▷ ⦄ (λx, C) p = λx, ctx-closed C p
ctx-closed ⦃ ContextClosed▷ ⦄ ⌊ C ⌋ p = ⌊ ctx-closed C p ⌋
ctx-closed ⦃ ContextClosed▷ ⦄ (C₀ ` C₁)(p₀ , p₁) =
  ctx-closed C₀ p₀ ` ctx-closed C₁ p₁
ctx-closed ⦃ ContextClosed▷ ⦄ (C₀ ꞉ C₁)(p₀ , p₁) =
  ctx-closed C₀ p₀ ꞉ ctx-closed C₁ p₁
OneContextClosed▷ = OneCtxClosed-of-CtxClosed

open import Data.Nat

instance
  ⇝-⊆-▷ : (_⇝_ {n = n}{tag}) ⊆ (_▷_ {n = n}{tag})

subrel ⦃ ⇝-⊆-▷ ⦄ (β π s S t T) =
  lam-comp π (refl t) (refl S) (refl T) (refl s)
subrel ⦃ ⇝-⊆-▷ ⦄ (v t T) = elim-comp T (refl t)
subrel ⦃ ⇝-⊆-▷ ⦄ (hole C[—] x⇝y) = 1-ctx-closed (subrel ⦃ ⇝-⊆-▷ ⦄ x⇝y) C[—]

open import Proof
open import Computation.Proof

instance
  ▷-⊆-↠ : (_▷_ {n = n}{tag}) ⊆ (_↠_ {n = n}{tag})

subrel ⦃ ▷-⊆-↠ ⦄ (elim-comp {t}{t'} T t▷t') =
  proof ⌊ t ꞉ T ⌋
    〉 _⇝_ 〉 t  :by: v t T
    〉 _↠_ 〉 t' :by: subrel t▷t'
  qed
subrel ⦃ ▷-⊆-↠ ⦄
  (lam-comp π {t}{t'}{S}{S'}{T}{T'}{s}{s'} t▷t' S▷S' T▷T' s▷s') =
  proof (λx, t ꞉ [ π x: S ]→ T) ` s
    〉 _↠_ 〉 (λx, t' ꞉ [ π x: S' ]→ T') ` s'
      :by: ctx-closed
             ((λx, — ꞉ [ π x: — ]→ —) ` —)
             (subrel t▷t' , (subrel S▷S' , subrel T▷T') , subrel s▷s')
    〉 _⇝_ 〉 (t' ꞉ T') [ s' ꞉ S' /new]
      :by: β π s' S' t' T'
  qed
subrel ⦃ ▷-⊆-↠ ⦄ (⋆ i) = refl (⋆ i)
subrel ⦃ ▷-⊆-↠ ⦄ (var x) = refl (var x)
subrel ⦃ ▷-⊆-↠ ⦄ ([ π x: S▷S' ]→ T▷T') =
  ctx-closed ([ π x: — ]→ —)
    (subrel {_P_ = _↠_} S▷S' , subrel {_P_ = _↠_} T▷T')
subrel ⦃ ▷-⊆-↠ ⦄ (λx, t▷t') =
  ctx-closed (λx, —) $ subrel {_P_ = _↠_} t▷t'
subrel ⦃ ▷-⊆-↠ ⦄ (f▷f' ` s▷s') =
  ctx-closed (— ` —) (subrel {_P_ = _↠_} f▷f' , subrel {_P_ = _↠_} s▷s')
subrel ⦃ ▷-⊆-↠ ⦄ (s▷s' ꞉ S▷S') =
  ctx-closed (— ꞉ —) (subrel {_P_ = _↠_} s▷s' , subrel {_P_ = _↠_} S▷S')
subrel ⦃ ▷-⊆-↠ ⦄ ⌊ e▷e' ⌋ =
  ctx-closed ⌊ — ⌋ $ subrel {_P_ = _↠_} e▷e'
