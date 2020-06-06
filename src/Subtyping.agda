{-# OPTIONS --exact-split --prop #-}
open import Basic
open import PropUniverses

module Subtyping
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

-- Definition 17 (subtyping)

open import Data.Nat hiding (_⊔_)
open import Syntax.Definition
open import Computation

infix 36 _~_
data _~_ {n} : ∀ {tag} (s t : expr-of-type tag n) → 𝒰 ⁺ ⊔ 𝒱 ᵖ where
  ~annot : ∀{s s'}(S S' : Term n)
    (p : s ~ s')
    -- (p' : (q : ∃ λ t → s == λx, t) →
    --       ∃ λ S₀ → ∃ λ T₀ →
    --       ∃ λ S₁ → ∃ λ T₁ →
    --       S ↠ [ π x: ])
    → -------------
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


open import Syntax.Context

open import Relation.Binary hiding (_~_; Reflexive~; Transitive~; Symmetric~)

instance
  Reflexive~ : Reflexive (_~_ {n = n}{tag})
  Transitive~ : Transitive (_~_ {n = n}{tag})
  Symmetric~ : Symmetric (_~_ {n = n}{tag})
  ContextClosed~ : ContextClosed _~_

open import Proof

refl ⦃ Reflexive~ {tag = term} ⦄ (⋆ i) = ⋆ i
refl ⦃ Reflexive~ {tag = term} ⦄ ([ π x: S ]→ T) =
  [ π x: refl S ]→ refl T
refl ⦃ Reflexive~ {tag = term} ⦄ (λx, t) = λx, refl t
refl ⦃ Reflexive~ {tag = term} ⦄ ⌊ e ⌋ = ⌊ refl e ⌋
refl ⦃ Reflexive~ {tag = elim} ⦄ (var x) = var x
refl ⦃ Reflexive~ {tag = elim} ⦄ (f ` s) = refl f ` refl s
refl ⦃ Reflexive~ {tag = elim} ⦄ (s ꞉ S) = ~annot S S $ refl s

trans ⦃ Transitive~ ⦄ (~annot S _ p)(~annot _ S″ q) =
  ~annot S S″ $ trans p q
trans ⦃ Transitive~ ⦄ (⋆ _) q = q
trans ⦃ Transitive~ ⦄ (var _) q = q
trans ⦃ Transitive~ ⦄ ([ π x: p₀ ]→ p₁)([ π x: q₀ ]→ q₁) =
  [ π x: trans p₀ q₀ ]→ trans p₁ q₁
trans ⦃ Transitive~ ⦄ (λx, p)(λx, q) = λx, trans p q
trans ⦃ Transitive~ ⦄ (p₀ ` p₁)(q₀ ` q₁) = trans p₀ q₀ ` trans p₁ q₁
trans ⦃ Transitive~ ⦄ ⌊ p ⌋ ⌊ q ⌋ = ⌊ trans p q ⌋

sym ⦃ Symmetric~ ⦄ (~annot S S' p) = ~annot S' S $ sym p
sym ⦃ Symmetric~ ⦄ (⋆ i) = ⋆ i
sym ⦃ Symmetric~ ⦄ (var x) = var x
sym ⦃ Symmetric~ ⦄ ([ π x: p₀ ]→ p₁) = [ π x: sym p₀ ]→ sym p₁
sym ⦃ Symmetric~ ⦄ (λx, p) = λx, sym p
sym ⦃ Symmetric~ ⦄ (p₀ ` p₁) = sym p₀ ` sym p₁
sym ⦃ Symmetric~ ⦄ ⌊ p ⌋ = ⌊ sym p ⌋

open import Logic

ctx-closed ⦃ ContextClosed~ ⦄ (term t) _ = refl t
ctx-closed ⦃ ContextClosed~ ⦄ (elim e) _ = refl e
ctx-closed ⦃ ContextClosed~ ⦄ — p = p
ctx-closed ⦃ ContextClosed~ ⦄ ([ π x: C₀ ]→ C₁)(p₀ , p₁) =
  [ π x: ctx-closed C₀ p₀ ]→ ctx-closed C₁ p₁
ctx-closed ⦃ ContextClosed~ ⦄ (λx, C) p = λx, ctx-closed C p
ctx-closed ⦃ ContextClosed~ ⦄ ⌊ C ⌋ p = ⌊ ctx-closed C p ⌋
ctx-closed ⦃ ContextClosed~ ⦄ (C₀ ` C₁)(p₀ , p₁) =
  ctx-closed C₀ p₀ ` ctx-closed C₁ p₁
ctx-closed ⦃ ContextClosed~ ⦄ (C₀ ꞉ C₁)(p₀ , p₁) =
  ~annot _ _ $ ctx-closed C₀ p₀

data _≼_ : RelOnExpr (𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲) where
  similar : {S T : expr-of-type tag n}
    (p : S ~ T)
    → ----------
    S ≼ T

  sort : ∀ {i j}
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

-- Lemma 19 (similarity preservation)

open import Substitution
open import ParallelReduction

open import Logic

step-▷-preserves-~ : {S S' T : expr-of-type tag m}
  (p : S ~ T)
  (q : S ▷ S')
  → -------------------------
  ∃ λ T' → S' ~ T' ∧ T ▷ T'
step-▷-preserves-~ (⋆ i) (⋆ i) =
  ⋆ i , (refl (⋆ i) , refl (⋆ i))
step-▷-preserves-~ (var v₁) (var v₁) =
  var v₁ , (refl (var v₁) , refl (var v₁))
step-▷-preserves-~ ([ π x: S~S' ]→ T~T')([ π x: S▷S″ ]→ T▷T″)
  with step-▷-preserves-~ S~S' S▷S″ | step-▷-preserves-~ T~T' T▷T″
step-▷-preserves-~ ([ π x: S~S' ]→ T~T')([ π x: S▷S″ ]→ T▷T″)
  | S‴ , (S'~S‴ , S″▷S‴) | T‴ , (T'~T‴ , T″▷T‴) =
  [ π x: S‴ ]→ T‴ , ([ π x: S'~S‴ ]→ T'~T‴ , [ π x: S″▷S‴ ]→ T″▷T‴)
step-▷-preserves-~ (λx, t~t')(λx, t▷t″) with step-▷-preserves-~ t~t' t▷t″
step-▷-preserves-~ (λx, t~t')(λx, t▷t″) | t‴ , (t'~t‴ , t″▷t‴) =
  λx, t‴ , (λx, t'~t‴ , λx, t″▷t‴)
step-▷-preserves-~ (f~f' ` s~s')(f▷f″ ` s▷s″)
  with step-▷-preserves-~ f~f' f▷f″ | step-▷-preserves-~ s~s' s▷s″
step-▷-preserves-~ (f~f' ` s~s')(f▷f″ ` s▷s″)
  | f‴ , (f'~f‴ , f″▷f‴) | s‴ , (s'~s‴ , s″▷s‴) =
  f‴ ` s‴ , (f'~f‴ ` s'~s‴ , f″▷f‴ ` s″▷s‴)
step-▷-preserves-~ ⌊ e~e' ⌋ ⌊ e▷e″ ⌋ with step-▷-preserves-~ e~e' e▷e″
step-▷-preserves-~ ⌊ e~e' ⌋ ⌊ e▷e″ ⌋ | e‴ , (e'~e‴ , e″▷e‴) =
  ⌊ e‴ ⌋ , (⌊ e'~e‴ ⌋ , ⌊ e″▷e‴ ⌋)
step-▷-preserves-~ (~annot S S' s~s')(s▷s″ ꞉ S▷S″)
  with step-▷-preserves-~ s~s' s▷s″
step-▷-preserves-~ (~annot S S' s~s')(s▷s″ ꞉ S▷S″)
  | s‴ , (s'~s‴ , s″▷s‴) =
  s‴ ꞉ S' , (~annot _ S' s'~s‴ , s″▷s‴ ꞉ refl S')
step-▷-preserves-~
  (~annot ([ π x: _ ]→ _) S' (λx, t~t') ` s~s')
  (lam-comp π t▷t″ S▷S″ T▷T″ s▷s″)
  with step-▷-preserves-~ t~t' t▷t″ | step-▷-preserves-~ s~s' s▷s″
step-▷-preserves-~
  (~annot ([ π x: _ ]→ _) S' (λx, t~t') ` s~s')
  (lam-comp π t▷t″ S▷S″ T▷T″ s▷s″)
  | t‴ , (t'~t‴ , t″▷t‴) | s‴ , (s'~s‴ , s″▷s‴) =
  (t‴ ꞉ {!!}) [ s‴ ꞉ {!!} /new] ,
  ({!!} ,
   {!lam-comp π t″▷t‴ ? ? s″▷s‴!})
step-▷-preserves-~ ⌊ p ⌋ (elim-comp T q) = {!!}

open import Confluence

steps-▷-confluent-~ : {S S' T T' : expr-of-type tag m}
  (p : S ~ T)
  (q : S ▷ S')
  (q' : T ▷ T')
  → -------------------------
  ∃ λ S″ →
  ∃ λ T″ →
  S″ ~ T″ ∧ S' ▷ S″ ∧ T' ▷ T″
-- steps-▷-confluent-~ (~id S) q q' with diamond-▷ q q'
-- steps-▷-confluent-~ (~id S) q q' | S″ , (S'▷S″ , T'▷S″) =
--   S″ , (S″ , (
--   refl S″ , S'▷S″ , T'▷S″))
-- steps-▷-confluent-~ (~annot S T (~id s))(annot s▷s' S▷S')(annot s▷t' S▷T')
--   with diamond-▷ s▷s' s▷t'
-- steps-▷-confluent-~ {S' = s' ꞉ S'}{T' = t' ꞉ T'}
--   (~annot S T (~id s))(annot s▷s' S▷S')(annot s▷t' S▷T')
--   | s″ , (s'▷s″ , t'▷s″) =
--   s″ ꞉ S' , (s″ ꞉ T' , (
--   ~annot S' T' (~id s″) ,
--   annot s'▷s″ (refl S') ,
--   annot t'▷s″ (refl T')))

open import Proposition.Identity hiding (refl)
open import Relation.Binary.ReflexiveTransitiveClosure
  renaming (refl-trans-close to rtc)

step-▷*-preserves-~ : {S S' T : expr-of-type tag m}
  (p : S ~ T)
  (q : rtc _▷_ S S')
  → -------------------------
  ∃ λ T' → S' ~ T' ∧ rtc _▷_ T T'
step-▷*-preserves-~ {T = T} p (rfl S) = T , (p , refl T)
step-▷*-preserves-~ p (step q q')
  with step-▷-preserves-~ p q
step-▷*-preserves-~ p (step q q') | T″ , (S″~T″ , T▷T″)
  with step-▷*-preserves-~ S″~T″ q'
step-▷*-preserves-~ p (step q q')
  | _ , (_ , T▷T″) | T' , (S'~T' , T″▷*T') =
  T' , (S'~T' , step T▷T″ T″▷*T')

step-↠-preserves-~ : {S S' T : expr-of-type tag m}
  (p : S ~ T)
  (q : S ↠ S')
  → -------------------------
  ∃ λ T' → S' ~ T' ∧ T ↠ T'
step-↠-preserves-~ {tag = tag}{m = m}{S = S}{S'} p q
  with step-▷*-preserves-~ p q'
  where _▷*_ = rtc (_▷_ {n = m}{tag})
        q' : S ▷* S'
        q' = subrel q
step-↠-preserves-~ p q | T' , (S'~T' , T▷*T') =
  T' , (S'~T' , subrel ⦃ r ⦄ T▷*T')
  where instance r = subrel-rtc-to-rtc-subrel-rtc

-- TODO: figure out if the `proof` in the paper really doesn't work
postulate
  steps-↠-confluent-~ : {S S' T T' : expr-of-type tag m}
    (p : S ~ T)
    (q : S ↠ S')
    (q' : T ↠ T')
    → -------------------------
    ∃ λ S″ →
    ∃ λ T″ →
    S″ ~ T″ ∧ S' ↠ S″ ∧ T' ↠ T″
-- steps-↠-confluent-~ {tag = tag}{m = m}{S = S}{S'}{T}{T'} p q q'
--   with steps-▷*-confluent-~ p q₁ q₁'
--   where _▷*_ = rtc (_▷_ {n = m}{tag})
--         q₁ : S ▷* S'
--         q₁ = subrel q
--         q₁' : T ▷* T'
--         q₁' = subrel q'
--         steps-▷*-confluent-~ : {S S' T T' : expr-of-type tag m}
--           (p : S ~ T)
--           (q : S ▷* S')
--           (q' : T ▷* T')
--           → -------------------------
--           ∃ λ S″ →
--           ∃ λ T″ →
--           S″ ~ T″ ∧ S' ▷* S″ ∧ T' ▷* T″
--         steps-▷*-confluent-~ p (rfl S) (rfl T) =
--           S , (T , (p , refl S , refl T))
--         steps-▷*-confluent-~ p (rfl S) (step T▷T₁ T₁▷*T')
--           with steps-▷-confluent-~ p (refl S) T▷T₁
--              | step-▷*-preserves-~ p ()
--              steps-▷*-confluent-~ ({!step-▷*-preserves-~!}) (refl S) T₁▷*T'
--         steps-▷*-confluent-~ p (rfl S) (step T▷T₁ T₁▷*T')
--           | S₂ , (T₂ , (S₂~T₂ , S▷S₂ , T₁▷T₂)) | z = {!!}
--         steps-▷*-confluent-~ p (step S▷S₁ S₁▷*S') (rfl T) =
--           {!!}
--         steps-▷*-confluent-~ p (step S▷S₁ S₁▷*S') (step T▷T₁ T₁▷*T') =
--           {!!}
-- steps-↠-confluent-~ _ _ _ | S″ , (T″ , (S″~T″ , S'▷*S″ , T'▷*T″)) =
--   S″ , (T″ , (S″~T″ , subrel ⦃ r ⦄ S'▷*S″ , subrel ⦃ r ⦄ T'▷*T″))
--   where instance r = subrel-rtc-to-rtc-subrel-rtc

-- Lemma 20 (subtyping preservation)

open import Type.Sum hiding (_,_)

step-↠-preserves-≼ : {S S' T : expr-of-type tag m}
  (p : S ≼ T)
  (q : S ↠ S')
  → -------------------------
  ∃ λ T' → S' ≼ T' ∧ T ↠ T'
step-↠-preserves-≽ : {S T T' : expr-of-type tag m}
  (p : S ≼ T)
  (q : T ↠ T')
  → -------------------------
  ∃ λ S' → S' ≼ T' ∧ S ↠ S'

-- step-↠-preserves-≼ (similar p) q with step-↠-preserves-~ p q
-- step-↠-preserves-≼ (similar p) q | T' , (S'~T' , T↠T') =
--   T' , (similar S'~T' , T↠T')
-- step-↠-preserves-≼ (sort {j = j} p) (rfl (⋆ i)) =
--   ⋆ j , (sort p  , refl (⋆ j))
-- step-↠-preserves-≼ (sort _) (step ⋆i⇝S' _) =
--   ⊥-recursion _ (sorts-don't-reduce ⋆i⇝S' (refl (⋆ _)))
-- step-↠-preserves-≼ (pi π S″≼S T≼T″) q = {!!}
-- step-↠-preserves-≼ (pi π S″≼S T≼T″) q with pi-compute-forms q
-- step-↠-preserves-≼ (pi π S″≼S T≼T″) q
--   | S' Σ., T' , (S↠S' , T↠T' , Id.refl ([ π x: S' ]→ T'))
--   with step-↠-preserves-≼ T≼T″ T↠T' | step-↠-preserves-≽ S″≼S S↠S'
-- step-↠-preserves-≼ (pi π S″≼S T≼T″) q
--   | S' Σ., T' , (S↠S' , T↠T' , Idₚ.refl _)
--   | T₁ , (T'≼T₁ , T″↠T₁)
--   | S₁ , (S₁≼S' , S″↠S₁) =
--   [ π x: S₁ ]→ T₁ ,
--   (pi π S₁≼S' T'≼T₁ ,
--    ctx-closed ([ π x: — ]→ —) (S″↠S₁ , T″↠T₁))

-- step-↠-preserves-≽ (similar p) q with step-↠-preserves-~ (sym p) q
-- step-↠-preserves-≽ (similar p) q | T' , (S'~T' , T↠T') =
--   T' , (similar (sym S'~T') , T↠T')
-- step-↠-preserves-≽ (sort {i = i} p) (rfl (⋆ j)) =
--   ⋆ i , (sort p , refl (⋆ i))
-- step-↠-preserves-≽ (sort _) (step ⋆j⇝T' _) =
--     ⊥-recursion _ (sorts-don't-reduce ⋆j⇝T' (refl (⋆ _)))
-- step-↠-preserves-≽ (pi π S″≼S T≼T″) q = {!!}
-- with pi-compute-forms q
-- step-↠-preserves-≽ (pi π S″≼S T≼T″) q
--   | S' Σ., T' , (S″↠S' , T″↠T' , Idₚ.refl ([ π x: S' ]→ T'))
--   with step-↠-preserves-≽ T≼T″ T″↠T' | step-↠-preserves-≼ S″≼S S″↠S'
-- step-↠-preserves-≽ (pi π S″≼S T≼T″) q
--   | S' Σ., T' , (S″↠S' , T″↠T' , Idₚ.refl ([ π x: S' ]→ T'))
--   | T₁ , (T₁≼T' , T↠T₁)
--   | S₁ , (S'≼S₁ , S↠S₁) =
--   [ π x: S₁ ]→ T₁ ,
--   (pi π S'≼S₁ T₁≼T' ,
--    ctx-closed ([ π x: — ]→ —) (S↠S₁ , T↠T₁))

postulate
  steps-↠-confluent-≼ : {S S' T T' : expr-of-type tag m}
    (p : S ≼ T)
    (q : S ↠ S')
    (q' : T ↠ T')
    → -------------------------
    ∃ λ S″ →
    ∃ λ T″ →
    S″ ≼ T″ ∧ S' ↠ S″ ∧ T' ↠ T″
-- steps-↠-confluent-≼ (similar p) q q' with steps-↠-confluent-~ p q q'
-- steps-↠-confluent-≼ (similar p) q q'
--   | S″ , (T″ , (S″~T″ , S'↠S″ , T'↠T″)) =
--   S″ , (T″ , (similar S″~T″ , S'↠S″ , T'↠T″))
-- steps-↠-confluent-≼ (sort p) (rfl (⋆ i)) (rfl (⋆ j)) =
--   ⋆ i , (⋆ j , (sort p , refl (⋆ i) , refl (⋆ j)))
-- steps-↠-confluent-≼ (sort _) (rfl _) (step ⋆j⇝T' _) =
--     ⊥-recursion _ (sorts-don't-reduce ⋆j⇝T' (refl (⋆ _)))
-- steps-↠-confluent-≼ (sort _) (step ⋆i⇝S' _) _ =
--     ⊥-recursion _ (sorts-don't-reduce ⋆i⇝S' (refl (⋆ _)))
-- steps-↠-confluent-≼ (pi S₁≼S T≼T₁) q q'
--   with pi-compute-forms q | pi-compute-forms q'
-- steps-↠-confluent-≼ (pi S₁≼S T≼T₁) q q'
--   | S₂ Σ., T₂ , (S↠S₂ , T↠T₂ , Idₚ.refl ([ π₂ x: S₂ ]→ T₂))
--   | S₃ Σ., T₃ , (S'↠S₃ , T'↠T₃ , Idₚ.refl ([ π₃ x: S₃ ]→ T₃)) =
--   {!!}

-- Lemma 21 (subtyping stability)

open import Liftable
open import Renaming
open import Proof

open import Axiom.FunctionExtensionality

-- ~-sub : ∀
--   {e e' : expr-of-type tag (m +1)}
--   (p₀ : e ~ e')
--   {R R'}
--   (p₁ : R ~ R')
--   (q : n < m +1)
--   → ---------------
--   e [ R / n [ q ]] ~ e' [ R' / n [ q ]]
-- ~-sub {term} (~id (⋆ i)) p₁ q = refl (⋆ i)
-- ~-sub {term} (~id ([ ρ x: S ]→ T)) p₁ q = {!!}
-- ~-sub {term} (~id (λx, t)) p₁ q = {!!}
-- ~-sub {term} (~id ⌊ e ⌋) p₁ q = {!!}
-- ~-sub {elim} (~id (var v')) p₁ q = {!!}
-- ~-sub {elim} (~id (f ` s)) p₁ q = {!!}
-- ~-sub {elim} (~id (s ꞉ S)) p₁ q = {!!}
-- ~-sub (~annot S S' p₀) p₁ q = {!!}

-- ≼-stable : (r R R' : Term m)
--   (q : n < m +1)
--   {S T : expr-of-type tag (m +1)}
--   (p : S ≼ T)
--   → ---------------
--   S [ r ꞉ R / n [ q ]] ≼ T [ r ꞉ R' / n [ q ]]
-- ≼-stable r R R' q (similar (~id e)) = similar ({!!})
-- ≼-stable r R R' q (similar (~annot S S' p)) = {!!}
-- ≼-stable r R R' q (sort p) = sort p
-- ≼-stable {n = n} r R R' q (pi {T = T}{T'} S'≼S T≼T') = {!!}
  -- pi (≼-stable r R R' q S'≼S)
  --    (Id.coe (ap (λ — → sub — T ≼ sub — T') $
  --                       Id.sym $
  --                       fun-ext $
  --                       lift-nth (r ꞉ R) q) $
  --      ≼-stable (shift r) (shift R) (shift R') (s<s q) T≼T')
