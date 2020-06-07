{-# OPTIONS --exact-split --prop #-}
open import Basic
open import PropUniverses

module Subtyping.Preservation
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Subtyping.Definition

-- Lemma 19 (similarity preservation)

open import Syntax
open import Substitution
open import Computation
open import ParallelReduction

open import Data.Nat hiding (_⊔_)
open import Relation.Binary
  hiding (_~_; Reflexive~; Transitive~; Symmetric~)
open import Logic

step-▷-preserves-~ : {S S' T : expr-of-type tag m}
  (p : S ~ T)
  (q : S ▷ S')
  → -------------------------
  ∃ λ T' → S' ~ T' ∧ T ▷ T'
{-
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
  | t‴ , (t'~t‴ , t″▷t‴) | s‴ , (s'~s‴ , s″▷s‴) = {!!}
  -- (t‴ ꞉ {!!}) [ s‴ ꞉ {!!} /new] ,
  -- ({!!} ,
  --  {!lam-comp π t″▷t‴ ? ? s″▷s‴!})
step-▷-preserves-~ ⌊ ~annot S S' s~s' ⌋ (elim-comp S s▷s″)
  with step-▷-preserves-~ s~s' s▷s″
step-▷-preserves-~ ⌊ ~annot S S' s~s' ⌋ (elim-comp S s▷s″)
  | s‴ , (s'~s‴ , s″▷s‴) = s‴ , (s'~s‴ , elim-comp S' s″▷s‴)
-}

open import Confluence

steps-▷-confluent-~ : {S S' T T' : expr-of-type tag m}
  (p : S ~ T)
  (q : S ▷ S')
  (q' : T ▷ T')
  → -------------------------
  ∃ λ S″ →
  ∃ λ T″ →
  S″ ~ T″ ∧ S' ▷ S″ ∧ T' ▷ T″
{-
steps-▷-confluent-~ (⋆ i)(⋆ i)(⋆ i) =
  ⋆ i , (⋆ i , (⋆ i , ⋆ i , ⋆ i))
steps-▷-confluent-~ (var x)(var x)(var x) =
  var x , (var x , (var x , var x , var x))
steps-▷-confluent-~
  ([ π x: p₀ ]→ p₁)([ π x: q₀ ]→ q₁)([ π x: q'₀ ]→ q'₁)
  with steps-▷-confluent-~ p₀ q₀ q'₀ | steps-▷-confluent-~ p₁ q₁ q'₁
steps-▷-confluent-~ _ _ ([ π x: _ ]→ _)
  | S″₀ , (T″₀ , (S″₀~T″₀ , S'₀▷S″₀ , T'₀▷T″₀))
  | S″₁ , (T″₁ , (S″₁~T″₁ , S'₁▷S″₁ , T'₁▷T″₁)) =
  [ π x: S″₀ ]→ S″₁ , (
  [ π x: T″₀ ]→ T″₁ ,
  ([ π x: S″₀~T″₀ ]→ S″₁~T″₁ ,
   [ π x: S'₀▷S″₀ ]→ S'₁▷S″₁ ,
   [ π x: T'₀▷T″₀ ]→ T'₁▷T″₁))
steps-▷-confluent-~ (λx, p)(λx, q)(λx, q')
  with steps-▷-confluent-~ p q q'
steps-▷-confluent-~ _ _ _ | S″ , (T″ , (S″~T″ , S'▷S″ , T'▷T″)) =
  λx, S″ , (λx, T″ , (λx, S″~T″ , λx, S'▷S″ , λx, T'▷T″))
steps-▷-confluent-~ (~annot S T p₀)(q₀ ꞉ q₁)(q'₀ ꞉ q'₁)
  with steps-▷-confluent-~ p₀ q₀ q'₀
steps-▷-confluent-~ (~annot S T p₀)(_꞉_ {S' = S₁} q₀ q₁)(_꞉_ {S' = T₁} q'₀ q'₁)
  | S″ , (T″ , (S″~T″ , S'▷S″ , T'▷T″)) =
  S″ ꞉ S₁ , (
  T″ ꞉ T₁ ,
  (~annot S₁ T₁ S″~T″ , S'▷S″ ꞉ refl S₁ , T'▷T″ ꞉ refl T₁))
steps-▷-confluent-~ ⌊ p ⌋ ⌊ q ⌋ ⌊ q' ⌋ with steps-▷-confluent-~ p q q'
... | S″ , (T″ , (S″~T″ , S'▷S″ , T'▷T″)) =
  ⌊ S″ ⌋ , (⌊ T″ ⌋ , (⌊ S″~T″ ⌋ , ⌊ S'▷S″ ⌋ , ⌊ T'▷T″ ⌋))
steps-▷-confluent-~ (p₀ ` p₁)(q₀ ` q₁)(q'₀ ` q'₁)
  with steps-▷-confluent-~ p₀ q₀ q'₀ | steps-▷-confluent-~ p₁ q₁ q'₁
steps-▷-confluent-~ (p₀ ` p₁)(q₀ ` q₁)(q'₀ ` q'₁)
  | S″₀ , (T″₀ , (S″~T″₀ , S'▷S″₀ , T'▷T″₀))
  | S″₁ , (T″₁ , (S″~T″₁ , S'▷S″₁ , T'▷T″₁)) =
  S″₀ ` S″₁ , (T″₀ ` T″₁ ,
  (S″~T″₀ ` S″~T″₁ , S'▷S″₀ ` S'▷S″₁ , T'▷T″₀ ` T'▷T″₁))
steps-▷-confluent-~ ⌊ ~annot S T p ⌋ ⌊ q₀ ꞉ q₁ ⌋ (elim-comp T q')
  with steps-▷-confluent-~ p q₀ q'
steps-▷-confluent-~ ⌊ ~annot S T p ⌋ ⌊ q₀ ꞉ q₁ ⌋ (elim-comp T q')
  | S″ , (T″ , (S″~T″ , S'▷S″ , T'▷T″)) =
  S″ , (T″ , (S″~T″ , elim-comp _ S'▷S″ , T'▷T″))
steps-▷-confluent-~ ⌊ ~annot S T p ⌋ (elim-comp S q) ⌊ q'₀ ꞉ q'₁ ⌋
  with steps-▷-confluent-~ p q q'₀
steps-▷-confluent-~ ⌊ ~annot S T p ⌋ (elim-comp S q) ⌊ q'₀ ꞉ q'₁ ⌋
  | S″ , (T″ , (S″~T″ , S'▷S″ , T'▷T″)) =
  S″ , (T″ , (S″~T″ , S'▷S″ , elim-comp _ T'▷T″))
steps-▷-confluent-~ ⌊ p ⌋ (elim-comp T q)(elim-comp T₁ q') = {!!}
steps-▷-confluent-~ (~annot S _ (λx, p₀) ` p₁)(q₀ ` q₁)(lam-comp π q'₀ q'₁ q'₂ q'₃) = {!!}
steps-▷-confluent-~ (p₀ ` p₁)
  (lam-comp π q₀ q₁ q₂ q₃)(lam-comp π₁ q'₀ q'₁ q'₂ q'₃) = {!!}
steps-▷-confluent-~ (p₀ ` p₁) (lam-comp π q₀ q₁ q₂ q₃)(q'₀ ` q'₁) = {!!}
-}

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
