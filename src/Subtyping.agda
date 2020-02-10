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
data _~_ : RelOnExpr (𝒰 ⁺ ⊔ 𝒱) where
  ~sort : ∀ i
    → ---------------
    ⋆ {n = n} i ~ ⋆ i

  ~var : ∀ (v : Var m)
    → ------------
    var v ~ var v

  ~pi : ∀ π {S S' : Term m}{T T'}
    (S~S' : S ~ S')
    (T~T' : T ~ T')
    → -----------------------------
    [ π x: S ]→ T ~ [ π x: S' ]→ T'

  ~lam : ∀ {t t' : Term (m +1)}
    (t~t' : t ~ t')
    → --------------
    _~_ {tag = term} (λx, t) (λx, t')

  ~elim : ∀ {e e' : Elim m}
    (e~e' : e ~ e')
    → ---------------
    _~_ {tag = term} (⌊ e ⌋) (⌊ e' ⌋)

  ~app : ∀ {f f'}{s s' : Term m}
    (f~f' : f ~ f')
    (s~s' : s ~ s')
    → ---------------
    f ` s ~ f' ` s'

  ~annot : ∀ {s s'}(S S' : Term m)
    (p : s ~ s')
    → -------------
    s ꞉ S ~ s' ꞉ S'

open import Relation.Binary hiding (_~_)

instance
  Reflexive~ : Reflexive (_~_ {n = n}{tag})
  Transitive~ : Transitive (_~_ {n = n}{tag})
  Symmetric~ : Symmetric (_~_ {n = n}{tag})

refl ⦃ Reflexive~ {tag = term} ⦄ (⋆ i) = ~sort i
refl ⦃ Reflexive~ {tag = term} ⦄ ([ ρ x: S ]→ T) = ~pi ρ (refl S) (refl T)
refl ⦃ Reflexive~ {tag = term} ⦄ (λx, t) = ~lam (refl t)
refl ⦃ Reflexive~ {tag = term} ⦄ ⌊ e ⌋ = ~elim (refl e)
refl ⦃ Reflexive~ {tag = elim} ⦄ (var v₁) = ~var v₁
refl ⦃ Reflexive~ {tag = elim} ⦄ (f ` s) = ~app (refl f) (refl s)
refl ⦃ Reflexive~ {tag = elim} ⦄ (s ꞉ S) = ~annot S S (refl s)

trans ⦃ Transitive~ ⦄ (~sort i) q = q
trans ⦃ Transitive~ ⦄ (~var v') q = q
trans ⦃ Transitive~ ⦄ (~pi π p p₁) (~pi π q q₁) = ~pi π (trans p q) (trans p₁ q₁)
trans ⦃ Transitive~ ⦄ (~lam p) (~lam q) = ~lam (trans p q)
trans ⦃ Transitive~ ⦄ (~elim p) (~elim q) = ~elim (trans p q)
trans ⦃ Transitive~ ⦄ (~app p p₁) (~app q q₁) = ~app (trans p q) (trans p₁ q₁)
trans ⦃ Transitive~ ⦄ (~annot S S' p) (~annot S″ S‴ q) = ~annot S S‴ (trans p q)

sym ⦃ Symmetric~ ⦄ (~sort i) = ~sort i
sym ⦃ Symmetric~ ⦄ (~var v₁) = ~var v₁
sym ⦃ Symmetric~ ⦄ (~pi π p p₁) = ~pi π (sym p) (sym p₁)
sym ⦃ Symmetric~ ⦄ (~lam p) = ~lam (sym p)
sym ⦃ Symmetric~ ⦄ (~elim p) = ~elim (sym p)
sym ⦃ Symmetric~ ⦄ (~app p p₁) = ~app (sym p) (sym p₁)
sym ⦃ Symmetric~ ⦄ (~annot S S' p) = ~annot S' S (sym p)

data _≼_ : RelOnExpr (𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲) where
  similar : {S T : expr-of-type tag m}
    (p : S ~ T)
    → ----------
    S ≼ T

  sort : ∀ {i j}
    (p : j ≻ i)
    → ------------
    ⋆ {n = n} i ≼ ⋆ j

  pi : ∀ π {S S' : Term m}{T T'}
    (p : S' ≼ S)
    (q : T ≼ T')
    → ---------------------
    [ π x: S ]→ T ≼ [ π x: S' ]→ T'

-- Lemma 18 (subtyping transitivity)

instance
  Reflexive≼ : Reflexive (_≼_ {n = n}{tag})
  Transitive≼ : Transitive (_≼_ {n = n}{tag})

refl ⦃ Reflexive≼ ⦄ t = similar (refl t)

trans ⦃ Transitive≼ ⦄ (similar p) (similar p₁) =
  similar (trans p p₁)
trans ⦃ Transitive≼ ⦄ (similar (~sort i)) q@(sort _) = q
trans ⦃ Transitive≼ ⦄ (similar (~pi π p p₁)) (pi π q q₁) =
  pi π (trans q (similar (sym p))) (trans (similar p₁) q₁)
trans ⦃ Transitive≼ ⦄ p@(sort _) (similar (~sort i)) = p
trans ⦃ Transitive≼ ⦄ (sort p) (sort p₁) = sort (trans p₁ p)
trans ⦃ Transitive≼ ⦄ (pi π p p₁) (similar (~pi π q q₁)) =
  pi π (trans (similar (sym q)) p) (trans p₁ (similar q₁))
trans ⦃ Transitive≼ ⦄ (pi π p p₁) (pi π q q₁) =
  pi π (trans q p) (trans p₁ q₁)

-- Lemma 19 (similarity preservation)

open import ParallelReduction
open import Logic

step-▷-preserves-~ : {S S' T : expr-of-type tag m}
  (p : S ~ T)
  (q : S ▷ S')
  → -------------------------
  ∃ λ T' → S' ~ T' ∧ T ▷ T'
step-▷-preserves-~ (~sort i) (sort i) =
  ⋆ i , (refl (⋆ i) , refl (⋆ i))
step-▷-preserves-~ (~var v₁) (var v₁) =
  var v₁ , (refl (var v₁) , refl (var v₁))
step-▷-preserves-~ (~pi π p p₁) (pi π q q₁)
  with step-▷-preserves-~ p q | step-▷-preserves-~ p₁ q₁
step-▷-preserves-~ (~pi π p p₁) (pi π q q₁) | elem , (left , right) | y = {!!}
step-▷-preserves-~ (~lam p) (lam q) = {!!}
step-▷-preserves-~ (~elim p) (elim q) = {!!}
step-▷-preserves-~ (~elim p) (elim-comp q q₁) = {!!}
step-▷-preserves-~ (~app p p₁) (app q q₁) = {!!}
step-▷-preserves-~ (~app p p₁) (lam-comp π q q₁ q₂ q₃) = {!!}
step-▷-preserves-~ (~annot S S' p) (annot q q₁) = {!!}
-- step-▷-preserves-~ {S' = S'} (~id S) q = S' , (refl S' , q)
-- step-▷-preserves-~ (~annot S T (~id s)) (annot {t' = s'}{T' = S'} s▷s' S▷S') =
--   s' ꞉ T , (~annot S' T (~id s')  , annot s▷s' (refl T))

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

step-↠-preserves-≼ (similar p) q with step-↠-preserves-~ p q
step-↠-preserves-≼ (similar p) q | T' , (S'~T' , T↠T') =
  T' , (similar S'~T' , T↠T')
step-↠-preserves-≼ (sort {j = j} p) (rfl (⋆ i)) =
  ⋆ j , (sort p  , refl (⋆ j))
step-↠-preserves-≼ (sort _) (step ⋆i⇝S' _) =
  ⊥-recursion _ (sorts-don't-reduce ⋆i⇝S' (refl (⋆ _)))
step-↠-preserves-≼ (pi π S″≼S T≼T″) q with pi-compute-forms q
step-↠-preserves-≼ (pi π S″≼S T≼T″) q
  | S' Σ., T' , (S↠S' , T↠T' , Idₚ.refl ([ π x: S' ]→ T'))
  with step-↠-preserves-≼ T≼T″ T↠T' | step-↠-preserves-≽ S″≼S S↠S'
step-↠-preserves-≼ (pi π S″≼S T≼T″) q
  | S' Σ., T' , (S↠S' , T↠T' , Idₚ.refl _)
  | T₁ , (T'≼T₁ , T″↠T₁)
  | S₁ , (S₁≼S' , S″↠S₁) =
  [ π x: S₁ ]→ T₁ , (pi π S₁≼S' T'≼T₁ , mk-pi-compute π S″↠S₁ T″↠T₁)

step-↠-preserves-≽ (similar p) q with step-↠-preserves-~ (sym p) q
step-↠-preserves-≽ (similar p) q | T' , (S'~T' , T↠T') =
  T' , (similar (sym S'~T') , T↠T')
step-↠-preserves-≽ (sort {i = i} p) (rfl (⋆ j)) =
  ⋆ i , (sort p , refl (⋆ i))
step-↠-preserves-≽ (sort _) (step ⋆j⇝T' _) =
    ⊥-recursion _ (sorts-don't-reduce ⋆j⇝T' (refl (⋆ _)))
step-↠-preserves-≽ (pi π S″≼S T≼T″) q with pi-compute-forms q
step-↠-preserves-≽ (pi π S″≼S T≼T″) q
  | S' Σ., T' , (S″↠S' , T″↠T' , Idₚ.refl ([ π x: S' ]→ T'))
  with step-↠-preserves-≽ T≼T″ T″↠T' | step-↠-preserves-≼ S″≼S S″↠S'
step-↠-preserves-≽ (pi π S″≼S T≼T″) q
  | S' Σ., T' , (S″↠S' , T″↠T' , Idₚ.refl ([ π x: S' ]→ T'))
  | T₁ , (T₁≼T' , T↠T₁)
  | S₁ , (S'≼S₁ , S↠S₁) =
  [ π x: S₁ ]→ T₁ , (pi π S'≼S₁ T₁≼T' , mk-pi-compute π S↠S₁ T↠T₁)

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

open import Substitution
open import Liftable
open import Renaming
open import Proof

open import Axiom.FunctionExtensionality

~-sub : ∀
  {e e' : expr-of-type tag (m +1)}
  (p₀ : e ~ e')
  {R R'}
  (p₁ : R ~ R')
  (q : n < m +1)
  → ---------------
  e [ R / n [ q ]] ~ e' [ R' / n [ q ]]
-- ~-sub {term} (~id (⋆ i)) p₁ q = refl (⋆ i)
-- ~-sub {term} (~id ([ ρ x: S ]→ T)) p₁ q = {!!}
-- ~-sub {term} (~id (λx, t)) p₁ q = {!!}
-- ~-sub {term} (~id ⌊ e ⌋) p₁ q = {!!}
-- ~-sub {elim} (~id (var v')) p₁ q = {!!}
-- ~-sub {elim} (~id (f ` s)) p₁ q = {!!}
-- ~-sub {elim} (~id (s ꞉ S)) p₁ q = {!!}
-- ~-sub (~annot S S' p₀) p₁ q = {!!}

≼-stable : (r R R' : Term m)
  (q : n < m +1)
  {S T : expr-of-type tag (m +1)}
  (p : S ≼ T)
  → ---------------
  S [ r ꞉ R / n [ q ]] ≼ T [ r ꞉ R' / n [ q ]]
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
