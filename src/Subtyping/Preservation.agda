{-# OPTIONS --exact-split --prop #-}
open import Basic
open import PropUniverses

module Subtyping.Preservation
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Subtyping.Definition
open import Subtyping.Similarity

-- -- Lemma 19 (similarity preservation)

-- open import Syntax
-- open import Syntax.Context
-- open import Computation
-- open import Substitution as Subs
--   hiding (sub; _[_/new])
-- open import Confluence
-- open import Computation.Proof

-- open import Type.Sum renaming (_,_ to _Σ,_)
-- open import Proposition.Identity hiding (refl)
-- open import Data.Nat hiding (_⊔_)
-- -- open import Relation.Binary
-- --   hiding (_~_; Reflexive~; Transitive~; Symmetric~)
-- open import Relation.Binary.ReflexiveTransitiveClosure
--   renaming (refl-trans-close to rtc)
-- open import Logic
-- open import Proof

-- private
--   sub = λ {tag}{m}{n} →
--     Subs.sub ⦃ subst = SubstitutableExpr {tag = tag} ⦄ {m}{n}
--   _[_/new] = λ {n}{tag : ExprTag} →
--     Subs._[_/new] ⦃ subst = SubstitutableExpr {tag = tag} ⦄ {n = n}
-- infix 180 _[_/new]

-- {-
-- open import ParallelReduction

-- step-▷-preserves-~ : {S S' T : expr-of-type tag m}
--   (p : S ▷ S')
--   (q : S ~ T)
--   → -------------------------
--   ∃ λ T' → S' ~ T' ∧ T ▷ T'
-- step-▷-preserves-~ (elim-comp {t' = t″} T p) ⌊ ~annot {s' = t'} T T' q q' ⌋
--   with t‴ , (t″~t‴ , t'▷t‴) ← step-▷-preserves-~ p q =
--   t‴ , (t″~t‴ , elim-comp T' t'▷t‴)
-- step-▷-preserves-~ (lam-comp π {S' = S″}{T' = T″}{s' = s″} t▷t″ S▷S″ T▷T″ s▷s″)
--   (~annot ([ π x: S ]→ T)([ ρ x: S' ]→ T') (λx, t~t‴) (S~S‴ , T~T‴) ` s~s‴)
--   with t' , (t″~t' , t‴▷t') ← step-▷-preserves-~ t▷t″ t~t‴
--      | s' , (s″~s' , s‴▷s') ← step-▷-preserves-~ s▷s″ s~s‴
--      | S' , (S″~S' , S‴▷S') ← step-▷-preserves-~ S▷S″ S~S‴
--      | T' , (T″~T' , T‴▷T') ← step-▷-preserves-~ T▷T″ T~T‴ =
--   (t' ꞉ T') [ s' ꞉ S' /new] , (
--   liftSub-to-~ (newSub (s″ ꞉ S″))(newSub (s' ꞉ S'))
--     (~annot T″ T' t″~t' $ subrel T″~T') $
--   ap newSub $ ~annot S″ S' s″~s' $ subrel S″~S' ,
--   lam-comp ρ t‴▷t' S‴▷S' T‴▷T' s‴▷s')
-- step-▷-preserves-~ (⋆ i)(⋆ i) = ⋆ i , (refl (⋆ i) , refl (⋆ i))
-- step-▷-preserves-~ (var x)(var x) = var x , (refl (var x) , refl (var x))
-- step-▷-preserves-~ ([ π x: p₀ ]→ p₁) q = {!!}
-- step-▷-preserves-~ (λx, p)(λx, q)
--   with t‴ , (t'~t‴ , t″▷t‴) ← step-▷-preserves-~ p q =
--   λx, t‴ , (λx, t'~t‴ , λx, t″▷t‴)
-- step-▷-preserves-~ (p₀ ` p₁)(q₀ ` q₁) = {!!}
--   -- with t‴ , (t'~t‴ , t″▷t‴) ← step-▷-preserves-~ p q =
-- step-▷-preserves-~ (p₀ ꞉ p₁)(~annot S S' q q') = ?
--   -- with s‴ , (s'~s‴ , s″▷s‴) ← step-▷-preserves-~ p₀ q =
--   -- s‴ ꞉ {!!} , ({!!} , s″▷s‴ ꞉ {!!})
-- step-▷-preserves-~ ⌊ p ⌋ ⌊ q ⌋
--   with e‴ , (e'~e‴ , e″▷e‴) ← step-▷-preserves-~ p q =
--   ⌊ e‴ ⌋ , (⌊ e'~e‴ ⌋ , ⌊ e″▷e‴ ⌋)
-- -}

-- open import Computation.Property.VectorizedSubstitution

-- ⇝-~-to-↠ : {S S' T : expr-of-type tag m}
--   (p : S ⇝ S')
--   (q : S ~ T)
--   → -------------------------
--   ∃ λ T' → S' ~ T' ∧ T ↠ T'
-- ⇝-~-to-↠ (β π s S t T)(
--   _`_ {s' = s'} (~annot ([ π x: S ]→ T)([ π' x: S' ]→ T')
--                         (λx,_ {t' = t'} t~t') (S~S' , T~T')) s~s') =
--   (t' ꞉ T') [ s' ꞉ S' /new] , (
--   liftSub-to-~ (newSub (s ꞉ S))(newSub (s' ꞉ S'))
--     (ctx-closed (— ꞉ —) (t~t' , T~T'))
--     (ap newSub $ ctx-closed (— ꞉ —) (s~s' , S~S')) ,
--   subrel $ β π' s' S' t' T')
-- ⇝-~-to-↠ (v _ T) ⌊ ~annot {s' = s'} T S' q q₁ ⌋ =
--   s' , (q , subrel $ v s' S')
-- ⇝-~-to-↠ (hole — p) q = ⇝-~-to-↠ p q
-- ⇝-~-to-↠ (hole [ π x: S ]→ C[—] ↓ p)([_x:_]→_ π {S' = S'} S~S' C[s]~T″)
--   with T' , (C[t]~T' , T″↠T') ← ⇝-~-to-↠ (hole C[—] p) C[s]~T″ =
--   [ π x: S' ]→ T' , (
--   [ π x: S~S' ]→ C[t]~T' ,
--   ctx-closed ([ π x: term S' ]→ —)(↑prop ⋆ₚ , T″↠T')) 
-- ⇝-~-to-↠ (hole ([ π x: C[—] ↓]→ T) p)([_x:_]→_ π {T' = T'} C[s]~S″ T~T')
--   with S' , (C[t]~S' , S″↠S') ← ⇝-~-to-↠ (hole C[—] p) C[s]~S″ =
--   [ π x: S' ]→ T' , (
--   [ π x: C[t]~S' ]→ T~T' ,
--   ctx-closed ([ π x: — ]→ term T')(S″↠S' , ↑prop ⋆ₚ))
-- ⇝-~-to-↠ (hole (λx, C[—]) p)(λx, C[s]~t')
--   with t″ , (C[t]~t″ , t'↠t″) ← ⇝-~-to-↠ (hole C[—] p) C[s]~t' =
--   λx, t″ , (λx, C[t]~t″ , ctx-closed (λx, —) t'↠t″)
-- ⇝-~-to-↠ (hole ⌊ C[—] ⌋ p) ⌊ q ⌋
--   with e″ , (C[t]~e″ , e'↠e″) ← ⇝-~-to-↠ (hole C[—] p) q =
--   ⌊ e″ ⌋ , (⌊ C[t]~e″ ⌋ , ctx-closed ⌊ — ⌋ e'↠e″)
-- ⇝-~-to-↠ (hole (f ` C[—] ↓) p)(q₀ ` q₁) = {!!}
-- ⇝-~-to-↠ (hole (C[—] ↓` s) p)(q₀ ` q₁) = {!!}
-- ⇝-~-to-↠ (hole (s ꞉ C[—] ↓) p)(~annot _ S' q₀ q₁) = {!!}
-- ⇝-~-to-↠ (hole (C[—] ↓꞉ S) p)(~annot S S' q₀ q₁)
--   with s″ , (C[t]~s″ , s'↠s″) ← ⇝-~-to-↠ (hole C[—] p) q₀ =
--   s″ ꞉ S' , (
--   ~annot S S' C[t]~s″ q₁ ,
--   ctx-closed (— ꞉ term S') (s'↠s″ , ↑prop ⋆ₚ))

-- {-
-- step-↠-preserves-~ : {S S' T : expr-of-type tag m}
--   (p : S ↠ S')
--   (q : S ~ T)
--   → -------------------------
--   ∃ λ T' → S' ~ T' ∧ T ↠ T'
-- step-↠-preserves-~ {T = T} (rfl _) q = T , (q , refl T) 
-- step-↠-preserves-~ (step (v t T) t↠t') ⌊ ~annot T T' q₀ _ ⌋
--   with step-↠-preserves-~ t↠t' q₀
-- ... | (t‴ , (t'~t‴ , s↠t‴)) = t‴ , (t'~t‴ , step (v _ T') s↠t‴)
-- step-↠-preserves-~ (step (β π s S t T) p) (~annot _ (⋆ i) (λx, q₀) () ` q₂)
-- step-↠-preserves-~ (step (β π s S t T) p) (~annot _ (λx, S') (λx, q₀) () ` q₂)
-- step-↠-preserves-~ (step (β π s S t T) p) (~annot _ ⌊ e ⌋ (λx, q₀) () ` q₂)
-- step-↠-preserves-~ (step (β π s S t T) p)
--   (_`_ {s = s}{s'}
--     (~annot ([ π x: S ]→ T)([ ρ x: S' ]→ T')(λx,_ {t' = t'} t~t')(S~S' , T~T'))
--     s~s')
--   with (t″ Σ, T″ , (subt↠t″ , subT↠T″ , Id.refl _)) ← annot-compute-forms p
--   with step-↠-preserves-~ subt↠t″ q' | step-↠-preserves-~ subT↠T″ Q'
--   where q' : t [ s ꞉ S /new] ~ t' [ s' ꞉ S' /new]
--         q' = liftSub-to-~ (newSub (s ꞉ S))(newSub (s' ꞉ S')) t~t' $
--              ap newSub $ ~annot S S' s~s' $ subrel S~S'
--         Q' : T [ s ꞉ S /new] ~ T' [ s' ꞉ S' /new]
--         Q' = liftSub-to-~ (newSub (s ꞉ S))(newSub (s' ꞉ S')) T~T' $
--              ap newSub $ ~annot S S' s~s' $ subrel S~S'
-- ... | (k , (t″~k , subt'↠k)) | (K , (T″~K , subT'↠K)) =
--   k ꞉ K , (
--   ~annot T″ K t″~k $ subrel T″~K , (
--   proof (λx, t' ꞉ [ ρ x: S' ]→ T') ` s'
--     〉 _⇝_ 〉 (t' ꞉ T') [ s' ꞉ S' /new] :by: β ρ s' S' t' T'
--     〉 _↠_ 〉 k ꞉ K
--       :by: ctx-closed (— ꞉ —) (subt'↠k , subT'↠K)
--   qed))
-- step-↠-preserves-~ (step (hole — s⇝t) p) q = step-↠-preserves-~ (step s⇝t p) q
-- step-↠-preserves-~ (step (hole [ π x: S ]→ C[—] ↓ s⇝t) p)
--   ([ π x: q₀ ]→ q₁) = ?
-- step-↠-preserves-~ (step (hole ([ π x: C[—] ↓]→ T) s⇝t) p) q =
--   {!!}
-- step-↠-preserves-~ (step (hole (λx, C[—]) s⇝t) p) q =
--   {!!}
-- step-↠-preserves-~ (step (hole ⌊ C[—] ⌋ s⇝t) p) ⌊ q ⌋ = {!step-↠-preserves-~ ? q!}
-- step-↠-preserves-~ (step (hole (f ` C[—] ↓) s⇝t) p) q =
--   {!!}
-- step-↠-preserves-~ (step (hole (C[—] ↓` s) s⇝t) p) q =
--   {!!}
-- step-↠-preserves-~ (step (hole (s ꞉ C[—] ↓) s⇝t) p) q =
--   {!!}
-- step-↠-preserves-~ (step (hole (C[—] ↓꞉ S) s⇝t) p) q =
--   {!!}
-- -}

-- -- step-↠-preserves-~ : {S S' T : expr-of-type tag m}
-- --   (p : S ~ T)
-- --   (q : S ↠ S')
-- --   → -------------------------
-- --   ∃ λ T' → S' ~ T' ∧ T ↠ T'
-- -- step-↠-preserves-~ p q = {!!}

-- -- TODO: figure out if the `proof` in the paper really doesn't work
-- postulate
--   steps-↠-confluent-~ : {S S' T T' : expr-of-type tag m}
--     (p : S ~ T)
--     (q : S ↠ S')
--     (q' : T ↠ T')
--     → -------------------------
--     ∃ λ S″ →
--     ∃ λ T″ →
--     S″ ~ T″ ∧ S' ↠ S″ ∧ T' ↠ T″
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

open import Syntax
open import Syntax.Context
open import Computation

open import Type.Sum renaming (_,_ to _Σ,_)
open import Data.Nat hiding (_⊔_)
open import Logic
open import Proof

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

step-↠-preserves-≼ {S' = S'} (refl≼ S) q = S' , (refl S' , q)
step-↠-preserves-≼ (sort {j = j} p) (rfl (⋆ i)) =
  ⋆ j , (sort p , refl (⋆ j))
step-↠-preserves-≼ (sort {i = i} p) (step ⋆i↝e q) =
  ⊥-recursion _ $ sorts-don't-reduce ⋆i↝e $ refl (⋆ i)
step-↠-preserves-≼ ([ π x: p₀ ]→ p₁) q with pi-compute-forms q
... | S″ Σ, T″ , (S₁↠S″ , T↠T″ , Id.refl ([ π x: S″ ]→ T″))
  with step-↠-preserves-≽ p₀ S₁↠S″ | step-↠-preserves-≼ p₁ T↠T″
... | S‴ , (S‴≼S″ , S'↠S‴) | T‴ , (T″≼T‴ , T''↠T‴) =
  [ π x: S‴ ]→ T‴ , (
  [ π x: S‴≼S″ ]→ T″≼T‴ ,
  ctx-closed ([ π x: — ]→ —) (S'↠S‴ , T''↠T‴))

step-↠-preserves-≽ {T' = T'} (refl≼ S) q = T' , (refl T' , q)
step-↠-preserves-≽ (sort {i = i} p) (rfl (⋆ j)) =
  ⋆ i , (sort p , refl (⋆ i))
step-↠-preserves-≽ (sort {j = j} p) (step ⋆j↝e q) =
  ⊥-recursion _ $ sorts-don't-reduce ⋆j↝e $ refl (⋆ j)
step-↠-preserves-≽ ([_x:_]→_ π {S}{S'}{T}{T'} S'≼S T≼T') q with pi-compute-forms q
... | S″ Σ, T″ , (S'↠S″ , T'↠T″ , Id.refl ([ π x: S″ ]→ T″))
  with step-↠-preserves-≼ S'≼S S'↠S″ | step-↠-preserves-≽ T≼T' T'↠T″
... | S‴ , (S″≼S‴ , S↠S‴) | T‴ , (T‴≼T″ , T↠T‴) =
  [ π x: S‴ ]→ T‴ , (
  [ π x: S″≼S‴ ]→ T‴≼T″ ,
  ctx-closed ([ π x: — ]→ —) (S↠S‴ , T↠T‴))

open import Confluence

steps-↠-confluent-≼ : {S S' T T' : expr-of-type tag m}
  (p : S ≼ T)
  (q : S ↠ S')
  (q' : T ↠ T')
  → -------------------------
  ∃ λ S″ →
  ∃ λ T″ →
  S″ ≼ T″ ∧ S' ↠ S″ ∧ T' ↠ T″
steps-↠-confluent-≼ (refl≼ S) q q'
  with S″ , (S'↠S″ , T'↠S″) ← diamond-↠ q q' =
  S″ , (S″ , (refl S″ , S'↠S″ , T'↠S″))
steps-↠-confluent-≼ (sort p) (rfl (⋆ i)) (rfl (⋆ j)) =
  ⋆ i , (⋆ j , (sort p , refl (⋆ i) , refl (⋆ j)))
steps-↠-confluent-≼ (sort {j = j} p) (rfl (⋆ i)) (step ⋆j↝e q') =
  ⊥-recursion _ $ sorts-don't-reduce ⋆j↝e $ refl (⋆ j)
steps-↠-confluent-≼ (sort {i = i} p) (step ⋆i↝e q) q' =
  ⊥-recursion _ $ sorts-don't-reduce ⋆i↝e $ refl (⋆ i)
steps-↠-confluent-≼ ([_x:_]→_ π {S}{S'}{T}{T'} S'≼S T≼T') q q'
  with pi-compute-forms q | pi-compute-forms q'
... | S″ Σ, T″ , (S↠S″ , T↠T″ , Id.refl ([ π x: S″ ]→ T″))
    | S‴ Σ, T‴ , (S'↠S‴ , T'↠T‴ , Id.refl ([ π x: S‴ ]→ T‴))
  with steps-↠-confluent-≼ S'≼S S'↠S‴ S↠S″
     | steps-↠-confluent-≼ T≼T' T↠T″ T'↠T‴
... | S₅ , (S₄ , (S₅≼S₄ , S‴↠S₅ , S″↠S₄))
    | T₄ , (T₅ , (T₄≼T₅ , T″↠T₄ , T‴↠T₅)) =
  [ π x: S₄ ]→ T₄ , ([ π x: S₅ ]→ T₅ ,
  ([ π x: S₅≼S₄ ]→ T₄≼T₅ ,
   ctx-closed ([ π x: — ]→ —) (S″↠S₄ , T″↠T₄) ,
   ctx-closed ([ π x: — ]→ —) (S‴↠S₅ , T‴↠T₅)))

