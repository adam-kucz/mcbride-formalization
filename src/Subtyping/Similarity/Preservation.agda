{-# OPTIONS --exact-split --prop #-}
open import Basic
open import PropUniverses

module Subtyping.Similarity.Preservation
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Subtyping.Similarity

-- Lemma 19 (similarity preservation)

open import Syntax
open import Syntax.Context
open import Computation
open import Renaming
open import Substitution as Subs
  hiding (sub; _[_/new])
open import Confluence
open import Computation.Proof

open import Type.Sum renaming (_,_ to _Σ,_)
open import Proposition.Identity hiding (refl)
open import Data.Nat hiding (_⊔_)
open import Relation.Binary
  hiding (_~_; Reflexive~; Transitive~; Symmetric~)
open import Relation.Binary.ReflexiveTransitiveClosure
  renaming (refl-trans-close to rtc)
open import Function hiding (_$_; _~_)
open import Logic
open import Proof
open import Function.Proof

private
  sub = λ {tag}{m}{n} →
    Subs.sub ⦃ subst = SubstitutableExpr {tag = tag} ⦄ {m}{n}
  _[_/new] = λ {n}{tag : ExprTag} →
    Subs._[_/new] ⦃ subst = SubstitutableExpr {tag = tag} ⦄ {n = n}
infix 180 _[_/new]

instance
  ~⊆annot~ : (_~_ {n = n}) ⊆ (annot-~ {n = n})
  ContextClosed~ : ContextClosed _~_
  OneContextClosed~ : OneContextClosed _~_
  Relating-sub-~ : ∀{m n}{tag}
    {σ : Sub m n}
    → ---------------------------
    Relating (sub σ) (_~_ {n = m}{tag}) (_~_ {n = n}{tag})
  Relating-rename-~ : ∀{m n}{tag}
    {ρ : Ren m n}
    → ---------------------------
    Relating (rename ρ) (_~_ {n = m}{tag}) (_~_ {n = n}{tag})

{-
open import ParallelReduction

step-▷-preserves-~ : {S S' T : expr-of-type tag m}
  (p : S ▷ S')
  (q : S ~ T)
  → -------------------------
  ∃ λ T' → S' ~ T' ∧ T ▷ T'
step-▷-preserves-~ (elim-comp {t' = t″} T p) ⌊ ~annot {s' = t'} T T' q q' ⌋
  with t‴ , (t″~t‴ , t'▷t‴) ← step-▷-preserves-~ p q =
  t‴ , (t″~t‴ , elim-comp T' t'▷t‴)
step-▷-preserves-~ (lam-comp π {S' = S″}{T' = T″}{s' = s″} t▷t″ S▷S″ T▷T″ s▷s″)
  (~annot ([ π x: S ]→ T)([ ρ x: S' ]→ T') (λx, t~t‴) (S~S‴ , T~T‴) ` s~s‴)
  with t' , (t″~t' , t‴▷t') ← step-▷-preserves-~ t▷t″ t~t‴
     | s' , (s″~s' , s‴▷s') ← step-▷-preserves-~ s▷s″ s~s‴
     | S' , (S″~S' , S‴▷S') ← step-▷-preserves-~ S▷S″ S~S‴
     | T' , (T″~T' , T‴▷T') ← step-▷-preserves-~ T▷T″ T~T‴ =
  (t' ꞉ T') [ s' ꞉ S' /new] , (
  liftSub-to-~ (newSub (s″ ꞉ S″))(newSub (s' ꞉ S'))
    (~annot T″ T' t″~t' $ subrel T″~T') $
  ap newSub $ ~annot S″ S' s″~s' $ subrel S″~S' ,
  lam-comp ρ t‴▷t' S‴▷S' T‴▷T' s‴▷s')
step-▷-preserves-~ (⋆ i)(⋆ i) = ⋆ i , (refl (⋆ i) , refl (⋆ i))
step-▷-preserves-~ (var x)(var x) = var x , (refl (var x) , refl (var x))
step-▷-preserves-~ ([ π x: p₀ ]→ p₁) q = {!!}
step-▷-preserves-~ (λx, p)(λx, q)
  with t‴ , (t'~t‴ , t″▷t‴) ← step-▷-preserves-~ p q =
  λx, t‴ , (λx, t'~t‴ , λx, t″▷t‴)
step-▷-preserves-~ (p₀ ` p₁)(q₀ ` q₁) = {!!}
  -- with t‴ , (t'~t‴ , t″▷t‴) ← step-▷-preserves-~ p q =
step-▷-preserves-~ (p₀ ꞉ p₁)(~annot S S' q q') = ?
  -- with s‴ , (s'~s‴ , s″▷s‴) ← step-▷-preserves-~ p₀ q =
  -- s‴ ꞉ {!!} , ({!!} , s″▷s‴ ꞉ {!!})
step-▷-preserves-~ ⌊ p ⌋ ⌊ q ⌋
  with e‴ , (e'~e‴ , e″▷e‴) ← step-▷-preserves-~ p q =
  ⌊ e‴ ⌋ , (⌊ e'~e‴ ⌋ , ⌊ e″▷e‴ ⌋)
-}

{-
open import Computation.Property.VectorizedSubstitution

⇝-~-to-↠ : {S S' T : expr-of-type tag m}
  (p : S ⇝ S')
  (q : S ~ T)
  → -------------------------
  ∃ λ T' → S' ~ T' ∧ T ↠ T'
⇝-~-to-↠ (β π s S t T)(
  _`_ {s' = s'} (~annot ([ π x: S ]→ T)([ π' x: S' ]→ T')
                        (λx,_ {t' = t'} t~t') (S~S' , T~T')) s~s') =
  (t' ꞉ T') [ s' ꞉ S' /new] , (
  liftSub-to-~ (newSub (s ꞉ S))(newSub (s' ꞉ S'))
    (ctx-closed (— ꞉ —) (t~t' , T~T'))
    (ap newSub $ ctx-closed (— ꞉ —) (s~s' , S~S')) ,
  subrel $ β π' s' S' t' T')
⇝-~-to-↠ (v _ T) ⌊ ~annot {s' = s'} T S' q q₁ ⌋ =
  s' , (q , subrel $ v s' S')
⇝-~-to-↠ (hole — p) q = ⇝-~-to-↠ p q
⇝-~-to-↠ (hole [ π x: S ]→ C[—] ↓ p)([_x:_]→_ π {S' = S'} S~S' C[s]~T″)
  with T' , (C[t]~T' , T″↠T') ← ⇝-~-to-↠ (hole C[—] p) C[s]~T″ =
  [ π x: S' ]→ T' , (
  [ π x: S~S' ]→ C[t]~T' ,
  ctx-closed ([ π x: term S' ]→ —)(↑prop ⋆ₚ , T″↠T')) 
⇝-~-to-↠ (hole ([ π x: C[—] ↓]→ T) p)([_x:_]→_ π {T' = T'} C[s]~S″ T~T')
  with S' , (C[t]~S' , S″↠S') ← ⇝-~-to-↠ (hole C[—] p) C[s]~S″ =
  [ π x: S' ]→ T' , (
  [ π x: C[t]~S' ]→ T~T' ,
  ctx-closed ([ π x: — ]→ term T')(S″↠S' , ↑prop ⋆ₚ))
⇝-~-to-↠ (hole (λx, C[—]) p)(λx, C[s]~t')
  with t″ , (C[t]~t″ , t'↠t″) ← ⇝-~-to-↠ (hole C[—] p) C[s]~t' =
  λx, t″ , (λx, C[t]~t″ , ctx-closed (λx, —) t'↠t″)
⇝-~-to-↠ (hole ⌊ C[—] ⌋ p) ⌊ q ⌋
  with e″ , (C[t]~e″ , e'↠e″) ← ⇝-~-to-↠ (hole C[—] p) q =
  ⌊ e″ ⌋ , (⌊ C[t]~e″ ⌋ , ctx-closed ⌊ — ⌋ e'↠e″)
⇝-~-to-↠ (hole (f ` C[—] ↓) p)(q₀ ` q₁) = {!!}
⇝-~-to-↠ (hole (C[—] ↓` s) p)(q₀ ` q₁) = {!!}
⇝-~-to-↠ (hole (s ꞉ C[—] ↓) p)(~annot _ S' q₀ q₁) = {!!}
⇝-~-to-↠ (hole (C[—] ↓꞉ S) p)(~annot S S' q₀ q₁)
  with s″ , (C[t]~s″ , s'↠s″) ← ⇝-~-to-↠ (hole C[—] p) q₀ =
  s″ ꞉ S' , (
  ~annot S S' C[t]~s″ q₁ ,
  ctx-closed (— ꞉ term S') (s'↠s″ , ↑prop ⋆ₚ))
-}

{-
step-↠-preserves-~ {T = T} (rfl _) q = T , (q , refl T) 
step-↠-preserves-~ (step (v t T) t↠t') ⌊ ~annot T T' q₀ _ ⌋
  with step-↠-preserves-~ t↠t' q₀
... | (t‴ , (t'~t‴ , s↠t‴)) = t‴ , (t'~t‴ , step (v _ T') s↠t‴)
step-↠-preserves-~ (step (β π s S t T) p) (~annot _ (⋆ i) (λx, q₀) () ` q₂)
step-↠-preserves-~ (step (β π s S t T) p) (~annot _ (λx, S') (λx, q₀) () ` q₂)
step-↠-preserves-~ (step (β π s S t T) p) (~annot _ ⌊ e ⌋ (λx, q₀) () ` q₂)
step-↠-preserves-~ (step (β π s S t T) p)
  (_`_ {s = s}{s'}
    (~annot ([ π x: S ]→ T)([ ρ x: S' ]→ T')(λx,_ {t' = t'} t~t')(S~S' , T~T'))
    s~s')
  with (t″ Σ, T″ , (subt↠t″ , subT↠T″ , Id.refl _)) ← annot-compute-forms p
  with step-↠-preserves-~ subt↠t″ q' | step-↠-preserves-~ subT↠T″ Q'
  where q' : t [ s ꞉ S /new] ~ t' [ s' ꞉ S' /new]
        q' = liftSub-to-~ (newSub (s ꞉ S))(newSub (s' ꞉ S')) t~t' $
             ap newSub $ ~annot S S' s~s' $ subrel S~S'
        Q' : T [ s ꞉ S /new] ~ T' [ s' ꞉ S' /new]
        Q' = liftSub-to-~ (newSub (s ꞉ S))(newSub (s' ꞉ S')) T~T' $
             ap newSub $ ~annot S S' s~s' $ subrel S~S'
... | (k , (t″~k , subt'↠k)) | (K , (T″~K , subT'↠K)) =
  k ꞉ K , (
  ~annot T″ K t″~k $ subrel T″~K , (
  proof (λx, t' ꞉ [ ρ x: S' ]→ T') ` s'
    〉 _⇝_ 〉 (t' ꞉ T') [ s' ꞉ S' /new] :by: β ρ s' S' t' T'
    〉 _↠_ 〉 k ꞉ K
      :by: ctx-closed (— ꞉ —) (subt'↠k , subT'↠K)
  qed))
step-↠-preserves-~ (step (hole — s⇝t) p) q = step-↠-preserves-~ (step s⇝t p) q
step-↠-preserves-~ (step (hole [ π x: S ]→ C[—] ↓ s⇝t) p)
  ([ π x: q₀ ]→ q₁) = ?
step-↠-preserves-~ (step (hole ([ π x: C[—] ↓]→ T) s⇝t) p) q =
  {!!}
step-↠-preserves-~ (step (hole (λx, C[—]) s⇝t) p) q =
  {!!}
step-↠-preserves-~ (step (hole ⌊ C[—] ⌋ s⇝t) p) ⌊ q ⌋ = {!step-↠-preserves-~ ? q!}
step-↠-preserves-~ (step (hole (f ` C[—] ↓) s⇝t) p) q =
  {!!}
step-↠-preserves-~ (step (hole (C[—] ↓` s) s⇝t) p) q =
  {!!}
step-↠-preserves-~ (step (hole (s ꞉ C[—] ↓) s⇝t) p) q =
  {!!}
step-↠-preserves-~ (step (hole (C[—] ↓꞉ S) s⇝t) p) q =
  {!!}
-}

step-↠-preserves-~ : {S S' T : expr-of-type tag m}
  (p : S ~ T)
  (q : S ↠ S')
  → -------------------------
  ∃ λ T' → S' ~ T' ∧ T ↠ T'
-- step-↠-preserves-~ p q = {!!}

-- TODO: figure out if the `proof` in the paper really doesn't work
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

subrel ⦃ ~⊆annot~ ⦄ = go
  where go : ∀{x y}(p : x ~ y) → annot-~ x y

--         go (⋆ i) =
--           (λ { (step ⋆i⇝'e _) →
--                ⊥-recursion _ $ sorts-don't-reduce ⋆i⇝'e $ Id.refl _}) ,
--           (λ { (step ⋆i⇝'e _) →
--                ⊥-recursion _ $ sorts-don't-reduce ⋆i⇝'e $ Id.refl _})
--         go ([ π x: p₀ ]→ p₁) = go' p₀ p₁ , go' (sym p₀) (sym p₁)
--           where go' : ∀{S S' : Term n}{T T'}(p₀ : S ~ S')(p₁ : T ~ T')
--                   → --------------------------------------------------
--                   annot-~.one-side ([ π x: S ]→ T)([ π x: S' ]→ T')
--                 go' p₀ p₁ {π}{S″}{T″} t↠[πx:S]→T
--                   with S″ Σ, T″ , (S↠S″ , T↠T″ , Id.refl _) ←
--                        pi-compute-forms t↠[πx:S]→T =
--                   {!!} Σ, {!!} Σ, {!!} , (
--                   ctx-closed ([ π x: — ]→ —) ({!!} , {!!}) ,
--                   {!!} , {!!})
--            -- (λ t↠[πx:S]→T → {!pi-compute-forms t↠[πx:S]→T!}) , {!!}
--         go (λx, p) = {!!}
--         go ⌊ p ⌋ = {!!}

ctx-closed ⦃ ContextClosed~ ⦄ = go
  where go : ∀{t tag n}
          (C : Context t tag n)
          {es es' : all-types t}
          (p : all-related _~_ t es es')
          → -------------------------------------------------------------
          fill-holes es C ~ fill-holes es' C
--         go (term t) p = refl t
--         go (elim e) p = refl e
--         go — p = p
--         go ([ π x: C₀ ]→ C₁)(p , q) = [ π x: go C₀ p ]→ go C₁ q
--         go (λx, C) p = λx, go C p
--         go ⌊ C ⌋ p = ⌊ go C p ⌋
--         go (C₀ ` C₁)(p , q) = go C₀ p ` go C₁ q
--         go (C₀ ꞉ term t)(p , q) =
--           ~annot _ _ (go C₀ p)(refl ⦃ Reflexive-annot ⦄ t)
--         go (C₀ ꞉ —)(p , q) = ~annot _ _ (go C₀ p) {!!}
--         -- go (C₀ ꞉ —)(p , [ π x: q₀ ]→ q₁) = ~annot _ _ (go C₀ p)(q₀ , q₁)
--         -- go (C₀ ꞉ —)(p , λx, q) = ~annot _ _ (go C₀ p)(↑prop ⋆ₚ)
--         -- go (C₀ ꞉ —)(p , ⌊ q ⌋) = ~annot _ _ (go C₀ p)(↑prop ⋆ₚ)
--         go (C₀ ꞉ [ π x: C₁ ]→ C₂)(p , (q₀ , q₁)) =
--           ~annot _ _ (go C₀ p) {!!} -- (go C₁ q₀ , go C₂ q₁)
--         go (C₀ ꞉ λx, C₁)(p , q) =
--           ~annot _ _ (go C₀ p) {!!} -- (↑prop ⋆ₚ)
--         go (C₀ ꞉ ⌊ C₁ ⌋)(p , q) =
--           ~annot _ _ (go C₀ p) {!!} -- (↑prop ⋆ₚ)

OneContextClosed~ = OneCtxClosed-of-CtxClosed

rel-preserv ⦃ Relating-sub-~ {σ = σ} ⦄ = go σ
  where go : ∀{tag m}
          (σ : Sub m n)
          {a b : expr-of-type tag m}
          (p : a ~ b)
          → --------------------------------
          sub σ a ~ sub σ b
--         go σ (⋆ i) = refl (⋆ i)
--         go σ (var x) = refl (σ x)
--         go σ ([ π x: p₀ ]→ p₁) = {!!}
--         go σ (λx, p) = {!!}
--         go σ (p₀ ` p₁) = {!!}
--         go σ ⌊ p ⌋ = {!!}
--         go σ (~annot S S' p q) = {!!}
  --       go σ (~annot (⋆ i₀) (⋆ i₁) p q) =
  --         ~annot (subst σ _)(subst σ _)(go σ p) ?
  --       go σ (~annot (⋆ i) (λx, S') p q) =
  --         ~annot (subst σ _)(subst σ _)(go σ p)(↑prop ⋆ₚ)
  --       go σ (~annot (⋆ i) ⌊ e ⌋ p q) =
  --         ~annot (subst σ _)(subst σ ⌊ e ⌋)(go σ p)(↑prop ⋆ₚ)
  --       go σ (~annot ([ π₀ x: S₀ ]→ T₀)([ π₁ x: S₁ ]→ T₁) p (q₀ , q₁)) =
  --         ~annot (subst σ _)(subst σ _)(go σ p)(go σ q₀ , go (lift σ) q₁)
  --       go σ (~annot (λx, t) (⋆ i) p q) =
  --         ~annot (subst σ _)(subst σ _)(go σ p)(↑prop ⋆ₚ)
  --       go σ (~annot (λx, t₀) (λx, t₁) p q) =
  --         ~annot (subst σ _)(subst σ _)(go σ p)(↑prop ⋆ₚ)
  --       go σ (~annot (λx, t) ⌊ e ⌋ p q) =
  --         ~annot (subst σ (λx, t))(subst σ ⌊ e ⌋)(go σ p)(↑prop ⋆ₚ)
  --       go σ (~annot ⌊ e ⌋ (⋆ i) p q) =
  --         ~annot (subst σ ⌊ e ⌋)(subst σ (⋆ i))(go σ p)(↑prop ⋆ₚ)
  --       go σ (~annot ⌊ e ⌋ (λx, t) p q) =
  --         ~annot (subst σ ⌊ e ⌋)(subst σ (λx, t))(go σ p)(↑prop ⋆ₚ)
  --       go σ (~annot ⌊ e₀ ⌋ ⌊ e₁ ⌋ p q) =
  --         ~annot (subst σ ⌊ e₀ ⌋)(subst σ ⌊ e₁ ⌋)(go σ p)(↑prop ⋆ₚ)
  --       go σ (⋆ i) = refl (⋆ i)
  --       go σ (var x) = refl (σ x)
  --       go σ ([ π x: p₀ ]→ p₁) = [ π x: go σ p₀ ]→ go (lift σ) p₁
  --       go σ (λx, p) = λx, go (lift σ) p
  --       go σ (p₀ ` p₁) = go σ p₀ ` go σ p₁
  --       go σ ⌊ p ⌋ = ⌊ go σ p ⌋

module Composable~ {n}{tag} where
  open MakeTransComposable (_~_ {n = n}{tag}) public

rel-preserv ⦃ Relating-rename-~ {ρ = ρ} ⦄ {a}{b} a~b =
  proof rename ρ a
    === sub (var ∘ ρ) a     :by: ap (λ — → — a) $ rename-as-sub ρ
    〉 _~_ 〉 sub (var ∘ ρ) b
      :by: ap (sub (var ∘ ρ)) ⦃ Relating-sub-~ ⦄ a~b [: _~_ ]
    === rename ρ b
      :by: ap (λ — → — b) $ sym $
           rename-as-sub ⦃ subst = SubstitutableExpr ⦄ ρ
  qed

-- open import Syntax.Context

-- open import Relation.Binary.Pointwise

-- liftSub-to-~ : ∀ {m n} {tag}
--   (σ σ' : Sub m n)
--   {t t' : expr-of-type tag m}
--   (t~t' : t ~ t')
--   (e~e' : Pointwise _~_ σ σ')
--   → ------------------------------
--   sub σ t ~ sub σ' t'
-- liftSub-to-~ σ σ' t~t' e~e' = {!!}
-- liftSub-to-~ σ σ' (~annot (⋆ i₀)(⋆ i₁) t~t' q) e~e' =
--   ~annot (⋆ i₀)(⋆ i₁)(liftSub-to-~ σ σ' t~t' e~e') {!!}
-- liftSub-to-~ σ σ' (~annot (⋆ i)(λx, t) t~t' q) e~e' =
--   ~annot (⋆ i)(λx, subst (lift σ') t)(liftSub-to-~ σ σ' t~t' e~e') {!!}
-- liftSub-to-~ σ σ' (~annot (⋆ i) ⌊ e ⌋ t~t' q) e~e' =
--   ~annot (⋆ i) ⌊ subst σ' e ⌋ (liftSub-to-~ σ σ' t~t' e~e') {!!}
-- liftSub-to-~ σ σ'
--   (~annot ([ ρ₀ x: S₀ ]→ T₀)([ ρ₁ x: S₁ ]→ T₁) t~t' (q₀ , q₁)) e~e' =
--   ~annot
--     ([ ρ₀ x: subst σ S₀ ]→ subst (lift σ) T₀)
--     ([ ρ₁ x: subst σ' S₁ ]→ subst (lift σ') T₁)
--     (liftSub-to-~ σ σ' t~t' e~e')
--     {!!}
--     -- (liftSub-to-~ σ σ' q₀ e~e' ,
--     --  liftSub-to-~ (lift σ)(lift σ') q₁ $
--     --  ap lift ⦃ RelatingLiftPtwise
--     --            ⦃ Relating-rename-Rel = Relating-rename-~ ⦄ ⦄
--     --  e~e')
-- liftSub-to-~ σ σ' (~annot (λx, t)(⋆ i) t~t' q) e~e' =
--   ~annot (λx, subst (lift σ) t)(⋆ i)(liftSub-to-~ σ σ' t~t' e~e') {!!}
-- liftSub-to-~ σ σ' (~annot (λx, t₀)(λx, t₁) t~t' q) e~e' =
--   ~annot (λx, subst (lift σ) t₀)
--          (λx, subst (lift σ') t₁)(liftSub-to-~ σ σ' t~t' e~e') {!!}
-- liftSub-to-~ σ σ' (~annot (λx, t) ⌊ e ⌋ t~t' q) e~e' =
--   ~annot (λx, subst (lift σ) t)
--          ⌊ subst σ' e ⌋ (liftSub-to-~ σ σ' t~t' e~e') {!!}
-- liftSub-to-~ σ σ' (~annot ⌊ e ⌋ (⋆ i) t~t' q) e~e' =
--   ~annot ⌊ subst σ e ⌋ (⋆ i)(liftSub-to-~ σ σ' t~t' e~e') {!!}
-- liftSub-to-~ σ σ' (~annot ⌊ e ⌋ (λx, t) t~t' q) e~e' =
--   ~annot ⌊ subst σ e ⌋ (λx, subst (lift σ') t)
--          (liftSub-to-~ σ σ' t~t' e~e') {!!}
-- liftSub-to-~ σ σ' (~annot ⌊ e₀ ⌋ ⌊ e₁ ⌋ t~t' q) e~e' =
--   ~annot ⌊ subst σ e₀ ⌋ ⌊ subst σ' e₁ ⌋ (liftSub-to-~ σ σ' t~t' e~e') {!!}
-- liftSub-to-~ σ σ' (⋆ i) e~e' = refl (⋆ i)
-- liftSub-to-~ σ σ' (var x) e~e' = e~e' x
-- liftSub-to-~ σ σ' ([ π x: t~t' ]→ t~t″) e~e' =
--   [ π x: liftSub-to-~ σ σ' t~t' e~e' ]→
--     liftSub-to-~ (lift σ)(lift σ') t~t″ (
--     ap lift ⦃ RelatingLiftPtwise
--               ⦃ Relating-rename-Rel = Relating-rename-~ ⦄ ⦄ e~e')
-- liftSub-to-~ σ σ' (λx, t~t') e~e' =
--   λx, liftSub-to-~ (lift σ)(lift σ') t~t' (
--       ap lift ⦃ RelatingLiftPtwise
--                 ⦃ Relating-rename-Rel = Relating-rename-~ ⦄ ⦄
--       e~e')
-- liftSub-to-~ σ σ' (t~t' ` t~t″) e~e' =
--   liftSub-to-~ σ σ' t~t' e~e' ` liftSub-to-~ σ σ' t~t″ e~e'
-- liftSub-to-~ σ σ' ⌊ t~t' ⌋ e~e' = ⌊ liftSub-to-~ σ σ' t~t' e~e' ⌋

{-
C[s]~→C[s]~C[t] : ∀{m n tag tag'}
  (C[—] : OneHoleContext tag m tag' n)
  (s : expr-of-type tag m)
  {T : expr-of-type tag' n}
  (p : C[—] [ s /—] ~ T)
  → ----------------------------------------
  ∃ λ t → T == C[—] [ t /—] 
C[s]~→C[s]~C[t] — s {t} p = t , Id.refl _
C[s]~→C[s]~C[t] [ π x: S ]→ C[—] ↓ s ([ π x: p₀ ]→ p₁)
  with t , Id.refl _ ← C[s]~→C[s]~C[t] C[—] s p₁ =
  t , {!!} -- Id.refl _ -- 1-ctx-closed q ([ π x: S ]→ — ↓)
C[s]~→C[s]~C[t] ([ π x: C[—] ↓]→ T) s ([ π x: p₀ ]→ p₁)
  with t , Id.refl _ ← C[s]~→C[s]~C[t] C[—] s p₀ =
  t , {!!} -- Id.refl _ -- 1-ctx-closed q ([ π x: — ↓]→ T)
C[s]~→C[s]~C[t] (λx, C[—]) s (λx, p)
  with t , Id.refl _ ← C[s]~→C[s]~C[t] C[—] s p =
  t , {!!} -- Id.refl _ -- 1-ctx-closed q (λx, —)
C[s]~→C[s]~C[t] ⌊ C[—] ⌋ s ⌊ p ⌋
  with t , Id.refl _ ← C[s]~→C[s]~C[t] C[—] s p =
  t , {!!} -- Id.refl _ -- 1-ctx-closed q ⌊ — ⌋
C[s]~→C[s]~C[t] (f ` C[—] ↓) s (p₀ ` p₁)
  with t , Id.refl _ ← C[s]~→C[s]~C[t] C[—] s p₁ =
  t , {!!} -- Id.refl _ -- 1-ctx-closed q (f ` — ↓)
C[s]~→C[s]~C[t] (C[—] ↓` s') s (p₀ ` p₁)
  with t , Id.refl _ ← C[s]~→C[s]~C[t] C[—] s p₀ =
  t , {!!} -- Id.refl _ -- 1-ctx-closed q (— ↓` s')
C[s]~→C[s]~C[t] (s' ꞉ — ↓) s (~annot _ T p q) =
  T , {!!} -- Id.refl _ -- ~annot s T (refl s') q
C[s]~→C[s]~C[t] (s' ꞉ [ π x: S ]→ C[—] ↓ ↓) s (~annot _ S' p q) = {!!}
C[s]~→C[s]~C[t] (s' ꞉ [ π x: C[—] ↓]→ T ↓) s (~annot _ S' p q) = {!!}
C[s]~→C[s]~C[t] (s' ꞉ λx, C[—] ↓) s (~annot _ S' p q) = {!!}
C[s]~→C[s]~C[t] (s' ꞉ ⌊ C[—] ⌋ ↓) s (~annot _ S' p q) = {!!}
C[s]~→C[s]~C[t] (C[—] ↓꞉ S) s (~annot _ S' p q)
  with t , Id.refl _ ← C[s]~→C[s]~C[t] C[—] s p =
  t , {!!} -- Id.refl _ -- 1-ctx-closed q' (— ↓꞉ S)
-}
