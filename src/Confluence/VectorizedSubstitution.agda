{-# OPTIONS --exact-split --prop #-}
open import Basic using (Rig; wfs)
open import PropUniverses

module Confluence.VectorizedSubstitution
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax
open import Substitution as Subs
  hiding (sub; _[_/new])
          
open import Renaming
open import Liftable
open import Computation
open import ParallelReduction
open _▷_

private
  sub = λ {m}{n}{tag : ExprTag} →
          Subs.sub ⦃ subst = SubstitutableExpr {tag = tag} ⦄ {m = m}{n}
  sub-ctx =
    λ {m}{n}{k}{tag₀ : ExprTag}{tag₁} →
      Subs.sub
        ⦃ subst = SubstitutableContext {tag₀ = tag₀}{tag₁}{k} ⦄
        {m = m}{n}
  _[_/new] = λ {n}{tag : ExprTag} →
               Subs._[_/new] ⦃ subst = SubstitutableExpr {tag = tag} ⦄ {n = n}
infix 180 _[_/new]

-- Lemma 14 (vectorized substitution)

open import Data.Nat
open import Relation.Binary.Pointwise.Definition
open import Logic
open import Proof
open import Function.Proof
open import ParallelReduction.Proof

instance
  RelatingLiftPtwise▷ :
    Relating (lift {m = m}{n}) (Pointwise _▷_) (Pointwise _▷_)

rel-preserv ⦃ RelatingLiftPtwise▷ ⦄ _ new = refl (var new)
rel-preserv ⦃ RelatingLiftPtwise▷ ⦄ 𝒆▷𝒆' (old v') =
  ap (shift {F = Elim}) $ 𝒆▷𝒆' v'

{-
liftSub-to-▷ : ∀ {m n} {tag}
  (σ σ' : Sub m n)
  {t t' : expr-of-type tag m}
  (t▷t' : t ▷ t')
  (𝒆▷𝒆' : Pointwise _▷_ σ σ')
  → ------------------------------
  sub σ t ▷ sub σ' t'
liftSub-to-▷ σ σ' (sort i) 𝒆▷𝒆' = refl (⋆ i)
liftSub-to-▷ σ σ' (pi π {S} {S'} {T} {T'} S▷S' T▷T') 𝒆▷𝒆' =
  pi π (liftSub-to-▷ σ σ' S▷S' 𝒆▷𝒆')
       (liftSub-to-▷ (lift σ) (lift σ')
       T▷T'
       (ap lift 𝒆▷𝒆'))
liftSub-to-▷ σ σ' (lam t▷t') 𝒆▷𝒆' =
  lam (liftSub-to-▷ (lift σ) (lift σ') t▷t' (ap lift 𝒆▷𝒆'))
liftSub-to-▷ σ σ' (elim t▷t') 𝒆▷𝒆' = elim (liftSub-to-▷ σ σ' t▷t' 𝒆▷𝒆')
liftSub-to-▷ σ σ' (elim-comp t▷t' t▷t'') 𝒆▷𝒆' =
  elim-comp (liftSub-to-▷ σ σ' t▷t' 𝒆▷𝒆')
            (liftSub-to-▷ σ σ' t▷t'' 𝒆▷𝒆')
liftSub-to-▷ σ σ' (var v') 𝒆▷𝒆' = 𝒆▷𝒆' v'
liftSub-to-▷ σ σ' (app t▷t' t▷t'') 𝒆▷𝒆' =
  app (liftSub-to-▷ σ σ' t▷t' 𝒆▷𝒆')
      (liftSub-to-▷ σ σ' t▷t'' 𝒆▷𝒆')
liftSub-to-▷ σ σ' (annot t▷t' t▷t'') 𝒆▷𝒆' =
  annot (liftSub-to-▷ σ σ' t▷t' 𝒆▷𝒆')
        (liftSub-to-▷ σ σ' t▷t'' 𝒆▷𝒆')
liftSub-to-▷ σ σ'
    (lam-comp π {t}{t'}{S}{S'}{T}{T'}{s}{s'} t▷t' t▷t'' t▷t''' t▷t'''')
    𝒆▷𝒆' =
  proof (λx, sub (lift σ) t ꞉ [ π x: sub σ S ]→ sub (lift σ) T) ` sub σ s
    〉 _▷_ 〉 (sub (lift σ') t' ꞉ sub (lift σ') T') [ sub σ' s' ꞉ sub σ' S' /new]
      :by: lam-comp π
             (liftSub-to-▷ (lift σ) (lift σ') t▷t' (ap lift 𝒆▷𝒆'))
             (liftSub-to-▷ σ σ' t▷t'' 𝒆▷𝒆')
             (liftSub-to-▷ (lift σ) (lift σ') t▷t''' (ap lift 𝒆▷𝒆'))
             (liftSub-to-▷ σ σ' t▷t'''' 𝒆▷𝒆')
    === (sub (lift σ') (t' ꞉ T')) [ sub σ' (s' ꞉ S') /new]
      :by: Id-refl _
    === sub (newSub (sub σ' (s' ꞉ S')) ⍟ lift σ') (t' ꞉ T')
      :by: ap (λ — → — (t' ꞉ T')) $
           sub-∘ ⦃ subst = SubstitutableExpr ⦄
             (newSub (sub σ' (s' ꞉ S'))) (lift σ')
    === sub (σ' ⍟ newSub (s' ꞉ S')) (t' ꞉ T')
      :by: ap (λ — → sub — (t' ꞉ T')) $ sym {R = _==_} $
           sub-newSub σ' (s' ꞉ S')
    === sub σ' ((t' ꞉ T') [ s' ꞉ S' /new])
      :by: ap (λ — → — (t' ꞉ T')) $ sym $
            sub-∘ σ' (newSub (s' ꞉ S'))
    === sub σ' (t' [ s' ꞉ S' /new]) ꞉ sub σ' (T' [ s' ꞉ S' /new])
      :by: Id-refl _
  qed
-}

open import Computation.Proof

instance
  RelatingLiftPtwise↠ :
    Relating (lift {m = m}{n}) (Pointwise _↠_) (Pointwise _↠_)

rel-preserv ⦃ RelatingLiftPtwise↠ ⦄ _ new = refl (var new)
rel-preserv ⦃ RelatingLiftPtwise↠ ⦄ 𝒆↠𝒆' (old v') =
  ap (shift {F = Elim}) $ 𝒆↠𝒆' v'

liftSub-↠-▷-to-↠ : ∀ {m n}{tag}
  (σ σ' : Sub m n)
  {t t' : expr-of-type tag m}
  (t▷t' : t ▷ t')
  (e↠e' : Pointwise _↠_ σ σ')
  → ------------------------------
  sub σ t ↠ sub σ' t'
liftSub-↠-▷-to-↠ σ σ' (sort i) e↠e' = refl (⋆ i)
liftSub-↠-▷-to-↠ σ σ' (pi π t▷t' t▷t'') e↠e' = {!!}
liftSub-↠-▷-to-↠ σ σ' (lam t▷t') e↠e' = {!!}
liftSub-↠-▷-to-↠ σ σ' (elim t▷t') e↠e' = {!!}
liftSub-↠-▷-to-↠ σ σ' (elim-comp t▷t' t▷t'') e↠e' = {!!}
liftSub-↠-▷-to-↠ σ σ' (var v') e↠e' = e↠e' v'
liftSub-↠-▷-to-↠ σ σ' (app {f}{f'}{s}{s'} f▷f' s▷s') e↠e' = {!!}
{-  proof sub σ f ` sub σ s
    〉 _↠_ 〉 sub σ' f' ` sub σ s
      :by: ctx-closed (liftSub-↠-▷-to-↠ σ σ' f▷f' e↠e') (— ↓` sub σ s)
    〉 _↠_ 〉 sub σ' f' ` sub σ' s'
      :by: ctx-closed (liftSub-↠-▷-to-↠ σ σ' s▷s' e↠e') (sub σ' f' ` — ↓)
  qed -}
liftSub-↠-▷-to-↠ σ σ' (annot {t}{t'}{T}{T'} t▷t' T▷T') e↠e' = {!!}
{-  proof sub σ t ꞉ sub σ T
    〉 _↠_ 〉 sub σ' t' ꞉ sub σ T
      :by: ctx-closed (liftSub-↠-▷-to-↠ σ σ' t▷t' e↠e') (— ↓꞉ sub σ T)
    〉 _↠_ 〉 sub σ' t' ꞉ sub σ' T'
      :by: ctx-closed (liftSub-↠-▷-to-↠ σ σ' T▷T' e↠e') (sub σ' t' ꞉ — ↓)
  qed -}
liftSub-↠-▷-to-↠ σ σ'
  (lam-comp π {t}{t'}{S}{S'}{T}{T'}{s}{s'} t▷t' S▷S' T▷T' s▷s') e↠e' =
  proof (λx, sub (lift σ) t ꞉ [ π x: sub σ S ]→ sub (lift σ) T) ` sub σ s
    〉 _↠_ 〉 (λx, sub (lift σ) t ꞉ [ π x: sub σ S ]→ sub (lift σ) T) ` sub σ' s'
      :by: ctx-closed
             (liftSub-↠-▷-to-↠ σ σ' s▷s' e↠e')
             ((λx, sub (lift σ) t ꞉ [ π x: sub σ S ]→ sub (lift σ) T) ` — ↓)
    〉 _↠_ 〉 (λx, sub (lift σ) t ꞉ [ π x: sub σ' S' ]→ sub (lift σ) T) ` sub σ' s'
      :by: ctx-closed
             (liftSub-↠-▷-to-↠ σ σ' S▷S' e↠e')
             ((λx, sub (lift σ) t ꞉ [ π x: — ↓]→ sub (lift σ) T ↓) ↓` sub σ' s')
    〉 _↠_ 〉 (λx, sub (lift σ) t ꞉ [ π x: sub σ' S' ]→ sub (lift σ) T) ` sub σ' s'
      :by: ctx-closed
             (liftSub-↠-▷-to-↠ σ σ' S▷S' e↠e')
             ((λx, sub (lift σ) t ꞉ [ π x: — ↓]→ sub (lift σ) T ↓) ↓` sub σ' s')
    〉 _↠_ 〉 sub σ' (sub (newSub (s' ꞉ S')) (t' ꞉ T'))
      :by: {!!}
  qed

{-
liftSub-refl-to-↠ : ∀ {m n}{tag}
  (σ σ' : Sub m n)
  (t : expr-of-type tag m)
  (e↠e' : Pointwise _↠_ σ σ')
  → ------------------------------
  sub σ t ↠ sub σ' t
{-
liftSub-refl-to-↠ {tag = term} σ σ' (⋆ i) e↠e' = refl (⋆ i)
liftSub-refl-to-↠ {tag = term} σ σ' ([ π x: S ]→ T) e↠e' =
  proof [ π x: sub σ S ]→ sub (lift σ) T
    〉 _↠_ 〉 [ π x: sub σ' S ]→ sub (lift σ) T
      :by: ctx-closed (liftSub-refl-to-↠ σ σ' S e↠e')
                      ([ π x: — ↓]→ sub (lift σ) T)
    〉 _↠_ 〉 [ π x: sub σ' S ]→ sub (lift σ') T
      :by: ctx-closed (liftSub-refl-to-↠ (lift σ) (lift σ') T (ap lift e↠e'))
                      ([ π x: sub σ' S ]→ — ↓)
  qed
liftSub-refl-to-↠ {tag = term} σ σ' (λx, t) e↠e' =
  ctx-closed (liftSub-refl-to-↠ (lift σ) (lift σ') t (ap lift e↠e')) (λx, —)
liftSub-refl-to-↠ {tag = term} σ σ' ⌊ e ⌋ e↠e' =
  ctx-closed (liftSub-refl-to-↠ σ σ' e e↠e') ⌊ — ⌋ 
liftSub-refl-to-↠ {tag = elim} σ σ' (var v') e↠e' = e↠e' v'
liftSub-refl-to-↠ {tag = elim} σ σ' (t ` s) e↠e' =
  proof sub σ t ` sub σ s
    〉 _↠_ 〉 sub σ' t ` sub σ s
      :by: ctx-closed (liftSub-refl-to-↠ σ σ' t e↠e') (— ↓` sub σ s)
    〉 _↠_ 〉 sub σ' t ` sub σ' s
      :by: ctx-closed (liftSub-refl-to-↠ σ σ' s e↠e') (sub σ' t ` — ↓)
  qed
liftSub-refl-to-↠ {tag = elim} σ σ' (s ꞉ S) e↠e' =
  proof sub σ s ꞉ sub σ S
    〉 _↠_ 〉 sub σ' s ꞉ sub σ S
      :by: ctx-closed (liftSub-refl-to-↠ σ σ' s e↠e') (— ↓꞉ sub σ S)
    〉 _↠_ 〉 sub σ' s ꞉ sub σ' S
      :by: ctx-closed (liftSub-refl-to-↠ σ σ' S e↠e') (sub σ' s ꞉ — ↓)
  qed
-}

open import Relation.Binary
open import Data.Nat.Proof

liftSub-⇝-to-↠ : ∀ {m n}{tag}
  (σ σ' : Sub m n)
  {t t' : expr-of-type tag m}
  (t⇝t' : t ⇝ t')
  (e↠e' : Pointwise _↠_ σ σ')
  → ------------------------------
  sub σ t ↠ sub σ' t'
liftSub-⇝-to-↠ σ σ' (β-exact (β π s S t T)) e↠e' = {!!}
{-
  proof sub σ ((λx, t ꞉ [ π x: S ]→ T) ` s)
    〉 _↠_ 〉 sub σ' ((λx, t ꞉ [ π x: S ]→ T) ` s)
      :by: liftSub-refl-to-↠ σ σ' ((λx, t ꞉ [ π x: S ]→ T) ` s) e↠e'
    === (λx, sub (lift σ') t ꞉ [ π x: sub σ' S ]→ sub (lift σ') T) ` sub σ' s
      :by: Id-refl _
    〉 _⇝β_ 〉 (sub (lift σ') t ꞉ sub (lift σ') T) [ sub σ' s ꞉ sub σ' S /new]
      :by: β π (sub σ' s) (sub σ' S) (sub (lift σ') t) (sub (lift σ') T)
    === sub σ-new (sub (lift σ') (t ꞉ T))
      :by: Id-refl _
    === sub (σ-new ⍟ lift σ') (t ꞉ T)
      :by: ap (λ — → — (t ꞉ T)) $ sub-∘ σ-new (lift σ')
    === sub (σ' ⍟ newSub (s ꞉ S)) (t ꞉ T)
      :by: ap (λ — → sub — (t ꞉ T)) $ sym {R = _==_} $ sub-newSub σ' (s ꞉ S)
    === sub σ' ((t ꞉ T) [ s ꞉ S /new])
      :by: ap (λ — → — (t ꞉ T)) $ sym $ sub-∘ σ' (newSub (s ꞉ S))
  qed
  where σ-new = newSub (sub σ' (s ꞉ S))
-}
liftSub-⇝-to-↠ σ σ' (v-exact (v t T)) e↠e' = {!!}
liftSub-⇝-to-↠ σ σ' (hole {s = s}{t} C[—] s⇝t) e↠e'
  with ⟶ ≤-↔-∃+ (1-hole-ctx-inhabited C[—])
liftSub-⇝-to-↠ {m} σ σ' (hole {tag₀ = tag₀}{s = s} {t} C[—] s⇝t) e↠e'
  | k , Id-refl _ =
  proof sub σ (C[—] [ s /—])
    === Subs.sub σ C[—] [ sub (lift-by k σ) s /—]
      :by: sub-ctx-prop σ s C[—]
    〉 _⇝_ 〉 Subs.sub σ C[—] [ t' /—]
      :by: ctx-closed (ap (sub (lift-by k σ)) s⇝t) (Subs.sub σ C[—])
    === Subs.sub σ (coe (Id-refl _) C[—]) [ t' /—]
      :by: ap (λ — → Subs.sub σ — [ t' /—]) $ sym {R = _==_} $
           coe-eval' C[—]
    〉 _↠_ 〉 Subs.sub σ' (coe (Id-refl _) C[—]) [ t' /—]
      :by: liftSub-aux (sub (lift-by k σ) t) σ σ' e↠e' C[—] (Id-refl _)
    === {!Subs.sub σ' C[—] [ sub (lift-by k σ') t /—]!} -- Subs.sub σ' C[—] [ t' /—]
      :by: {!sym {R = _==_} $ sub-ctx-prop σ' t C[—]!} -- ap (λ — → Subs.sub σ' — [ t' /—]) $ coe-eval' C[—]
    === sub σ' (C[—] [ t /—])
      :by: sym {R = _==_} $ sub-ctx-prop σ' t C[—]
  qed
  where t' = sub (lift-by k σ) t
        open import Proposition.Identity.Coercion
        liftSub-aux : ∀{k m n l tag₀ tag₁}
          (t : expr-of-type tag₀ (k + n))
          (σ σ' : Sub m n)
          (e↠e' : Pointwise _↠_ σ σ')
          (C : 1-hole-ctx tag₀ l tag₁ m)
          (p : l == k + m)
          → ----------------------------------------
          let C' = coe (ap (λ — → 1-hole-ctx tag₀ — tag₁ m) p) C in
          Subs.sub σ C' [ t /—]
          ↠
          Subs.sub σ' C' [ t /—]
        liftSub-aux t σ σ' e↠e' [ π x: S ]→ C ↓ (Id-refl _) = {!!}
        liftSub-aux t σ σ' e↠e' ([ π x: C ↓]→ T) (Id-refl _) = {!!}
        liftSub-aux t σ σ' e↠e' (λx, C) (Id-refl _) = {!!}
        liftSub-aux t σ σ' e↠e' ⌊ C ⌋ (Id-refl _) = {!!}
        {-
          proof sub-ctx σ (coe (Id-refl _) ⌊ C ⌋) [ t /—]
            === ⌊ sub-ctx σ C  [ t /—] ⌋
              :by: ap (λ — → sub-ctx σ — [ t /—]) $ coe-eval' ⌊ C ⌋
            === ⌊ sub-ctx σ (coe (Id-refl _) C)  [ t /—] ⌋
              :by: ap (λ — → ⌊ sub-ctx σ — [ t /—] ⌋) $ sym {R = _==_} $
                   coe-eval' C
            〉 _↠_ 〉 ⌊ sub-ctx σ' (coe (Id-refl _) C) [ t /—] ⌋
              :by: ctx-closed (liftSub-aux t σ σ' e↠e' C (Id-refl _)) ⌊ — ⌋
            === ⌊ sub-ctx σ' C  [ t /—] ⌋
              :by: ap (λ — → ⌊ sub-ctx σ' — [ t /—] ⌋) $ coe-eval' C
            === sub-ctx σ' (coe (Id-refl _) ⌊ C ⌋) [ t /—]
              :by: ap (λ — → sub-ctx σ' — [ t /—]) $ sym {R = _==_} $
                   coe-eval' ⌊ C ⌋
          qed
        -}
        liftSub-aux t σ σ' e↠e' (f ` C ↓) (Id-refl _) = {!!}
        liftSub-aux t σ σ' e↠e' (C ↓` s) (Id-refl _) = {!!}
        liftSub-aux t σ σ' e↠e' (s ꞉ C ↓) (Id-refl _) = {!!}
        liftSub-aux t σ σ' e↠e' (C ↓꞉ S) (Id-refl _) = {!!}
        liftSub-aux t σ σ' e↠e' — p = {!!}
        {-
        liftSub-aux {zero} t σ σ' e↠e' — (Id-refl m) =
          proof Subs.sub σ (coe (Id-refl _) —) [ t /—]
            === Subs.sub σ — [ t /—]
              :by: ap (λ — → Subs.sub σ — [ t /—]) $ coe-eval' —
            〉 _↠_ 〉 coe (Id-refl _) — [ t /—]
              :by: rfl _
            === Subs.sub σ' (coe (Id-refl _) —) [ t /—]
              :by: ap (λ — → Subs.sub σ' — [ t /—]) $ sym {R = _==_} $
                   coe-eval' —
          qed
        liftSub-aux {k +1}{m} t σ σ' e↠e' — p =
          ⊥-recursion _ $ irrefl m (
          proof m
            〉 _≤_ 〉 k + m    :by: postfix (k +_) m
            〉 _<_ 〉 k + m +1 :by: postfix suc (k + m)
            === m           :by: sym p
          qed)
        -}

-- TODO: include pointwise-(rtc of reflexive R) commutativity
-- in the standard library
liftSub-to-↠ : ∀ {m n}{tag}
  (σ σ' : Sub m n)
  {t t' : expr-of-type tag m}
  (t↠t' : t ↠ t')
  (e↠e' : Pointwise _↠_ σ σ')
  → ------------------------------
  sub σ t ↠ sub σ' t'
{-
liftSub-to-↠ σ σ' (step {c = t'} (β-exact (β π s S t T)) t↠t') e↠e' =
  proof sub σ ((λx, t ꞉ [ π x: S ]→ T) ` s)
    === (λx, sub (lift σ) t ꞉ [ π x: sub σ S ]→ sub (lift σ) T) ` sub σ s
      :by: Id-refl _
    〉 _↠_ 〉 (λx, sub (lift σ) t ꞉ [ π x: sub σ S ]→ sub (lift σ) T) ` sub σ' s
      :by: ap ((λx, sub (lift σ) t ꞉ [ π x: sub σ S ]→ sub (lift σ) T) `_)
              (liftSub-to-↠ σ σ' (rfl s) e↠e')
    〉 _↠_ 〉 (λx, sub (lift σ') t ꞉ [ π x: sub σ' S ]→ sub (lift σ') T) ` sub σ' s
      :by: ap (_` sub σ' s) (
           proof λx, sub (lift σ) t ꞉ [ π x: sub σ S ]→ sub (lift σ) T
             〉 _↠_ 〉 λx, sub (lift σ') t ꞉ [ π x: sub σ S ]→ sub (lift σ) T
               :by: ap (λ — → λx, — ꞉ [ π x: sub σ S ]→ sub (lift σ) T) $
                       liftSub-to-↠ (lift σ) (lift σ') (rfl t) (ap lift e↠e')
             〉 _↠_ 〉 λx, sub (lift σ') t ꞉ [ π x: sub σ' S ]→ sub (lift σ') T
               :by: ap (λx, sub (lift σ') t ꞉_) (
                    proof [ π x: sub σ S ]→ sub (lift σ) T
                      〉 _↠_ 〉 [ π x: sub σ' S ]→ sub (lift σ) T
                        :by: ap ([ π x:_]→ sub (lift σ) T)
                                (liftSub-to-↠ σ σ' (rfl S) e↠e')
                      〉 _↠_ 〉 [ π x: sub σ' S ]→ sub (lift σ') T
                        :by: ap ([ π x: sub σ' S ]→_) $
                                liftSub-to-↠ (lift σ) (lift σ') (rfl T) $
                                ap lift e↠e'
                    qed)
           qed)              
    〉 _↠_ 〉 sub σ' t'
      :by: {!!}
  qed
liftSub-to-↠ σ σ' (step (v-exact (v t T)) t↠t') e↠e' = {!!}
liftSub-to-↠ σ σ' (step (hole C[—] r) t↠t') e↠e' = {!!}
liftSub-to-↠ {tag = term} σ σ' (rfl (⋆ i)) e↠e' = refl (⋆ i)
liftSub-to-↠ {tag = term} σ σ' (rfl ([ π x: S ]→ T)) e↠e' =
  proof [ π x: sub σ S ]→ sub (lift σ) T
    〉 _↠_ 〉 [ π x: sub σ' S ]→ sub (lift σ) T
      :by: ctx-closed (liftSub-to-↠ σ σ' (refl S) e↠e')
                      ([ π x: — ↓]→ sub (lift σ) T)
    〉 _↠_ 〉 [ π x: sub σ' S ]→ sub (lift σ') T
      :by: ctx-closed (liftSub-to-↠ (lift σ) (lift σ') (refl T) (ap lift e↠e'))
                      ([ π x: sub σ' S ]→ — ↓)
  qed
liftSub-to-↠ {tag = term} σ σ' (rfl (λx, t)) e↠e' =
  ctx-closed (liftSub-to-↠ (lift σ) (lift σ') (refl t) (ap lift e↠e')) (λx, —)
liftSub-to-↠ {tag = term} σ σ' (rfl ⌊ e ⌋) e↠e' =
  ctx-closed (liftSub-to-↠ σ σ' (rfl e) e↠e') ⌊ — ⌋ 
liftSub-to-↠ {tag = elim} σ σ' (rfl (var v')) e↠e' = e↠e' v'
liftSub-to-↠ {tag = elim} σ σ' (rfl (t ` s)) e↠e' =
  proof sub σ t ` sub σ s
    〉 _↠_ 〉 sub σ' t ` sub σ s
      :by: ctx-closed (liftSub-to-↠ σ σ' (refl t) e↠e') (— ↓` sub σ s)
    〉 _↠_ 〉 sub σ' t ` sub σ' s
      :by: ctx-closed (liftSub-to-↠ σ σ' (refl s) e↠e') (sub σ' t ` — ↓)
  qed
liftSub-to-↠ {tag = elim} σ σ' (rfl (s ꞉ S)) e↠e' =
  proof sub σ s ꞉ sub σ S
    〉 _↠_ 〉 sub σ' s ꞉ sub σ S
      :by: ctx-closed (liftSub-to-↠ σ σ' (refl s) e↠e') (— ↓꞉ sub σ S)
    〉 _↠_ 〉 sub σ' s ꞉ sub σ' S
      :by: ctx-closed (liftSub-to-↠ σ σ' (refl S) e↠e') (sub σ' s ꞉ — ↓)
  qed
-}
-}
