{-# OPTIONS --exact-split --prop #-}
open import Basic using (Rig; wfs)
open import PropUniverses

module ParallelReduction.Property.VectorizedSubstitution
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax
open import Syntax.Context
open import Substitution as Subs
  hiding (sub; _[_/new])
          
open import Renaming
open import Liftable
open import ParallelReduction.Definition
open import ParallelReduction.Property

private
  sub = λ {m}{n}{tag : ExprTag} →
          Subs.sub ⦃ subst = SubstitutableExpr {tag = tag} ⦄ {m = m}{n}
  -- sub-ctx =
  --   λ {m}{n}{t : Holes}{tag} →
  --     Subs.sub
  --       ⦃ subst = SubstitutableContext {t = t}{tag} ⦄
  --       {m = m}{n}
  _[_/new] = λ {n}{tag : ExprTag} →
               Subs._[_/new] ⦃ subst = SubstitutableExpr {tag = tag} ⦄ {n = n}
infix 180 _[_/new]

-- Lemma 14 (vectorized substitution) (part 1)

open import Type.Sum hiding (_,_)
open import Data.Nat
open import Relation.Binary.Pointwise.Definition
open import Logic
open import Proof
open import Function.Proof

liftSub-to-▷ : ∀ {m n} {tag}
  (σ σ' : Sub m n)
  {t t' : expr-of-type tag m}
  (t▷t' : t ▷ t')
  (e▷e' : Pointwise _▷_ σ σ')
  → ------------------------------
  sub σ t ▷ sub σ' t'
liftSub-to-▷ σ σ' (elim-comp T t▷t') e▷e' =
  elim-comp (sub σ T) (liftSub-to-▷ σ σ' t▷t' e▷e')
liftSub-to-▷ σ σ'
  (lam-comp π {t}{t'}{S}{S'}{T}{T'}{s}{s'} t▷t' S▷S' T▷T' s▷s') e▷e' =
  proof (λx, sub (lift σ) t ꞉ [ π x: sub σ S ]→ sub (lift σ) T) ` sub σ s
    〉 _▷_ 〉 (sub (lift σ') t' ꞉ sub (lift σ') T') [ sub σ' s' ꞉ sub σ' S' /new]
      :by: lam-comp π
             (liftSub-to-▷ (lift σ) (lift σ') t▷t'
                           (ap lift ⦃ RelatingLiftPtwise ⦄ e▷e'))
             (liftSub-to-▷ σ σ' S▷S' e▷e')
             (liftSub-to-▷ (lift σ) (lift σ') T▷T'
                           (ap lift ⦃ RelatingLiftPtwise ⦄ e▷e'))
             (liftSub-to-▷ σ σ' s▷s' e▷e')
    === (sub (lift σ') (t' ꞉ T')) [ sub σ' (s' ꞉ S') /new]
      :by: Id.refl _
    === sub (newSub (sub σ' (s' ꞉ S')) ⍟ lift σ') (t' ꞉ T')
      :by: ap (λ — → — (t' ꞉ T')) $
           sub-∘ ⦃ subst = SubstitutableExpr ⦄
             (newSub (sub σ' (s' ꞉ S'))) (lift σ')
    === sub (σ' ⍟ newSub (s' ꞉ S')) (t' ꞉ T')
      :by: ap (λ — → sub — (t' ꞉ T')) $ sym {R = _==_} $
           sub-newSub σ' (s' ꞉ S')
    === sub σ' ((t' ꞉ T') [ s' ꞉ S' /new])
      :by: ap (λ — → — (t' ꞉ T')) $ sym $
            sub-∘ ⦃ subst = SubstitutableExpr ⦄ σ' (newSub (s' ꞉ S'))
  qed
liftSub-to-▷ σ σ' (⋆ i) e▷e' = ⋆ i
liftSub-to-▷ σ σ' (var x) e▷e' = e▷e' x
liftSub-to-▷ σ σ' ([ π x: S▷S' ]→ T▷T') e▷e' =
  [ π x: liftSub-to-▷ σ σ' S▷S' e▷e' ]→
    liftSub-to-▷ (lift σ)(lift σ') T▷T'
      (ap lift ⦃ RelatingLiftPtwise
                 ⦃ Relating-rename-Rel = Relating-rename-▷ ⦄ ⦄
       e▷e')
liftSub-to-▷ σ σ' (λx, t▷t') e▷e' =
  λx, liftSub-to-▷ (lift σ)(lift σ') t▷t'
        (ap lift ⦃ RelatingLiftPtwise
                   ⦃ Relating-rename-Rel = Relating-rename-▷ ⦄ ⦄
         e▷e')
liftSub-to-▷ σ σ' (f▷f' ` s▷s') e▷e' =
  liftSub-to-▷ σ σ' f▷f' e▷e' ` liftSub-to-▷ σ σ' s▷s' e▷e'
liftSub-to-▷ σ σ' (s▷s' ꞉ S▷S') e▷e' =
  liftSub-to-▷ σ σ' s▷s' e▷e' ꞉ liftSub-to-▷ σ σ' S▷S' e▷e'
liftSub-to-▷ σ σ' ⌊ e▷e' ⌋ σ▷σ' = ⌊ liftSub-to-▷ σ σ' e▷e' σ▷σ' ⌋

{-
liftSub-↠-▷-to-↠ : ∀{m n}{tag}
  (σ σ' : Sub m n)
  {t t' : expr-of-type tag m}
  (t▷t' : t ▷ t')
  (e↠e' : Pointwise _↠_ σ σ')
  → ------------------------------
  sub σ t ↠ sub σ' t'
liftSub-↠-▷-to-↠ σ σ' (elim-comp {t}{t'}{T} t▷t') e↠e' =
  proof sub σ ⌊ t ꞉ T ⌋
    〉 _⇝v_ 〉 sub σ t  :by: v (sub σ t) (sub σ T)
    〉 _↠_ 〉 sub σ' t' :by: liftSub-↠-▷-to-↠ σ σ' t▷t' e↠e'
  qed
liftSub-↠-▷-to-↠ σ σ'
  (lam-comp π {t}{t'}{S}{S'}{T}{T'}{s}{s'} t▷t' S▷S' T▷T' s▷s') e↠e' =
  proof (λx, sub (lift σ) t ꞉ [ π x: sub σ S ]→ sub (lift σ) T) ` sub σ s
    〉 _↠_ 〉 (λx, sub (lift σ') t' ꞉ [ π x: sub σ' S' ]→ sub (lift σ') T') `
            sub σ' s'
      :by: ctx-closed ((λx, — ꞉ [ π x: — ]→ —) ` —) (
             liftSub-↠-▷-to-↠ (lift σ) (lift σ') t▷t' $ ap lift e↠e' , (
             liftSub-↠-▷-to-↠ σ σ' S▷S' e↠e' ,
             liftSub-↠-▷-to-↠ (lift σ) (lift σ') T▷T' $ ap lift e↠e') ,
             liftSub-↠-▷-to-↠ σ σ' s▷s' e↠e')
    〉 _↠_ 〉 sub (lift σ') (t' ꞉ T') [ sub σ' (s' ꞉ S') /new]
      :by: subrel $ lam-comp π (refl (sub (lift σ') t'))
                               (refl (sub σ' S'))
                               (refl (sub (lift σ') T'))
                               (refl (sub σ' s'))
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
  qed
liftSub-↠-▷-to-↠ σ σ' (ctx (term t) es es' p) e↠e' =
  liftSub-refl-to-↠ σ σ' t e↠e'
liftSub-↠-▷-to-↠ σ σ' (ctx (elim e) es es' p) e↠e' =
  liftSub-refl-to-↠ σ σ' e e↠e'
liftSub-↠-▷-to-↠ σ σ' (ctx — es es' p) e↠e' = liftSub-↠-▷-to-↠ σ σ' p e↠e'
liftSub-↠-▷-to-↠ σ σ' (ctx ([ π x: C₀ ]→ C₁)(l Σ., r)(l' Σ., r')(p₀ , p₁)) e↠e' =
  ctx-closed ([ π x: — ]→ —) (
    liftSub-↠-▷-to-↠ σ σ' (ctx C₀ l l' p₀) e↠e' ,
    liftSub-↠-▷-to-↠ (lift σ) (lift σ') (ctx C₁ r r' p₁) $ ap lift e↠e')
liftSub-↠-▷-to-↠ σ σ' (ctx (λx, C) es es' p) e↠e' =
  1-ctx-closed (liftSub-↠-▷-to-↠ (lift σ) (lift σ') (ctx C es es' p) $
                ap lift e↠e') (λx, —)
liftSub-↠-▷-to-↠ σ σ' (ctx ⌊ C ⌋ es es' p) e↠e' =
  1-ctx-closed (liftSub-↠-▷-to-↠ σ σ' (ctx C es es' p) e↠e') ⌊ — ⌋
liftSub-↠-▷-to-↠ σ σ' (ctx (C₀ ` C₁)(l Σ., r)(l' Σ., r')(p₀ , p₁)) e↠e' =
  ctx-closed (— ` —) (liftSub-↠-▷-to-↠ σ σ' (ctx C₀ l l' p₀) e↠e' ,
                      liftSub-↠-▷-to-↠ σ σ' (ctx C₁ r r' p₁) e↠e')
liftSub-↠-▷-to-↠ σ σ' (ctx (C₀ ꞉ C₁)(l Σ., r)(l' Σ., r')(p₀ , p₁)) e↠e' =
  ctx-closed (— ꞉ —) (liftSub-↠-▷-to-↠ σ σ' (ctx C₀ l l' p₀) e↠e' ,
                      liftSub-↠-▷-to-↠ σ σ' (ctx C₁ r r' p₁) e↠e')
-}
