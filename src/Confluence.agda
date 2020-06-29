{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import Basic using (Rig; wfs)
open import PropUniverses

module Confluence
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax
open import Substitution as Subs
  hiding (sub; _[_/new])
private
  sub = λ {m}{n}{tag : ExprTag} →
          Subs.sub ⦃ subst = SubstitutableExpr {tag = tag} ⦄ {m = m}{n}
  _[_/new] = λ {n}{tag : ExprTag} →
               Subs._[_/new] ⦃ subst = SubstitutableExpr {tag = tag} ⦄ {n = n}
infix 180 _[_/new]
          
open import Renaming
open import Liftable
open import Computation hiding (v)
open import ParallelReduction

-- Lemma 15 (parallel reduction diamond)

open import Syntax.Context

open import Type.Unit
open import Type.Sum hiding (_,_)
open import Relation.Binary.Diamond
open import Function hiding (_$_)
open import Logic
open import Proof
open import Function.Proof
open import Relation.Binary.Pointwise

diamond-▷ : ∀{n tag} → diamond (_▷_ {n = n}{tag})
diamond-▷ (⋆ i)(⋆ i) = ⋆ i , (⋆ i , ⋆ i)
diamond-▷ (var v)(var v) = var v , (var v , var v)
diamond-▷ ([ π x: S▷S' ]→ T▷T')([ π x: S▷S″ ]→ T▷T″)
  with diamond-▷ S▷S' S▷S″ | diamond-▷ T▷T' T▷T″
diamond-▷ ([ π x: S▷S' ]→ T▷T')([ π x: S▷S″ ]→ T▷T″)
  | S‴ , (S'▷S‴ , S″▷S‴) | T‴ , (T'▷T‴ , T″▷T‴) =
  [ π x: S‴ ]→ T‴ , ([ π x: S'▷S‴ ]→ T'▷T‴ , [ π x: S″▷S‴ ]→ T″▷T‴)
diamond-▷ (λx, t▷t')(λx, t▷t″) with diamond-▷ t▷t' t▷t″
diamond-▷ (λx, t▷t') (λx, t▷t″) | t‴ , (t'▷t‴ , t″▷t‴) =
  λx, t‴ , (λx, t'▷t‴ , λx, t″▷t‴)
diamond-▷ (s▷s' ꞉ S▷S') (s▷s″ ꞉ S▷S″)
  with diamond-▷ s▷s' s▷s″ | diamond-▷ S▷S' S▷S″
diamond-▷ (s▷s' ꞉ S▷S') (s▷s″ ꞉ S▷S″)
  | s‴ , (s'▷s‴ , s″▷s‴) | S‴ , (S'▷S‴ , S″▷S‴) =
  s‴ ꞉ S‴ , (s'▷s‴ ꞉ S'▷S‴ , s″▷s‴ ꞉ S″▷S‴)
diamond-▷ ⌊ e▷e' ⌋ ⌊ e▷e″ ⌋ with diamond-▷ e▷e' e▷e″
diamond-▷ ⌊ e▷e' ⌋ ⌊ e▷e″ ⌋ | e‴ , (e'▷e‴ , e″▷e‴) =
  ⌊ e‴ ⌋ , (⌊ e'▷e‴ ⌋ , ⌊ e″▷e‴ ⌋)
diamond-▷ ⌊ t▷t' ꞉ _ ⌋ (elim-comp _ t▷t″) with diamond-▷ t▷t' t▷t″
diamond-▷ ⌊ t▷t' ꞉ _ ⌋ (elim-comp _ t▷t″) | t‴ , (t'▷t‴ , t″▷t‴) =
  t‴ , (elim-comp _ t'▷t‴ , t″▷t‴)
diamond-▷ (elim-comp _ t▷t') ⌊ t▷t″ ꞉ _ ⌋ with diamond-▷ t▷t' t▷t″
diamond-▷ (elim-comp _ t▷t') ⌊ t▷t″ ꞉ _ ⌋ | t‴ , (t'▷t‴ , t″▷t‴) =
  t‴ , (t'▷t‴ , elim-comp _ t″▷t‴)
diamond-▷ (elim-comp T t▷t')(elim-comp T t▷t″) = diamond-▷ t▷t' t▷t″
diamond-▷ (f▷f' ` s▷s') (f▷f″ ` s▷s″)
  with diamond-▷ f▷f' f▷f″ | diamond-▷ s▷s' s▷s″
diamond-▷ (f▷f' ` s▷s') (f▷f″ ` s▷s″)
  | f‴ , (f'▷f‴ , f″▷f‴) | s‴ , (s'▷s‴ , s″▷s‴) =
  f‴ ` s‴ , (f'▷f‴ ` s'▷s‴ , f″▷f‴ ` s″▷s‴)
diamond-▷ ((λx, t▷t' ꞉ [ π x: S▷S' ]→ T▷T') ` s▷s')
           (lam-comp π t▷t″ S▷S″ T▷T″ s▷s″)
  with diamond-▷ t▷t' t▷t″ | diamond-▷ S▷S' S▷S″
     | diamond-▷ T▷T' T▷T″ | diamond-▷ s▷s' s▷s″
diamond-▷ _ (lam-comp π {S' = S″}{s' = s″} _ _ _ _)
  | t‴ , (t'▷t‴ , t″▷t‴) | S‴ , (S'▷S‴ , S″▷S‴)
  | T‴ , (T'▷T‴ , T″▷T‴) | s‴ , (s'▷s‴ , s″▷s‴) =
  (t‴ ꞉ T‴) [ s‴ ꞉ S‴ /new] ,
    (lam-comp π t'▷t‴ S'▷S‴ T'▷T‴ s'▷s‴ ,
     liftSub-to-▷ (newSub (s″ ꞉ S″)) (newSub (s‴ ꞉ S‴))
                  (t″▷t‴ ꞉ T″▷T‴)
                  (ap newSub $ s″▷s‴ ꞉ S″▷S‴))
diamond-▷ (lam-comp π t▷t' S▷S' T▷T' s▷s')
           ((λx, t▷t″ ꞉ [ π x: S▷S″ ]→ T▷T″) ` s▷s″)
  with diamond-▷ t▷t' t▷t″ | diamond-▷ S▷S' S▷S″
     | diamond-▷ T▷T' T▷T″ | diamond-▷ s▷s' s▷s″
diamond-▷ (lam-comp π {S' = S'}{s' = s'} _ _ _ _) _
  | t‴ , (t'▷t‴ , t″▷t‴) | S‴ , (S'▷S‴ , S″▷S‴)
  | T‴ , (T'▷T‴ , T″▷T‴) | s‴ , (s'▷s‴ , s″▷s‴) =
  (t‴ ꞉ T‴) [ s‴ ꞉ S‴ /new] ,
    (liftSub-to-▷ (newSub (s' ꞉ S')) (newSub (s‴ ꞉ S‴))
                  (t'▷t‴ ꞉ T'▷T‴)
                  (ap newSub $ s'▷s‴ ꞉ S'▷S‴) ,
     lam-comp π t″▷t‴ S″▷S‴ T″▷T‴ s″▷s‴)
diamond-▷ (lam-comp π t▷t' S▷S' T▷T' s▷s')
           (lam-comp π t▷t″ S▷S″ T▷T″ s▷s″)
  with diamond-▷ t▷t' t▷t″ | diamond-▷ S▷S' S▷S″
     | diamond-▷ T▷T' T▷T″ | diamond-▷ s▷s' s▷s″
diamond-▷ (lam-comp π {S' = S'}{s' = s'} _ _ _ _)
           (lam-comp π {S' = S″}{s' = s″} _ _ _ _)
  | t‴ , (t'▷t‴ , t″▷t‴) | S‴ , (S'▷S‴ , S″▷S‴)
  | T‴ , (T'▷T‴ , T″▷T‴) | s‴ , (s'▷s‴ , s″▷s‴) =
  (t‴ ꞉ T‴) [ s‴ ꞉ S‴ /new] ,
    (liftSub-to-▷ (newSub (s' ꞉ S')) (newSub (s‴ ꞉ S‴))
                  (t'▷t‴ ꞉ T'▷T‴)
                  (ap newSub $ s'▷s‴ ꞉ S'▷S‴) ,
     liftSub-to-▷ (newSub (s″ ꞉ S″)) (newSub (s‴ ꞉ S‴))
                  (t″▷t‴ ꞉ T″▷T‴)
                  (ap newSub $ s″▷s‴ ꞉ S″▷S‴))

-- Corollary 16 (confluence)

open import Relation.Binary.ReflexiveTransitiveClosure
  renaming (refl-trans-close to rtc)

diamond-↠ : ∀{n tag} → diamond (_↠_ {n = n}{tag})
diamond-↠ = parallelogram _⇝_ diamond-▷ 
  where instance _ = ⇝-⊆-▷; _ = ▷-⊆-↠
