{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import Basic using (Rig; wfs)
open import PropUniverses

module Confluence
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax ⦃ rig ⦄ ⦃ wfs ⦄
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
open _▷_

open import Confluence.VectorizedSubstitution

-- Lemma 15 (parallel reduction diamond)

open import Relation.Binary.Diamond
open import Logic

diamond-▷ : diamond (_▷_ {n = n}{tag})
diamond-▷ {q = q} (sort i) s▷q = q , (s▷q , refl q)
diamond-▷ (var v) (var v) = var v , (refl (var v) , refl (var v))
diamond-▷ (pi π S▷S' T▷T') (pi π S▷S″ T▷T″)
  with diamond-▷ S▷S' S▷S″ | diamond-▷ T▷T' T▷T″
diamond-▷ (pi π S▷S' T▷T') (pi π S▷S″ T▷T″)
  | S‴ , (S'▷S‴ , S″▷S‴) | T‴ , (T'▷T‴ , T″▷T‴) =
  [ π x: S‴ ]→ T‴ , (pi π S'▷S‴ T'▷T‴ , pi π S″▷S‴ T″▷T‴)
diamond-▷ (lam t▷t') (lam t▷t″) with diamond-▷ t▷t' t▷t″
diamond-▷ (lam t▷t') (lam t▷t″) | t‴ , (t'▷t‴ , t″▷t‴) =
  λx, t‴ , (lam t'▷t‴ , lam t″▷t‴)
diamond-▷ (annot t▷t' T▷T') (annot t▷t″ T▷T″)
  with diamond-▷ t▷t' t▷t″ | diamond-▷ T▷T' T▷T″
diamond-▷ (annot t▷t' T▷T') (annot t▷t″ T▷T″)
  | t‴ , (t'▷t‴ , t″▷t‴) | T‴ , (T'▷T‴ , T″▷T‴) =
  t‴ ꞉ T‴ , (annot t'▷t‴ T'▷T‴ , annot t″▷t‴ T″▷T‴)
diamond-▷ (elim e▷e') (elim e▷e″) with diamond-▷ e▷e' e▷e″
diamond-▷ (elim e▷e') (elim e▷e″) | e‴ , (e'▷e‴ , e″▷e‴) =
  ⌊ e‴ ⌋ , (elim e'▷e‴ , elim e″▷e‴)
diamond-▷ (app f▷f' s▷s') (app f▷f″ s▷s″)
  with diamond-▷ f▷f' f▷f″ | diamond-▷ s▷s' s▷s″
diamond-▷ (app f▷f' s▷s') (app f▷f″ s▷s″)
  | f‴ , (f'▷f‴ , f″▷f‴) | s‴ , (s'▷s‴ , s″▷s‴) =
  f‴ ` s‴ , (app f'▷f‴ s'▷s‴ , app f″▷f‴ s″▷s‴)
diamond-▷ (elim-comp t▷p T▷T') (elim-comp t▷q T▷T″) = diamond-▷ t▷p t▷q
diamond-▷ (elim (annot t▷t' T▷T')) (elim-comp t▷q T▷T″)
  with diamond-▷ t▷t' t▷q | diamond-▷ T▷T' T▷T″
diamond-▷ (elim (annot t▷t' T▷T')) (elim-comp t▷q T▷T″)
  | t‴ , (t'▷t‴ , q▷t‴) | T‴ , (T'▷T‴ , T″▷T‴) =
  t‴ , (elim-comp t'▷t‴ T'▷T‴ , q▷t‴)
diamond-▷ (elim-comp t▷q T▷T″) (elim (annot t▷t' T▷T'))
  with diamond-▷ t▷t' t▷q | diamond-▷ T▷T' T▷T″
diamond-▷ (elim-comp t▷q T▷T″) (elim (annot t▷t' T▷T')) 
  | t‴ , (t'▷t‴ , q▷t‴) | T‴ , (T'▷T‴ , T″▷T‴) =
  t‴ , (q▷t‴ , elim-comp t'▷t‴ T'▷T‴)
diamond-▷
  (app (annot (lam t▷t') (pi π S▷S' T▷T')) s▷s')
  (lam-comp π t▷t″ S▷S″ T▷T″ s▷s″)
  with diamond-▷ t▷t' t▷t″
     | diamond-▷ S▷S' S▷S″
     | diamond-▷ T▷T' T▷T″
     | diamond-▷ s▷s' s▷s″
diamond-▷
  (app (annot (lam t▷t') (pi π S▷S' T▷T')) s▷s')
  (lam-comp π {S' = S″}{s' = s″} t▷t″ S▷S″ T▷T″ s▷s″)
  | t‴ , (t'▷t‴ , t″▷t‴)
  | S‴ , (S'▷S‴ , S″▷S‴)
  | T‴ , (T'▷T‴ , T″▷T‴)
  | s‴ , (s'▷s‴ , s″▷s‴) =
  (t‴ ꞉ T‴) [ s‴ ꞉ S‴ /new] ,
  (lam-comp π t'▷t‴ S'▷S‴ T'▷T‴ s'▷s‴ ,
   liftSub-to-▷ (newSub (s″ ꞉ S″)) (newSub (s‴ ꞉ S‴))
     (annot t″▷t‴ T″▷T‴) λ { new → annot s″▷s‴ S″▷S‴ ; (old v) → refl (var v)})
diamond-▷
  (lam-comp π t▷t″ S▷S″ T▷T″ s▷s″)
  (app (annot (lam t▷t') (pi π S▷S' T▷T')) s▷s')
  with diamond-▷ t▷t' t▷t″
     | diamond-▷ S▷S' S▷S″
     | diamond-▷ T▷T' T▷T″
     | diamond-▷ s▷s' s▷s″
diamond-▷
  (lam-comp π {S' = S″}{s' = s″} t▷t″ S▷S″ T▷T″ s▷s″)
  (app (annot (lam t▷t') (pi π S▷S' T▷T')) s▷s')
  | t‴ , (t'▷t‴ , t″▷t‴)
  | S‴ , (S'▷S‴ , S″▷S‴)
  | T‴ , (T'▷T‴ , T″▷T‴)
  | s‴ , (s'▷s‴ , s″▷s‴) =
  (t‴ ꞉ T‴) [ s‴ ꞉ S‴ /new] ,
  (liftSub-to-▷ (newSub (s″ ꞉ S″)) (newSub (s‴ ꞉ S‴))
     (annot t″▷t‴ T″▷T‴) (λ { new → annot s″▷s‴ S″▷S‴ ; (old v) → refl (var v)}) ,
   lam-comp π t'▷t‴ S'▷S‴ T'▷T‴ s'▷s‴)
diamond-▷
  (lam-comp π t▷t' S▷S' T▷T' s▷s')
  (lam-comp π t▷t″ S▷S″ T▷T″ s▷s″)
  with diamond-▷ t▷t' t▷t″
     | diamond-▷ S▷S' S▷S″
     | diamond-▷ T▷T' T▷T″
     | diamond-▷ s▷s' s▷s″
diamond-▷
  (lam-comp π {S' = S'}{s' = s'} t▷t' S▷S' T▷T' s▷s')
  (lam-comp π {S' = S″}{s' = s″} t▷t″ S▷S″ T▷T″ s▷s″)
  | t‴ , (t'▷t‴ , t″▷t‴)
  | S‴ , (S'▷S‴ , S″▷S‴)
  | T‴ , (T'▷T‴ , T″▷T‴)
  | s‴ , (s'▷s‴ , s″▷s‴) =
  (t‴ ꞉ T‴) [ s‴ ꞉ S‴ /new] ,
  (annot
    (liftSub-to-▷ (newSub (s' ꞉ S')) (newSub (s‴ ꞉ S‴)) t'▷t‴
      λ { new → annot s'▷s‴ S'▷S‴ ; (old v) → refl (var v)})
    (liftSub-to-▷ (newSub (s' ꞉ S')) (newSub (s‴ ꞉ S‴)) T'▷T‴
      λ { new → annot s'▷s‴ S'▷S‴ ; (old v) → refl (var v)}) ,
   annot
    (liftSub-to-▷ (newSub (s″ ꞉ S″)) (newSub (s‴ ꞉ S‴)) t″▷t‴
      λ { new → annot s″▷s‴ S″▷S‴ ; (old v) → refl (var v)})
    (liftSub-to-▷ (newSub (s″ ꞉ S″)) (newSub (s‴ ꞉ S‴)) T″▷T‴
      λ { new → annot s″▷s‴ S″▷S‴ ; (old v) → refl (var v)}))

-- Corollary 16 (confluence)

open import Relation.Binary.ReflexiveTransitiveClosure
  renaming (refl-trans-close to rtc)

diamond-↠ : diamond (_↠_ {n = n}{tag})
diamond-↠ = parallelogram _⇝_ diamond-▷ 
  where instance _ = ⇝-⊆-▷; _ = ▷-⊆-↠
