{-# OPTIONS --exact-split --prop #-}
open import Basic using (Rig; wfs)
open import PropUniverses

module Confluence.VectorizedSubstitution
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

-- Lemma 14 (vectorized substitution)

open import Data.Nat
open import Proposition.Identity hiding (refl)
open import Proof
open import Proposition.Proof
open import ParallelReduction.Proof

private
  liftSubVec : ∀ {m n}
    (σ σ' : Sub m n)
    (𝒆▷𝒆' : (v : Var m) → σ v ▷ σ' v)
    → -------------------------------
    (v : Var (suc m)) → lift σ v ▷ lift σ' v

liftSubVec σ σ' 𝒆▷𝒆' Var.new = refl (var Var.new)
liftSubVec σ σ' 𝒆▷𝒆' (Var.old v) = ap (shift {F = Elim}) $ 𝒆▷𝒆' v

liftSub-to-▷ : ∀ {m n} {tag}
  (σ σ' : Sub m n)
  {t t' : expr-of-type tag m}
  (t▷t' : t ▷ t')
  (𝒆▷𝒆' : (v : Var m) → σ v ▷ σ' v)
  → ------------------------------
  sub σ t ▷ sub σ' t'
liftSub-to-▷ σ σ' (sort i) 𝒆▷𝒆' = refl (⋆ i)
liftSub-to-▷ σ σ' (pi π {S} {S'} {T} {T'} S▷S' T▷T') 𝒆▷𝒆' =
  pi π (liftSub-to-▷ σ σ' S▷S' 𝒆▷𝒆')
       (liftSub-to-▷ (lift σ) (lift σ')
       T▷T'
       (liftSubVec σ σ' 𝒆▷𝒆'))
liftSub-to-▷ σ σ' (lam t▷t') 𝒆▷𝒆' =
  lam (liftSub-to-▷ (lift σ) (lift σ') t▷t' (liftSubVec σ σ' 𝒆▷𝒆'))
liftSub-to-▷ σ σ' (elim t▷t') 𝒆▷𝒆' = elim (liftSub-to-▷ σ σ' t▷t' 𝒆▷𝒆')
liftSub-to-▷ σ σ' (elim-comp t▷t' t▷t'') 𝒆▷𝒆' =
  elim-comp (liftSub-to-▷ σ σ' t▷t' 𝒆▷𝒆')
            (liftSub-to-▷ σ σ' t▷t'' 𝒆▷𝒆')
liftSub-to-▷ σ σ' (var v) 𝒆▷𝒆' = 𝒆▷𝒆' v
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
             (liftSub-to-▷ (lift σ) (lift σ') t▷t' (liftSubVec σ σ' 𝒆▷𝒆'))
             (liftSub-to-▷ σ σ' t▷t'' 𝒆▷𝒆')
             (liftSub-to-▷ (lift σ) (lift σ') t▷t''' (liftSubVec σ σ' 𝒆▷𝒆'))
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

open import Computation.Proof

liftSub-to-↠ : ∀ {m n}{tag}
  (σ σ' : Sub m n)
  {t t' : expr-of-type tag m}
  (t↠t' : t ↠ t')
  (e↠e' : ∀ v → σ v ↠ σ' v)
  → ------------------------------
  sub σ t ↠ sub σ' t'
liftSub-to-↠ {tag = term} σ σ' (rfl (⋆ i)) e↠e' = refl (⋆ i)
liftSub-to-↠ {tag = term} σ σ' (rfl ([ π x: S ]→ T)) e↠e' =
  proof [ π x: sub σ S ]→ sub (lift σ) T
    〉 _↠_ 〉 [ π x: sub σ' S ]→ sub (lift σ) T
      :by: ctx-closed (liftSub-to-↠ σ σ' (refl S) e↠e')
                      ([ π x: — ↓]→ sub (lift σ) T)
    〉 _↠_ 〉 [ π x: sub σ' S ]→ sub (lift σ') T
      :by: ctx-closed (liftSub-to-↠ (lift σ) (lift σ') (refl T) λ
                        { new → refl (var new)
                        ; (old v) → ap shift $ e↠e' v})
                      ([ π x: sub σ' S ]→ — ↓)
  qed
liftSub-to-↠ {tag = term} σ σ' (rfl (λx, t)) e↠e' =
  ctx-closed (liftSub-to-↠ (lift σ) (lift σ') (refl t) λ
    { new → refl (var new)
    ; (old v) → ap shift $ e↠e' v}) (λx, —)
liftSub-to-↠ {tag = term} σ σ' (rfl ⌊ e ⌋) e↠e' =
  ctx-closed (liftSub-to-↠ σ σ' (rfl e) e↠e') ⌊ — ⌋ 
liftSub-to-↠ {tag = elim} σ σ' (rfl (var v)) e↠e' = e↠e' v
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
liftSub-to-↠ σ σ' (step (β-exact β') t↠t') e↠e' = ?
liftSub-to-↠ σ σ' (step (v-exact v') t↠t') e↠e' = ?
liftSub-to-↠ σ σ' (step (hole C[—] t⇝t″) t↠t') e↠e' = ? 
