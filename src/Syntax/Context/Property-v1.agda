{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Syntax.Context.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax.Context.Arbitrary
open import Syntax.Context.Substitutable

open import Type.Sum
open import Data.Nat
open import Data.Vec as V hiding ([_])
open import Function hiding (_$_)

open import Syntax
open import Liftable
open import Substitution as Subs
  hiding (_[_/new])

private
  subst = λ {tag}{m}{n} →
    sub ⦃ subst = SubstitutableExpr {tag = tag} ⦄ {m = m}{n}
  _[_/new] = Subs._[_/new] ⦃ subst = SubstitutableElim ⦄
  subc = λ {tag}{k}{v}{m}{n} →
    sub ⦃ subst = SubstitutableContext {tag = tag}{k}{v} ⦄ {m = m}{n}
infix 180 _[_/new]

sub-all : ∀{m n}
  (σ : Sub m n)
  {k}(v : Holes k)
  (es : all-types (map [ id × _+ m ] v))
  → -------------------------------------
  all-types (map [ id × _+ n ] v)
sub-all σ [] es = es
sub-all {m = m} σ ((tag Σ., l) ∷ v) (e Σ., es) =
  subst (lift-by l σ) e Σ., sub-all σ v es

open import Proof

open import Proposition.Identity.Coercion

sub-ctx-aux : ∀ {m n}
  (σ : Sub m n)
  {k}{v' : Holes k}{tag}
  (C : Context v' tag m)
  {v : Holes k}
  (es : all-types (map [ id × _+ m ] v))
  (p : v' == map [ id × _+ m ] v)
  → ------------------------------------------------------------------
  let C' = coe (ap (λ — → Context — tag m) p) C in
  sub σ (fill-holes es C') == fill-holes (sub-all σ v es) (subc σ C')
sub-ctx-aux {m} σ (term t) {[]} es p = {!!}
{-  proof sub σ (fill-holes es (coe coer (term t)))
    === sub σ (fill-holes es (term t))
      :by: ap (λ — → sub σ (fill-holes es —)) $ coe-eval' (term t)
    === sub σ t
      :by: Id-refl _
    === fill-holes es (coe (Id-refl _) (term (sub σ t)))
      :by: ap (fill-holes es) $ sym $ coe-eval' (term (sub σ t)) 
    === fill-holes es (subc σ (term t))
      :by: Id-refl _
    === fill-holes es (subc σ (coe coer (term t)))
      :by: ap (λ — → fill-holes es (subc σ —)) $ sym $ coe-eval' (term t)
  qed
  where coer = ap (λ — → Context — term m) p -}
sub-ctx-aux {m} σ (elim e) {[]} es p = {!!}
{-
  proof sub σ (fill-holes es (coe coer (elim e)))
    === sub σ (fill-holes es (elim e))
      :by: ap (λ — → sub σ (fill-holes es —)) $ coe-eval' (elim e)
    === sub σ e
      :by: Id-refl _
    === fill-holes es (coe (Id-refl _) (elim (sub σ e)))
      :by: ap (fill-holes es) $ sym $ coe-eval' (elim (sub σ e)) 
    === fill-holes es (subc σ (elim e))
      :by: Id-refl _
    === fill-holes es (subc σ (coe coer (elim e)))
      :by: ap (λ — → fill-holes es (subc σ —)) $ sym $ coe-eval' (elim e)
  qed
  where coer = ap (λ — → Context — elim m) p
-}
sub-ctx-aux {m}{n} σ — {v@(V.[ tag Σ., zero ])} es@(e Σ., _) (Id-refl _) = {!!}
{-  proof sub σ (fill-holes es (coe (Id-refl _) —))
    === sub σ (fill-holes es —)
      :by: ap (λ — → sub σ (fill-holes es —)) $ coe-eval' —
    === sub σ e
      :by: Id-refl _
    === fill-holes (sub-all σ v es) (coe coer₀ (coe coer₁ —))
      :by: ap (fill-holes (sub-all σ v es)) $ subrel {_P_ = _==_} (
           proof —
             het== coe coer₁ —
               :by: isym $ coe-eval coer₁ —
             het== coe coer₀ (coe coer₁ —)
               :by: isym $ coe-eval coer₀ (coe coer₁ —)
           qed)
    === fill-holes (sub-all σ v es) (subc σ —)
      :by: Id-refl _
    === fill-holes (sub-all σ v es) (subc σ (coe (Id-refl _) —))
      :by: ap (λ — → fill-holes (sub-all σ v es) (subc σ —)) $
              sym {R = _==_} $ coe-eval' —
  qed
  where coer₀ = ap (λ — → Context V.[ tag Σ., — ] tag n) $
                +==→-== $ Id-refl (n + m)
        coer₁ = ap (λ — → Context V.[ tag Σ., — ] tag n) $
                sym $ +==→-== $ Id-refl (n + m) -}
sub-ctx-aux {m +1} σ — {V.[ tag Σ., l +1 ]} es p = {!!}
  -- ⊥-recursion _ $ ¬-+1+-==- l m p'
  -- where p' : l + m +1 == m
  --       p' = proof l + m +1
  --              === l + (m +1) :by: sym $ +-suc l m
  --              === m
  --                :by: ap pred $ sym {R = _==_} $ subrel $
  --                     ∧right $ from-Σ== $ ap head p
  --            qed
sub-ctx-aux σ ([ π x: C₀ ]→ C₁) es p = {!!}
sub-ctx-aux {m}{n} σ (λx, C) {v} es (Id-refl _) =
  proof subst σ (fill-holes es (coe (Id-refl _) (λx, C)))
    === subst σ (fill-holes es (λx, C))
      :by: ap (λ — → subst σ (fill-holes es —)) $
           coe-eval' (λx, C)
    === λx, subst (lift σ) (fill-holes es C)
      :by: Id-refl _
    === λx, {!!} -- fill-holes (sub-all (lift σ) v es) (subc (lift σ) (coe (Id-refl _) C))
      :by: ap λx,_ {!sub-ctx-aux (lift σ) C ? p!}
    === fill-holes (sub-all σ v es) (coe coer (λx, sub-context (lift σ) C))
      :by: {!!}
    === fill-holes (sub-all σ v es) (subc σ (λx, C))
      :by: Id-refl _
    === fill-holes (sub-all σ v es) (subc σ (coe (Id-refl _) (λx, C)))
      :by: ap (λ — → fill-holes (sub-all σ v es) (subc σ —)) $
           sym $ coe-eval' (λx, C)
  qed
  where coer = ap (λ v → Context v term n) $
               dmap-map n v λ {hole} → context-inhabited (λx, C) hole
        v' = map [ id × pred ] v
        p : map [ id × _+ m ] v == map [ id × _+ (m +1) ] v'
        p = {!!}
sub-ctx-aux {m}{n} σ ⌊ C ⌋ {v} es (Id-refl _) = {!!}
{-  proof subst σ (fill-holes es (coe (Id-refl _) ⌊ C ⌋))
    === ⌊ subst σ (fill-holes es C) ⌋
      :by: ap (λ — → subst σ (fill-holes es —)) $ coe-eval' ⌊ C ⌋
    === ⌊ subst σ (fill-holes es (coe (Id-refl _) C)) ⌋
      :by: ap (λ — → ⌊ subst σ (fill-holes es —) ⌋) $
           sym {R = _==_} $ coe-eval' C
    === ⌊ fill-holes (sub-all σ v es) (subc σ (coe (Id-refl _) C)) ⌋
      :by: ap ⌊_⌋ $ sub-ctx-aux σ C es $ Id-refl _
    === ⌊ fill-holes (sub-all σ v es) (subc σ C) ⌋
      :by: ap (λ — → ⌊ fill-holes (sub-all σ v es) (subc σ —) ⌋) $ coe-eval' C
    === fill-holes (sub-all σ v es) (coe coer ⌊ sub-context σ C ⌋)
      :by: ap (fill-holes (sub-all σ v es)) move-coe
    === fill-holes (sub-all σ v es) (subc σ ⌊ C ⌋)
      :by: Id-refl _
    === fill-holes (sub-all σ v es) (subc σ (coe (Id-refl _) ⌊ C ⌋))
      :by: ap (λ — → fill-holes (sub-all σ v es) (subc σ —)) $
           sym $ coe-eval' ⌊ C ⌋
  qed
  where coer = ap (λ — → Context — term n) $
               dmap-map n v λ {hole} → context-inhabited C hole
        move-coe : ⌊ subc σ C ⌋ == coe coer ⌊ sub-context σ C ⌋
        coer' = ap (λ v → Context v elim n) $
                dmap-map n v λ {hole} → context-inhabited C hole
        move-coe = subrel (
          proof ⌊ coe coer' (sub-context σ C) ⌋
            het== ⌊ sub-context σ C ⌋
              :by: Id.ap2 (λ v (C : Context v elim n) → ⌊ C ⌋)
                     (sym $ dmap-map n v λ {hole} → context-inhabited C hole)
                     (coe-eval coer' (sub-context σ C))
            het== coe coer ⌊ sub-context σ C ⌋
              :by: isym $ coe-eval coer ⌊ sub-context σ C ⌋
          qed)
-}
sub-ctx-aux σ (C₀ ` C₁) es p = {!!}
sub-ctx-aux σ (C₀ ꞉ C₁) es p = {!!}
-- sub-ctx-prop {k} σ e C =
--   proof subst σ (C [ e /—])
--     === sub σ (coe (Id-refl _) C)
--           [ subst (lift-by k σ) (coe (Id-refl _) e) /—]
--       :by: sub-ctx-aux σ e C k (Id-refl _)
--     === sub σ C [ subst (lift-by k σ) e /—]
--       :by: subrel {_P_ = _==_} $
--            ap2 (λ C e → sub σ C [ subst (lift-by k σ) e /—])
--                (coe-eval (Id-refl _) C) (coe-eval (Id-refl _) e)
--   qed
