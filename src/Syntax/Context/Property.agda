{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Syntax.Context.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax.Context.Arbitrary renaming ([_] to [[_]])
open import Syntax.Context.Substitutable public

open import Type.Sum hiding (_,_)
open import Data.Nat
open import Data.Tree.Binary
open import Function hiding (_$_)

open import Syntax
open import Liftable
open import Substitution as Subs
  hiding (_[_/new])

private
  subst = λ {tag}{m}{n} →
    sub ⦃ subst = SubstitutableExpr {tag = tag} ⦄ {m = m}{n}
  _[_/new] = Subs._[_/new] ⦃ subst = SubstitutableElim ⦄
  subc = λ {tag}{t}{m}{n} →
    sub ⦃ subst = SubstitutableContext {t = t}{tag} ⦄ {m = m}{n}
infix 180 _[_/new]

open import Proof

open import Proposition.Identity.Coercion

import Data.Functor as F
open import Data.Functor.Construction
open import Data.Maybe.Functor
open import Data.Tree.Binary.Functor
open F.Functor (ComposeFunctor ⦃ BinaryTreeFunctor ⦄ ⦃ MaybeFunctor ⦄)

instance
  UptoBinaryTreeFunctor =
    ComposeFunctor ⦃ BinaryTreeFunctor ⦄ ⦃ MaybeFunctor ⦄

sub-all : ∀{m n}
  (σ : Sub m n)
  (t : Holes)
  (es : all-types (fmap [ id × _+ m ] t))
  → -------------------------------------
  all-types (fmap [ id × _+ n ] t)
sub-all σ ◻ es = es
sub-all σ [[ tag Σ., k ]] es = subst (lift-by k σ) es
sub-all σ (l /\ r) (es-l Σ., es-r) = sub-all σ l es-l Σ., sub-all σ r es-r

open import Logic
open import Function.Proof

open import Axiom.FunctionExtensionality

postulate
  sub-ctx-prop : ∀ {m n}
    (σ : Sub m n)
    {t : Holes}{tag}
    (C : Context (fmap [ id × _+ m ] t) tag m)
    (es : all-types (fmap [ id × _+ m ] t))
    → ------------------------------------------------------------------
    sub σ (fill-holes es C) == fill-holes (sub-all σ t es) (subc σ C)

{-
sub-ctx-aux σ (term t) es {[]} (Id-refl []) = {!!}
{-  proof sub σ t
    === fill-holes es (term (sub σ t))
      :by: Id-refl _
    === fill-holes es (coe (Id-refl _) (term (sub σ t)))
      :by: ap (fill-holes es) $ sym $ coe-eval' (term (sub σ t))
    === fill-holes es (subc σ (coe (Id-refl _) (term t)))
      :by: ap (λ — → fill-holes es (subc σ —)) $
           sym $ coe-eval' (term t)
  qed -}
sub-ctx-aux σ (elim e) es {[]} (Id-refl []) = {!!}
{-  proof sub σ e
    === fill-holes es (elim (sub σ e))
      :by: Id-refl _
    === fill-holes es (coe (Id-refl _) (elim (sub σ e)))
      :by: ap (fill-holes es) $ sym $ coe-eval' (elim (sub σ e))
    === fill-holes es (subc σ (coe (Id-refl _) (elim e)))
      :by: ap (λ — → fill-holes es (subc σ —)) $
           sym $ coe-eval' (elim e)
  qed -}
sub-ctx-aux {m}{n} σ — (e Σ., _) {V.[ tag Σ., zero ]} (Id-refl _) = {!!}
{-  proof sub σ e
    === fill-holes (subst σ e Σ., _) (coe coer₀ (coe coer₁ —))
      :by: ap (fill-holes (subst σ e Σ., _)) $ subrel {_P_ = _==_} (
           proof —
             het== coe coer₁ —
               :by: isym $ coe-eval coer₁ —
             het== coe coer₀ (coe coer₁ —)
               :by: isym $ coe-eval coer₀ (coe coer₁ —)
           qed)
    === fill-holes (subst σ (coe (Id-refl _) e) Σ., _)
                   (subc σ (coe (Id-refl _) —))
      :by: ap2 (λ e C → fill-holes (subst σ e Σ., _) (subc σ C))
               (sym {R = _==_} $ coe-eval' e)
               (sym {R = _==_} $ coe-eval' —)
  qed
  where coer₀ = ap (λ — → Context V.[ tag Σ., — ] tag n) $
                +==→-== $ Id-refl (n + m)
        coer₁ = ap (λ — → Context V.[ tag Σ., — ] tag n) $
                sym $ +==→-== $ Id-refl (n + m) -}
sub-ctx-aux {m +1} σ — es {V.[ tag Σ., l +1 ]} p = {!!}
{-  ⊥-recursion _ $ ¬-+1+-==- l m p'
  where p' : l + m +1 == m
        p' = proof l + m +1
               === l + (m +1) :by: sym $ +-suc l m
               === m
                 :by: ap pred $ sym {R = _==_} $ subrel $
                      ∧right $ from-Σ== $ ap head p
             qed -}
sub-ctx-aux {m} σ ([ π x: C₀ ]→ C₁) es p = {!!}
sub-ctx-aux σ (λx, C) es (Id-refl _) with context-inhabited-vec C
sub-ctx-aux {m}{n} σ {k} (λx, C) es {v} (Id-refl _) | v' , p =
  proof λx, sub (lift σ) (fill-holes es C)
    === λx, fill-holes (sub-all (lift σ) v' p es)
              (coe (ap (λ v → Context v term (n +1)) (dmap-map (n +1) v' f″))
                (sub-context (lift σ)
                  (coe (ap (λ v → Context v term (m +1)) p) C)))
      :by: ap λx,_ $ sub-ctx-aux (lift σ) C es p
    === λx, fill-holes (coe (ap all-types $ sym v==)
                            (sub-all σ v (Id-refl _) es))
                       (sub-context (lift σ) C)
      :by: ap λx,_ $ subrel {_P_ = _==_} step₀
    === fill-holes (sub-all σ v (Id-refl _) es)
                   (coe coer (λx, sub-context (lift σ) C))
      :by: step₁
    === fill-holes (sub-all σ v (Id-refl _) es) (subc σ (λx, C))
      :by: Id-refl _
    === fill-holes (sub-all σ v (Id-refl _) es)
                   (subc σ (coe (Id-refl _) (λx, C)))
      :by: ap (λ — → fill-holes (sub-all σ v (Id-refl _) es) (subc σ —)) $
           sym $ coe-eval' (λx, C) 
  qed
  where v== = dmap-map n v λ {hole} → context-inhabited (λx, C) hole
        coer = ap (λ v → Context v term n) v==
        p' : ∀{k}(v v' : Holes k)
             (p : map [ id × _+ m ] v == map [ id × _+ (m +1) ] v')
             → ----------------------------------------------------
             v == map [ id × suc ] v'
        p' [] [] p = Id-refl []
        p' ((tag Σ., l) ∷ v) ((tag' Σ., l') ∷ v') p =
          ap2 _∷_ (ap2 Σ._,_ q' q) $ p' v v' $ ap tail p
          where q : l == l' +1
                q = proof l
                      === l + m - m [ _ ]
                        :by: sym $ +==→-== $ Id-refl (l + m)
                      === l' + (m +1) - m [ _ ]
                        :by: -== (ap (pr₂ ∘ head) {r' = _==_} p) (Id-refl m)
                      === (l' +1) + m - m [ postfix ((l' +1) +_) m ]
                        :by: -== (+-suc l' m) (Id-refl m)
                      === l' +1
                        :by: +==→-== $ Id-refl (l' +1 + m)
                    qed
                q' : tag == tag'
                q' = ap (pr₁ ∘ head) p
        f″ : ∀{hole}
             (p : member hole (map [ id × _+ (m +1) ] v'))
             → -------------------------------------------
             m +1 ≤ pr₂ hole
        f″ p with V.∈map⁻¹ v' [ id × _+ (m +1) ] p
        f″ p | tag Σ., l , (Id-refl _ , _) = postfix (l +_) (m +1)
        step₀ :
          fill-holes (sub-all (lift σ) v' p es)
            (coe (ap (λ v → Context v term (n +1)) (dmap-map (n +1) v' f″))
              (sub-context (lift σ)
                (coe (ap (λ v → Context v term (m +1)) p) C)))
          Het.==
          fill-holes (coe (ap all-types $ sym v==)
                          (sub-all σ v (Id-refl _) es))
                     (sub-context (lift σ) C)
        step₀ = Het.ap3
          (λ(v : Holes k)
            (es : all-types v)
            (C : Context v term (n +1)) → fill-holes es C)
          (proof map [ id × _+ (n +1) ] v'
             === map [ id × (_+ n) ∘ suc ] v'
               :by: ap (λ — → map [ id × — ] v') {!subrel $ fun-ext ?!}
             === dmap (map [ id × _+ m ] v) _
               :by: {!!}
           qed)
          (proof sub-all (lift σ) v' p es
             -- het== sub-all σ v (Id-refl _) es
             --   :by: {!!}
             het== coe (ap all-types $ sym v==) (sub-all σ v (Id-refl _) es)
               :by: {!!} -- isym $ coe-eval (ap all-types $ sym v==)
                         --           (sub-all σ v (Id-refl _) es)
           qed)
          (proof coe (ap (λ v → Context v term (n +1))
                         (dmap-map (n +1) v' f″))
                     (sub-context (lift σ)
                       (coe (ap (λ v → Context v term (m +1)) p) C))
             het== sub-context (lift σ) C
               :by: {!!}
           qed)
        step₁ = subrel {_P_ = _==_} $
           Het.ap3 (λ v (es : all-types v)(C : Context v term n) →
                      fill-holes es C)
                   v==
                   (coe-eval (ap all-types $ sym v==)
                             (sub-all σ v (Id-refl _) es))
                   (isym $ coe-eval coer (λx, sub-context (lift σ) C))
sub-ctx-aux {m} σ ⌊ C ⌋ es (Id-refl _) = {!!}
sub-ctx-aux {m} σ (C₀ ` C₁) es p = {!!}
sub-ctx-aux {m} σ (C₀ ꞉ C₁) es p = {!!}
{-
sub-ctx-aux {m}{n} σ (λx, C) {v} es (Id-refl _) =
  proof subst σ (fill-holes es (coe (Id-refl _) (λx, C)))
    === subst σ (fill-holes es (λx, C))
      :by: ap (λ — → subst σ (fill-holes es —)) $
           coe-eval' (λx, C)
    === λx, subst (lift σ) (fill-holes es C)
      :by: Id-refl _
    === λx, {!!} -- fill-holes (sub-all (lift σ) v es) (subc (lift σ) (coe (Id-refl _) C))
      :by: ap λx,_ {!!}
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
-}
-}
