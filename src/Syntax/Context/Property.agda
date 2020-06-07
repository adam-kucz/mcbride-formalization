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

sub-ctx-prop : ∀ {m n}
  (σ : Sub m n)
  {t : Holes}{tag}
  (C : Context (fmap [ id × _+ m ] t) tag m)
  (es : all-types (fmap [ id × _+ m ] t))
  → ------------------------------------------------------------------
  sub σ (fill-holes es C) == fill-holes (sub-all σ t es) (subc σ C)

open import Proposition.Identity
  renaming (Idₚ to Id) hiding (refl)
open import Type.Sum hiding (_,_)
open import Data.Nat.Arithmetic.Subtraction.Unsafe
open import Operation.Binary

fmap-fmn+m : ∀ m n →
  fmap (Auxiliary.f m n) ∘ fmap [ id × _+ m ] == fmap [ id × _+ n ]
fmap-fmn+m m n =
  proof fmap (Auxiliary.f m n) ∘ fmap [ id × _+ m ]
    === fmap ([ id × (λ l → n + l - m) ] ∘ [ id × _+ m ])
      :by: sym $ fmap-∘ (Auxiliary.f m n) [ id × _+ m ]
    === fmap [ id × _+ n ]
      :by: ap fmap $ subrel $ fun-ext (λ { (tag Σ., k) →
           subrel $ Σ==
             (Id.refl tag)
             (proof n + (k + m) - m
                === n + k + m - m   :by: ap (_- m) $ assoc n k m
                het== n + k         :by: left-inverse-of (_+ m) (n + k)
                === k + n           :by: comm n k
              qed)})
  qed

context-inhabited-tree : ∀{t : Holes}{tag}{m}
  (C : Context t tag m)
  → -------------------------------------
  ∃ λ (t' : Holes) → t == fmap [ id × _+ m ] t'
context-inhabited-tree (λx, C) with context-inhabited-tree C
context-inhabited-tree {m = m} (λx, C) | t , Id.refl _ =
  fmap [ id × suc ] t , ap (λ — → — t) (
  proof fmap [ id × _+ (m +1) ]
    === fmap ([ id × _+ m ] ∘ [ id × suc ])
      :by: ap fmap $ subrel $ fun-ext (λ { (tag Σ., k) →
             subrel $ Σ== (Id.refl tag) (subrel $ +-suc k m)})
    === fmap [ id × _+ m ] ∘ fmap [ id × suc ]
      :by: fmap-∘ [ id × _+ m ] [ id × suc ]
  qed)
context-inhabited-tree ⌊ C ⌋ = context-inhabited-tree C
context-inhabited-tree (term t) = ◻ , Id.refl _
context-inhabited-tree (elim e) = ◻ , Id.refl _
context-inhabited-tree {[[ tag Σ., k ]]} — =
  [[ tag Σ., 0 ]] , Id.refl _
context-inhabited-tree ([ _ x: C₀ ]→ C₁)
  with context-inhabited-tree C₀ | context-inhabited-tree C₁
context-inhabited-tree {m = m} ([ _ x: C₀ ]→ C₁)
  | l , Id.refl _ | r , Id.refl _ =
  l /\ fmap [ id × suc ] r , ap (λ — → fmap [ id × _+ m ] l /\ — r) (
  proof fmap [ id × _+ (m +1) ]
    === fmap ([ id × _+ m ] ∘ [ id × suc ])
      :by: ap fmap $ subrel $ fun-ext (λ { (tag Σ., k) →
             subrel $ Σ== (Id.refl tag) (subrel $ +-suc k m)})
    === fmap [ id × _+ m ] ∘ fmap [ id × suc ]
      :by: fmap-∘ [ id × _+ m ] [ id × suc ]
  qed)
context-inhabited-tree (C₀ ` C₁)
  with context-inhabited-tree C₀ | context-inhabited-tree C₁
context-inhabited-tree (C₀ ` C₁) | l , Id.refl _ | r , Id.refl _ =
  l /\ r , Id.refl _
context-inhabited-tree (C₀ ꞉ C₁)
  with context-inhabited-tree C₀ | context-inhabited-tree C₁
context-inhabited-tree (C₀ ꞉ C₁) | l , Id.refl _ | r , Id.refl _ =
  l /\ r , Id.refl _

sub-ctx-aux : ∀ {m n}
  (σ : Sub m n)
  {t' : Holes}{tag}
  (C : Context t' tag m)
  {t : Holes}
  (es : all-types (fmap [ id × _+ m ] t))
  (p : t' == fmap [ id × _+ m ] t)
  → ------------------------------------------------------------------
  let es' : all-types t'
      es' = coe (ap all-types $ sym p) es
      C' = Context (fmap [ id × _+ m ] t) tag m
      C' = coe (ap (λ — → Context — tag m) p) C
  in
  subst σ (fill-holes es' C)
  ==
  fill-holes {t = fmap [ id × _+ n ] t} (sub-all σ t es) (subc σ C')
sub-ctx-aux σ (term t) {◻} es (Id.refl ◻) = {!!}
{-  proof subst σ t
    === fill-holes es (term (subst σ t))
      :by: Id.refl _
    === fill-holes es (coe (Id.refl _) (term (subst σ t)))
      :by: ap (fill-holes es) $ sym {R = _==_} $
           coe-eval-hom (term (subst σ t))
    === fill-holes es (subc {t = ◻} σ (term t))
      :by: Id.refl _
    === fill-holes es (subc {t = ◻} σ (coe (Id.refl _) (term t)))
      :by: ap (λ — → fill-holes es (subc {t = ◻} σ —)) $ sym $
           coe-eval-hom (term t)
  qed -}
sub-ctx-aux σ (elim e) {◻} es (Id.refl ◻) = {!!}
{-  proof subst σ e
    === fill-holes es (elim (subst σ e))
      :by: Id.refl _
    === fill-holes es (coe (Id.refl _) (elim (subst σ e)))
      :by: ap (fill-holes es) $ sym {R = _==_} $
           coe-eval-hom (elim (subst σ e))
    === fill-holes es (subc {t = ◻} σ (elim e))
      :by: Id.refl _
    === fill-holes es (subc {t = ◻} σ (coe (Id.refl _) (elim e)))
      :by: ap (λ — → fill-holes es (subc {t = ◻} σ —)) $ sym $
           coe-eval-hom (elim e)
  qed -}
sub-ctx-aux {m}{n} σ — {t@([[ tag Σ., zero ]])} es (Id.refl _) = {!!}
{-  proof subst σ (coe (Id.refl _) es)
    === subst σ es
      :by: ap (subst σ) $ coe-eval-hom es
    === fill-holes (subst σ es) —          
      :by: Id.refl _
    === fill-holes (subst σ es) (coe p₀ (coe p₁  —))
      :by: ap (fill-holes (subst σ es)) $ sym {R = _==_} $
           coe-2-eval p₀ p₁ —
    === fill-holes (subst σ es) (subc {t = t} σ —)
      :by: Id.refl _
    === fill-holes (subst σ es) (subc {t = t} σ (coe (Id.refl _) —))
      :by: ap (λ — → fill-holes (subst σ es) (subc {t = t} σ —)) $
           sym {R = _==_} $ coe-eval-hom —
  qed
  where p₀ = ap (λ f → Context (f [[ tag Σ., 0 ]]) tag n) $
             fmap-fmn+m m n
        p₁ = ap (λ f → Context (f [[ tag Σ., 0 ]]) tag n) $
             sym $ fmap-fmn+m m n -}
sub-ctx-aux {m} σ {[[ tag' Σ., m ]]} — {[[ tag Σ., l +1 ]]} es p = {!!}
{-  ⊥-recursion _ $ ¬-+1+-==- l m $ sym $ q p
  where q : ∀{a b}(p : Id Holes [[ tag' Σ., a ]] [[ tag Σ., b ]]) → a == b
        q (Id.refl _) = Id.refl _ -}
sub-ctx-aux σ ([ π x: C₀ ]→ C₁) {t} es p = {!!}
sub-ctx-aux σ {t'} (λx, C) es p with context-inhabited-tree C
sub-ctx-aux {m}{n} σ {_}{tag} (λx, C) {t} es p | t″ , Id.refl _ =
  proof λx, subst (lift σ) (fill-holes (coe p₀ es) C)
    === λx, subst (lift σ) (fill-holes (coe (Id.refl _) (coe p₀ es)) C)
      :by: ap (λ — → λx, subst (lift σ) (fill-holes — C)) $
           sym {R = _==_} $ coe-eval-hom (coe p₀ es)
    === λx, fill-holes (sub-all (lift σ) t″ (coe p₀ es))
                       (subc (lift σ) (coe (Id.refl _) C))
      :by: ap λx,_ $ sub-ctx-aux (lift σ) C (coe p₀ es) (Id.refl _)
    === fill-holes (sub-all σ t es) (subc σ (coe p₁ (λx, C)))
      :by: {!!}
  qed
  where p₀ = ap all-types $ sym p
        p₁ = ap (λ — → Context — tag m) p
        -- q = ap (λ f → Context (f t) term n) $ fmap-fmn+m m n
sub-ctx-aux σ ⌊ C ⌋ {t} es p = {!!}
sub-ctx-aux σ (C₀ ` C₁) {t} es p = {!!}
sub-ctx-aux σ (C₀ ꞉ C₁) {t} es p = {!!}
{-
sub-ctx-aux {m}{n} σ — (e Σ., _) {V.[ tag Σ., zero ]} (Id.refl _) = {!!}
{-  proof sub σ e
    === fill-holes (subst σ e Σ., _) (coe coer₀ (coe coer₁ —))
      :by: ap (fill-holes (subst σ e Σ., _)) $ subrel {_P_ = _==_} (
           proof —
             het== coe coer₁ —
               :by: isym $ coe-eval coer₁ —
             het== coe coer₀ (coe coer₁ —)
               :by: isym $ coe-eval coer₀ (coe coer₁ —)
           qed)
    === fill-holes (subst σ (coe (Id.refl _) e) Σ., _)
                   (subc σ (coe (Id.refl _) —))
      :by: ap2 (λ e C → fill-holes (subst σ e Σ., _) (subc σ C))
               (sym {R = _==_} $ coe-eval-hom e)
               (sym {R = _==_} $ coe-eval-hom —)
  qed
  where coer₀ = ap (λ — → Context V.[ tag Σ., — ] tag n) $
                +==→-== $ Id.refl (n + m)
        coer₁ = ap (λ — → Context V.[ tag Σ., — ] tag n) $
                sym $ +==→-== $ Id.refl (n + m) -}
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
sub-ctx-aux σ (λx, C) es (Id.refl _) with context-inhabited-vec C
sub-ctx-aux {m}{n} σ {k} (λx, C) es {v} (Id.refl _) | v' , p =
  proof λx, sub (lift σ) (fill-holes es C)
    === λx, fill-holes (sub-all (lift σ) v' p es)
              (coe (ap (λ v → Context v term (n +1)) (dmap-map (n +1) v' f″))
                (sub-context (lift σ)
                  (coe (ap (λ v → Context v term (m +1)) p) C)))
      :by: ap λx,_ $ sub-ctx-aux (lift σ) C es p
    === λx, fill-holes (coe (ap all-types $ sym v==)
                            (sub-all σ v (Id.refl _) es))
                       (sub-context (lift σ) C)
      :by: ap λx,_ $ subrel {_P_ = _==_} step₀
    === fill-holes (sub-all σ v (Id.refl _) es)
                   (coe coer (λx, sub-context (lift σ) C))
      :by: step₁
    === fill-holes (sub-all σ v (Id.refl _) es) (subc σ (λx, C))
      :by: Id.refl _
    === fill-holes (sub-all σ v (Id.refl _) es)
                   (subc σ (coe (Id.refl _) (λx, C)))
      :by: ap (λ — → fill-holes (sub-all σ v (Id.refl _) es) (subc σ —)) $
           sym $ coe-eval-hom (λx, C) 
  qed
  where v== = dmap-map n v λ {hole} → context-inhabited (λx, C) hole
        coer = ap (λ v → Context v term n) v==
        p' : ∀{k}(v v' : Holes k)
             (p : map [ id × _+ m ] v == map [ id × _+ (m +1) ] v')
             → ----------------------------------------------------
             v == map [ id × suc ] v'
        p' [] [] p = Id.refl []
        p' ((tag Σ., l) ∷ v) ((tag' Σ., l') ∷ v') p =
          ap2 _∷_ (ap2 Σ._,_ q' q) $ p' v v' $ ap tail p
          where q : l == l' +1
                q = proof l
                      === l + m - m [ _ ]
                        :by: sym $ +==→-== $ Id.refl (l + m)
                      === l' + (m +1) - m [ _ ]
                        :by: -== (ap (pr₂ ∘ head) {r' = _==_} p) (Id.refl m)
                      === (l' +1) + m - m [ postfix ((l' +1) +_) m ]
                        :by: -== (+-suc l' m) (Id.refl m)
                      === l' +1
                        :by: +==→-== $ Id.refl (l' +1 + m)
                    qed
                q' : tag == tag'
                q' = ap (pr₁ ∘ head) p
        f″ : ∀{hole}
             (p : member hole (map [ id × _+ (m +1) ] v'))
             → -------------------------------------------
             m +1 ≤ pr₂ hole
        f″ p with V.∈map⁻¹ v' [ id × _+ (m +1) ] p
        f″ p | tag Σ., l , (Id.refl _ , _) = postfix (l +_) (m +1)
        step₀ :
          fill-holes (sub-all (lift σ) v' p es)
            (coe (ap (λ v → Context v term (n +1)) (dmap-map (n +1) v' f″))
              (sub-context (lift σ)
                (coe (ap (λ v → Context v term (m +1)) p) C)))
          Het.==
          fill-holes (coe (ap all-types $ sym v==)
                          (sub-all σ v (Id.refl _) es))
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
             -- het== sub-all σ v (Id.refl _) es
             --   :by: {!!}
             het== coe (ap all-types $ sym v==) (sub-all σ v (Id.refl _) es)
               :by: {!!} -- isym $ coe-eval (ap all-types $ sym v==)
                         --           (sub-all σ v (Id.refl _) es)
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
                             (sub-all σ v (Id.refl _) es))
                   (isym $ coe-eval coer (λx, sub-context (lift σ) C))
sub-ctx-aux {m} σ ⌊ C ⌋ es (Id.refl _) = {!!}
sub-ctx-aux {m} σ (C₀ ` C₁) es p = {!!}
sub-ctx-aux {m} σ (C₀ ꞉ C₁) es p = {!!}
{-
sub-ctx-aux {m}{n} σ (λx, C) {v} es (Id.refl _) =
  proof subst σ (fill-holes es (coe (Id.refl _) (λx, C)))
    === subst σ (fill-holes es (λx, C))
      :by: ap (λ — → subst σ (fill-holes es —)) $
           coe-eval-hom (λx, C)
    === λx, subst (lift σ) (fill-holes es C)
      :by: Id.refl _
    === λx, {!!} -- fill-holes (sub-all (lift σ) v es) (subc (lift σ) (coe (Id.refl _) C))
      :by: ap λx,_ {!!}
    === fill-holes (sub-all σ v es) (coe coer (λx, sub-context (lift σ) C))
      :by: {!!}
    === fill-holes (sub-all σ v es) (subc σ (λx, C))
      :by: Id.refl _
    === fill-holes (sub-all σ v es) (subc σ (coe (Id.refl _) (λx, C)))
      :by: ap (λ — → fill-holes (sub-all σ v es) (subc σ —)) $
           sym $ coe-eval-hom (λx, C)
  qed
  where coer = ap (λ v → Context v term n) $
               dmap-map n v λ {hole} → context-inhabited (λx, C) hole
sub-ctx-aux {m}{n} σ ⌊ C ⌋ {v} es (Id.refl _) = {!!}
{-  proof subst σ (fill-holes es (coe (Id.refl _) ⌊ C ⌋))
    === ⌊ subst σ (fill-holes es C) ⌋
      :by: ap (λ — → subst σ (fill-holes es —)) $ coe-eval-hom ⌊ C ⌋
    === ⌊ subst σ (fill-holes es (coe (Id.refl _) C)) ⌋
      :by: ap (λ — → ⌊ subst σ (fill-holes es —) ⌋) $
           sym {R = _==_} $ coe-eval-hom C
    === ⌊ fill-holes (sub-all σ v es) (subc σ (coe (Id.refl _) C)) ⌋
      :by: ap ⌊_⌋ $ sub-ctx-aux σ C es $ Id.refl _
    === ⌊ fill-holes (sub-all σ v es) (subc σ C) ⌋
      :by: ap (λ — → ⌊ fill-holes (sub-all σ v es) (subc σ —) ⌋) $ coe-eval-hom C
    === fill-holes (sub-all σ v es) (coe coer ⌊ sub-context σ C ⌋)
      :by: ap (fill-holes (sub-all σ v es)) move-coe
    === fill-holes (sub-all σ v es) (subc σ ⌊ C ⌋)
      :by: Id.refl _
    === fill-holes (sub-all σ v es) (subc σ (coe (Id.refl _) ⌊ C ⌋))
      :by: ap (λ — → fill-holes (sub-all σ v es) (subc σ —)) $
           sym $ coe-eval-hom ⌊ C ⌋
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
--     === sub σ (coe (Id.refl _) C)
--           [ subst (lift-by k σ) (coe (Id.refl _) e) /—]
--       :by: sub-ctx-aux σ e C k (Id.refl _)
--     === sub σ C [ subst (lift-by k σ) e /—]
--       :by: subrel {_P_ = _==_} $
--            ap2 (λ C e → sub σ C [ subst (lift-by k σ) e /—])
--                (coe-eval (Id.refl _) C) (coe-eval (Id.refl _) e)
--   qed
-}

-}
