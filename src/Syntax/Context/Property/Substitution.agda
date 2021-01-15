{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Syntax.Context.Property.Substitution
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax.Context.Arbitrary renaming ([_] to [[_]])
open import Syntax.Context.Property.Substitutable

open import Type.Sum renaming (_,_ to _Σ,_)
open import Data.Nat
open import Data.Tree.Binary
open import Relation.Binary.Pointwise
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

open import Type.Unit
open import Proposition.Sum
open import Proof

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
  (es : all-types (fmap 〈 id × _+ m 〉 t))
  → -------------------------------------
  all-types (fmap 〈 id × _+ n 〉 t)
sub-all σ ◻ es = es
sub-all σ [[ tag Σ, k ]] es = subst (lift-by k σ) es
sub-all σ (l /\ r) (es-l Σ, es-r) = sub-all σ l es-l Σ, sub-all σ r es-r

open import Data.Nat.Arithmetic.Subtraction.Unsafe hiding (-+)
open import Data.Maybe
open import Collection hiding (_~_; _-_)
open import Operation.Binary
open import Function.Proof

open import Proposition.Identity.Coercion

open Auxiliary

sub-all' : ∀{m n}
  (σ : Sub m n)
  (t : Holes)
  (p : {tag : ExprTag}{k : ℕ}(q : just (tag Σ, k) ∈ t) → m ≤ k)
  (es : all-types t)
  → ----------------------------------------------------------------
  all-types (fmap (f m n) t)
sub-all' _ ◻ _ es = es
sub-all' {m}{n} σ [[ tag Σ, k ]] p es =
  coe (ap (expr-of-type tag) q) (
    subst (lift-by (k - m) σ) (
      coe (ap (expr-of-type tag) $
           unsafe-prop-from-safe (λ l → k == l + m) p₀ $ sym $ -+ p₀)
          es))
  where p₀ : m ≤ k
        p₀ = p $ _ ∈leaf
        p₁ : m ≤ k + n
        p₁ = proof m
               〉 _≤_ 〉 k     :by: p₀
               〉 _≤_ 〉 k + n :by: postfix (_+ n) k
             qed
        q : k - m + n == n + k - m
        q = unsafe-prop-from-safe (λ l → l + n == n + k - m) p₀ (
          proof k - m [ p₀ ] + n
            === k + n - m [ p₁ ] :by: -+comm p₀
            === k + n - m        :by: sym $ unsafe-is-safe p₁
            === n + k - m        :by: ap (_- m) $ comm k n
          qed)
sub-all' σ (l /\ r) p (es-l Σ, es-r) =
  sub-all' σ l (λ q → p $ _ ∈left q /\ r) es-l Σ,
  sub-all' σ r (λ q → p $ _ ∈right l /\ q) es-r

open import Type.Sum hiding (_,_)

private
  het-Σ== : ∀{x : X}{y : Y}{z : Z}{w : W}
    (p : x Het.== y)
    (q : z Het.== w)
    → -----------------
    x Σ, z Het.== y Σ, w

het-Σ== (Het.refl x)(Het.refl z) = Het.refl (x Σ, z)

sub-all'-lift : ∀{m}{n}
  (σ : Sub m n)
  (t : Holes)
  (p : {tag : ExprTag}{k : ℕ}(q : just (tag Σ, k) ∈ t) → m +1 ≤ k)
  → ------------------------------------------------------------------
  let p' : {tag : ExprTag}{k : ℕ}(q : just (tag Σ, k) ∈ t) → m ≤ k
      p' {tag}{k} q =
        proof m 〉 _≤_ 〉 m +1 :by: postfix suc m
                〉 _≤_ 〉 k    :by: p q
        qed
  in sub-all' (lift σ) t p ~ sub-all' σ t p'

open import Logic

open import Axiom.FunctionExtensionality
open import Function.Extensionality

sub-all'-lift σ ◻ p es = Het.refl es
sub-all'-lift σ [[ tag Σ, 0 ]] q es = ⊥-recursion _ contradiction
  where contradiction : ⊥
        contradiction with q $ _ ∈leaf
        contradiction | ()
sub-all'-lift {m}{n} σ [[ tag Σ, k +1 ]] q es =
  proof coe coer₁ (subst (lift-by (k - m) (lift σ)) (coe coer₀ es))
    het== subst (lift-by (k - m) (lift σ)) (coe coer₀ es)
      :by: coe-eval coer₁ (subst (lift-by (k - m) (lift σ)) (coe coer₀ es))
    het== subst (lift-by (k +1 - m) σ) (coe coer₀' es)
      :by: Het.ap3 (λ (mn : ℕ × ℕ) → let m = pr₁ mn; n = pr₂ mn in
                    λ (σ : Sub m n)(e : expr-of-type tag m) →
                      subst σ e)
             (Σ== p₀ (subrel p₁)) σ==σ' e==e'
    het== coe coer₁' (subst (lift-by (k +1 - m) σ) (coe coer₀' es))
      :by: isym $
           coe-eval coer₁' (subst (lift-by (k +1 - m) σ) (coe coer₀' es))
  qed
  where p : m ≤ k
        p = ap pred ⦃ Relating-pred-≤ ⦄ (q $ _ ∈leaf)
        p' = proof m 〉 _≤_ 〉 k    :by: p
                     〉 _≤_ 〉 k +1 :by: postfix suc k [: _≤_ ]
             qed
        coer₀ = ap (expr-of-type tag){r = _==_}(
          proof k +1
            === k - m [ p ] + m +1 :by: ap suc $ sym {R = _==_} $ -+ p
            === k - m + m +1
              :by: ap (λ — → — + m +1) $ sym $ unsafe-is-safe p
            === k - m + (m +1)     :by: sym $ +-suc (k - m) m
          qed)
        coer₀' =
          ap (expr-of-type tag){r = _==_}(
          proof k +1
            === k +1 - m [ p' ] + m :by: sym $ -+ p'
            === k +1 - m + m
              :by: ap (_+ m) $ sym $ unsafe-is-safe p'
          qed)
        coer₁ =
          ap (expr-of-type tag){r = _==_}(
          proof k - m + (n +1)
            === k - m [ p ] + (n +1)
              :by: ap (_+ (n +1)) $ unsafe-is-safe p
            === k + (n +1) - m [ _ ]
              :by: -+comm p
            === k + (n +1) - m
              :by: sym $ unsafe-is-safe (
                proof m 〉 _≤_ 〉 k          :by: p
                        〉 _≤_ 〉 k + (n +1) :by: postfix (_+ (n +1)) k
                qed)
            === n + (k +1) - m
              :by: ap (_- m){r = _==_}(
                   proof k + (n +1)
                     === k + n +1   :by: +-suc k n
                     === n + k +1   :by: ap suc $ comm k n
                     === n + (k +1) :by: sym $ +-suc n k
                   qed)
          qed)
        coer₁' = ap (expr-of-type tag){r = _==_}(
          proof k +1 - m + n
            === k +1 - m [ p' ] + n :by: ap (_+ n) $ unsafe-is-safe p'
            === k +1 + n - m [ _ ]  :by: -+comm p'
            === k +1 + n - m        :by: sym $ unsafe-is-safe (
              proof m 〉 _≤_ 〉 k +1     :by: p'
                      〉 _≤_ 〉 k +1 + n :by: postfix (_+ n) (k +1)
              qed)
            === n + (k +1) - m      :by: ap (_- m) $ comm (k +1) n
          qed)
        p₀ = proof k - m + (m +1)
               === k - m + m +1        :by: +-suc (k - m) m
               === k - m [ p ] + m +1
                 :by: ap (λ — → — + m +1) $ unsafe-is-safe p
               === k +1                :by: ap suc $ -+ p
               === k +1 - m [ p' ] + m :by: sym $ -+ p' [: _==_ ]
               === k +1 - m + m
                 :by: ap (_+ m) $ sym $  unsafe-is-safe p'
             qed
        p₁ = proof k - m + (n +1)
               === (k - m +1) + n       :by: +-suc (k - m) n
               === (k - m [ p ] +1) + n
                 :by: ap (λ — → — +1 + n) $ unsafe-is-safe p
               === (k +1 - m [ p' ]) + n :by: ap (_+ n) (suc- p)
               === k +1 - m + n
                 :by: ap (_+ n) $ sym $ unsafe-is-safe p' [: _==_ ]
             qed
        p″ = ap Var $ +-suc (k - m) m
        σ==σ' =
          proof lift-by (k - m) (lift σ)
            het== lift-by (k - m) (lift σ) ∘ coe (sym p″)
              :by: het-fun-ext p″ (λ x →
                   ap (lift-by (k - m) (lift σ)) $
                   subrel {sup = Het._==_} $ sym {R = _==_} $
                   coe-2-eval (sym p″) x)
            het== lift-by (k - m +1) σ
              :by: isym $ fun-ext $ lift-by-lift~ (k - m) σ
            het== lift-by (k +1 - m) σ
              :by: ap (flip lift-by σ) ⦃ Relating-all-==-het== ⦄ (
                   proof k - m +1
                     === k - m [ p ] +1
                       :by: ap suc {r' = _==_} $ unsafe-is-safe p [: _==_ ]
                     === k +1 - m [ p' ] :by: suc- p [: _==_ ]
                     === k +1 - m
                       :by: sym $ unsafe-is-safe p' [: _==_ ]
                   qed)
                   [: Het._==_ ]
          qed
        e==e' = 
          proof coe coer₀ es
            het== es            :by: coe-eval coer₀ es
            het== coe coer₀' es :by: isym $ coe-eval coer₀' es [: Het._==_ ]
          qed
sub-all'-lift σ (l /\ r) p (es₀ Σ, es₁) =
  het-Σ== (sub-all'-lift σ l (λ q → p $ _ ∈left q /\ r) es₀)
          (sub-all'-lift σ r (λ q → p $ _ ∈right l /\ q) es₁)

sub-ctx-aux : ∀ {m n}
  (σ : Sub m n)
  {t}{tag}
  (C : Context t tag m)
  (es : all-types t)
  → ------------------------------------------------------------------
  subst σ (fill-holes es C)
  ==
  fill-holes (sub-all' σ t (context-inhabited C) es) (sub-context σ C)
sub-ctx-aux σ (term t) es = Id.refl (subst σ t)
sub-ctx-aux σ (elim e) es = Id.refl (subst σ e)
sub-ctx-aux {m}{n} σ {_}{tag} — es =
  proof subst σ es
    === fill-holes (subst σ es) —
      :by: Id.refl _
    === fill-holes (coe coer₂ (subst (lift-by (m - m) σ) (coe coer₁ es)))
                   (coe coer₀ —)
      :by: subrel {sup = _==_}{sub = Het._==_} $
           Het.ap3
             (λ k (e : all-types [[ tag Σ, k ]])
                  (C : Context [[ tag Σ, k ]] tag n) → fill-holes e C)
             n==n+m-m
             (proof subst σ es
                het== subst (lift-by (m - m) σ) (coe coer₁ es)
                  :by: Het.ap3
                         (λ k (σ : Sub (k + m)(k + n))
                              (e : expr-of-type tag (k + m)) → subst σ e)
                         (sym $ m -self==0)
                         (ap (flip lift-by σ) ⦃ Relating-all-==-het== ⦄ $
                          sym $ m -self==0)
                         (isym $ coe-eval coer₁ es)
                het== coe coer₂ (subst (lift-by (m - m) σ) (coe coer₁ es))
                  :by: isym $ coe-eval coer₂ _
              qed)
              (isym $ coe-eval coer₀ —)
  qed
  where n==n+m-m = sym {R = _==_} $ subrel $ left-inverse-of (_+ m) n
        coer₀ = ap (λ — → Context [[ tag Σ, — ]] tag n) n==n+m-m
        coer₁ = ap (λ — → expr-of-type tag (— + m)) $ sym $ m -self==0
        coer₂ = ap (expr-of-type tag){r = _==_}(
          proof m - m + n
            === n         :by: ap (_+ n) $ m -self==0
            === n + m - m
              :by: sym {R = _==_} $ subrel $ left-inverse-of (_+ m) n
          qed)
sub-ctx-aux σ {l /\ r}([ π x: C₀ ]→ C₁)(es₀ Σ, es₁) =
  ap2 ([ π x:_]→_){r₁ = _==_}(sub-ctx-aux σ C₀ es₀)(
  proof subst (lift σ) (fill-holes es₁ C₁)
    === fill-holes
          (sub-all' (lift σ) r (context-inhabited C₁) es₁)
          (sub-context (lift σ) C₁)
      :by: sub-ctx-aux (lift σ) C₁ es₁
    === fill-holes (sub-all' σ r p es₁) (sub-context (lift σ) C₁)
      :by: ap (λ — → fill-holes — (sub-context (lift σ) C₁)) $
           subrel {sup = _==_} $
           sub-all'-lift σ r (context-inhabited C₁) es₁
  qed)
  where p = context-inhabited (λx, C₁)
sub-ctx-aux σ {t} (λx, C) es = ap λx,_ {r = _==_}(
  proof subst (lift σ) (fill-holes es C)
    === fill-holes
          (sub-all' (lift σ) t (context-inhabited C) es)
          (sub-context (lift σ) C)
      :by: sub-ctx-aux (lift σ) C es
    === fill-holes (sub-all' σ t p es) (sub-context (lift σ) C)
      :by: ap (λ — → fill-holes — (sub-context (lift σ) C)) $
           subrel {sup = _==_} $
           sub-all'-lift σ t (context-inhabited C) es
  qed)
  where p = context-inhabited (λx, C)
sub-ctx-aux σ ⌊ C ⌋ es = ap ⌊_⌋ $ sub-ctx-aux σ C es
sub-ctx-aux σ (C₀ ` C₁)(es₀ Σ, es₁) =
  ap2 _`_ (sub-ctx-aux σ C₀ es₀)(sub-ctx-aux σ C₁ es₁)
sub-ctx-aux σ (C₀ ꞉ C₁)(es₀ Σ, es₁) =
  ap2 _꞉_ (sub-ctx-aux σ C₀ es₀)(sub-ctx-aux σ C₁ es₁)



-- sub-ctx-prop : ∀ {m n}
--   (σ : Sub m n)
--   {t : Holes}{tag}
--   (C : Context (fmap [ id × _+ m ] t) tag m)
--   (es : all-types (fmap [ id × _+ m ] t))
--   → ------------------------------------------------------------------
--   sub σ (fill-holes es C) == fill-holes (sub-all σ t es) (subc σ C)


-- fmap-fmn+m : ∀ m n →
--   fmap (Auxiliary.f m n) ∘ fmap [ id × _+ m ] == fmap [ id × _+ n ]
-- fmap-fmn+m m n =
--   proof fmap (Auxiliary.f m n) ∘ fmap [ id × _+ m ]
--     === fmap ([ id × (λ l → n + l - m) ] ∘ [ id × _+ m ])
--       :by: sym $ fmap-∘ (Auxiliary.f m n) [ id × _+ m ]
--     === fmap [ id × _+ n ]
--       :by: ap fmap $ subrel $ fun-ext (λ { (tag Σ, k) →
--            subrel $ Σ==
--              (Id.refl tag)
--              (proof n + (k + m) - m
--                 === n + k + m - m   :by: ap (_- m) $ assoc n k m
--                 het== n + k         :by: left-inverse-of (_+ m) (n + k)
--                 === k + n           :by: comm n k
--               qed)})
--   qed

{-
sub-all== :
  (σ : Sub m n)
  {t t' : Holes}
  (p : {tag : ExprTag}{k : ℕ}(q : just (tag Σ, k) ∈ t') → m ≤ k)
  {es : all-types (fmap [ id × _+ m ] t)}
  {es' : all-types t'}
  (t==t' : t' == fmap [ id × _+ m ] t)
  (es==es' : es Het.== es')
  → ----------------------------------------------------------------
  sub-all σ t es Het.== sub-all' σ t' p es'
sub-all== σ {◻} p (Id.refl _) es==es' = es==es'
sub-all== {m}{n} σ {[[ tag Σ, k ]]} p {es}{es'}(Id.refl _) es==es' =
  proof subst (lift-by k σ) es
    het== subst (lift-by (k + m - m) σ) (coe coer₀ es')
      :by: Het.ap3 (λ (mn : ℕ × ℕ) → let m = pr₁ mn; n = pr₂ mn in
                    λ (σ : Sub m n)(e : expr-of-type tag m) →
                    subst σ e)
             (ap2 Σ._,_ (ap (_+ m) p₀) (ap (_+ n) p₀))
             (ap (flip lift-by σ) p₀)
             (proof es
                het== es'           :by: es==es'
                het== coe coer₀ es' :by: isym $ coe-eval coer₀ es'
              qed)
    het== coe coer₁ (subst (lift-by (k + m - m) σ) (coe coer₀ es'))
      :by: isym $ coe-eval coer₁ _
  qed
  where p₀ : k == k + m - m
        p₀ = sym {R = _==_} $ subrel $ left-inverse-of (_+ m) k
        p₁ =
          proof k + m - m + n
            === k + n
              :by: ap (_+ n) $ subrel $ left-inverse-of (_+ m) k
            === n + k
              :by: comm k n
            === n + k + m - m
              :by: sym {R = _==_} $ subrel $ left-inverse-of (_+ m) (n + k)
            === n + (k + m) - m
              :by: ap (_- m) $ sym $ assoc n k m
          qed
        coer₀ = ap (λ — → expr-of-type tag (— + m)) p₀                
        coer₁ = ap (λ — → expr-of-type tag —) p₁
sub-all== {m}{n} σ {l /\ r} p
  {es-l Σ, es-r}{es-l' Σ, es-r'}(Id.refl _) es==es' =
  het-Σ== (sub-all== σ (λ q → p $ _ ∈left q /\ _)(Id.refl _) $
                     subrel $ ∧left $ from-Σ== $
                     subrel {sup = _==_} es==es')
          (sub-all== σ (λ q → p $ _ ∈right _ /\ q)(Id.refl _) $
                     ∧right $ from-Σ== $
                     subrel {sup = _==_} es==es')
-}

{-
context-inhabited-tree : ∀{t : Holes}{tag}{m}
  (C : Context t tag m)
  → -------------------------------------
  ∃ λ (t' : Holes) → t == fmap [ id × _+ m ] t'
context-inhabited-tree (λx, C) with context-inhabited-tree C
context-inhabited-tree {m = m} (λx, C) | t , Id.refl _ =
  fmap [ id × suc ] t , ap (λ — → — t) (
  proof fmap [ id × _+ (m +1) ]
    === fmap ([ id × _+ m ] ∘ [ id × suc ])
      :by: ap fmap $ subrel $ fun-ext (λ { (tag Σ, k) →
             subrel $ Σ== (Id.refl tag) (subrel $ +-suc k m)})
    === fmap [ id × _+ m ] ∘ fmap [ id × suc ]
      :by: fmap-∘ [ id × _+ m ] [ id × suc ]
  qed)
context-inhabited-tree ⌊ C ⌋ = context-inhabited-tree C
context-inhabited-tree (term t) = ◻ , Id.refl _
context-inhabited-tree (elim e) = ◻ , Id.refl _
context-inhabited-tree {[[ tag Σ, k ]]} — =
  [[ tag Σ, 0 ]] , Id.refl _
context-inhabited-tree ([ _ x: C₀ ]→ C₁)
  with context-inhabited-tree C₀ | context-inhabited-tree C₁
context-inhabited-tree {m = m} ([ _ x: C₀ ]→ C₁)
  | l , Id.refl _ | r , Id.refl _ =
  l /\ fmap [ id × suc ] r , ap (λ — → fmap [ id × _+ m ] l /\ — r) (
  proof fmap [ id × _+ (m +1) ]
    === fmap ([ id × _+ m ] ∘ [ id × suc ])
      :by: ap fmap $ subrel $ fun-ext (λ { (tag Σ, k) →
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
-}

