{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Syntax.Context.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax.Context.Arbitrary

open import Type.Sum hiding (_,_)
open import Data.Vec as V hiding ([_])
open import Data.Nat
open import Function hiding (_$_)

open import Syntax
open import Renaming
open import Liftable
open import Substitution as Subs
  hiding (_[_/new])

instance
  SubstitutableContext : ∀{tag m}{v : Holes m} →
    Substitutable (
      λ n → context (map [ id × _+ n ] v) tag n)

open import Collection

context-inhabited : ∀{tag m n}{v : Holes m}
  (C : context v tag n)
  → --------------------------------------------------
  ∀ (hole : ExprTag × ℕ)(p : hole ∈ v) → n ≤ pr₂ hole

open import Logic
open import Proof
open import Function.Proof

context-inhabited — (_ Σ., n) (x∈x∷ []) = refl {R = _≤_} n
context-inhabited ([ π x: C₀ ]→ C₁) hole p
  with ⟶ (∈++ _ _) p
context-inhabited ([ π x: C₀ ]→ C₁) hole p | ∨left q =
  context-inhabited C₀ hole q
context-inhabited {n = n} ([ π x: C₀ ]→ C₁) hole p | ∨right q =
  proof n
    〉 _≤_ 〉 n +1     :by: postfix suc n
    〉 _≤_ 〉 pr₂ hole :by: context-inhabited C₁ hole q
  qed
context-inhabited {n = n} (λx, C) hole p =
  proof n
    〉 _≤_ 〉 n +1     :by: postfix suc n
    〉 _≤_ 〉 pr₂ hole :by: context-inhabited C hole p
  qed
context-inhabited ⌊ C ⌋ hole p = context-inhabited C hole p
context-inhabited (C₀ ` C₁) hole p with ⟶ (∈++ _ _) p
context-inhabited (C₀ ` C₁) hole p | ∨left q = context-inhabited C₀ hole q
context-inhabited (C₀ ` C₁) hole p | ∨right q = context-inhabited C₁ hole q
context-inhabited (C₀ ꞉ C₁) hole p with ⟶ (∈++ _ _) p
context-inhabited (C₀ ꞉ C₁) hole p | ∨left q = context-inhabited C₀ hole q
context-inhabited (C₀ ꞉ C₁) hole p | ∨right q = context-inhabited C₁ hole q

-- open import Proposition.Empty
--   renaming (⊥-recursion to ⊥ₜ-recursion) using ()
-- open import Relation.Binary
open import Data.Nat

open import Proposition.Identity.Coercion
-- sub-1-hole-ctx : ∀ k {m m' n n'}
--   (σ : Sub m n)
--   (p : m' == k + m)
--   (q : n' == k + n)
--   {tag₀ tag₁}
--   (C : 1-hole-ctx tag₀ m' tag₁ m)
--   → ----------------------------------------
--   1-hole-ctx tag₀ n' tag₁ n

sub-context : ∀{m n}
  (σ : Sub m n)
  {k}
  {v : Holes k}
  {tag}
  (C : context v tag m)
  → ----------------------------------------
  let v' = dmap v (λ hole p →
             pr₁ hole Σ.,
             pr₂ hole - m [ context-inhabited C hole p ] + n)
  in context v' tag n
sub-context σ (term t) = {!!}
sub-context σ (elim e) = {!!}
sub-context {m}{n} σ {tag = tag} — =
  coe (ap (λ — → context V.[ tag Σ., (— + n) ] tag n) $
       sym $ +==→-== $ Id-refl m)
      —
sub-context σ ([ π x: C₀ ]→ C₁) = {!!}
sub-context σ (λx, C) = {!!}
sub-context σ ⌊ C ⌋ = ⌊ sub-context σ C ⌋
sub-context {n = n} σ (_`_ {v₀ = v₀}{v₁} C₀ C₁) =
  coe (ap (λ — → context — elim n) {!dmap++ v₀ v₁ !})
      (sub-context σ C₀ ` sub-context σ C₁)
sub-context σ (C₀ ꞉ C₁) = {!!}
-- sub-1-hole-ctx k σ p q ([ π x: C ↓]→ T) =
--   [ π x: sub-1-hole-ctx k σ p q C ↓]→ sub (lift σ) T
-- sub-1-hole-ctx k σ p q ⌊ C ⌋ = ⌊ sub-1-hole-ctx k σ p q C ⌋
-- sub-1-hole-ctx k σ p q (f ` C ↓) = sub σ f ` sub-1-hole-ctx k σ p q C ↓
-- sub-1-hole-ctx k σ p q (C ↓` s) = sub-1-hole-ctx k σ p q C ↓` sub σ s
-- sub-1-hole-ctx k σ p q (s ꞉ C ↓) = sub σ s ꞉ sub-1-hole-ctx k σ p q C ↓
-- sub-1-hole-ctx k σ p q (C ↓꞉ S) = sub-1-hole-ctx k σ p q C ↓꞉ sub σ S
-- sub-1-hole-ctx zero {n' = n'} σ p q {tag} — =
--   coe (ap (1-hole-ctx tag n' tag) q) —
-- sub-1-hole-ctx (k +1) {m} σ p q — = ⊥ₜ-recursion _ (irrefl m (
--   proof m
--     〉 _≤_ 〉 k + m    :by: postfix (k +_) m
--     〉 _<_ 〉 k + m +1 :by: postfix suc (k + m) 
--     === m           :by: sym p
--   qed))
-- sub-1-hole-ctx zero {m}{m'} σ p q (λx, C) = ⊥ₜ-recursion _ (irrefl (m +1) (
--   proof m +1
--     〉 _≤_ 〉 m'   :by: 1-hole-ctx-inhabited C
--     〉 _==_ 〉 m   :by: p
--     〉 _<_ 〉 m +1 :by: postfix suc m
--   qed))
-- sub-1-hole-ctx (k +1) {m}{_}{n} σ p q (λx, C) =
--   λx, sub-1-hole-ctx k (lift σ)
--         (trans p (sym $ +-suc k m))
--         (trans q (sym $ +-suc k n)) C
-- sub-1-hole-ctx zero {m}{m'} σ p q [ π x: S ]→ C ↓ =
--   ⊥ₜ-recursion _ (irrefl (m +1) (
--     proof m +1
--       〉 _≤_ 〉 m'   :by: 1-hole-ctx-inhabited C
--       〉 _==_ 〉 m   :by: p
--       〉 _<_ 〉 m +1 :by: postfix suc m
--     qed))
-- sub-1-hole-ctx (k +1) {m}{_}{n} σ p q [ π x: S ]→ C ↓ =
--   [ π x: sub σ S ]→
--     sub-1-hole-ctx k (lift σ)
--       (trans p (sym $ +-suc k m))
--       (trans q (sym $ +-suc k n)) C ↓

{-
sub-1-hole-ctx== :
  ∀{k₀ k₁ m₀ m₁ m'₀ m'₁ n₀ n₁ n'₀ n'₁ tag₀ tag₁ tag'₀ tag'₁}
  {σ₀ : Sub m₀ n₀}
  {σ₁ : Sub m₁ n₁}
  {C₀ : 1-hole-ctx tag'₀ m'₀ tag₀ m₀}
  {C₁ : 1-hole-ctx tag'₁ m'₁ tag₁ m₁}
  (p₀ : m'₀ == k₀ + m₀)
  (q₀ : n'₀ == k₀ + n₀)
  (p₁ : m'₁ == k₁ + m₁)
  (q₁ : n'₁ == k₁ + n₁)
  (eq₀ : k₀ == k₁)
  (eq₁ : m₀ == m₁)
  (eq₂ : n₀ == n₁)
  (eq₃ : tag₀ == tag₁)
  (eq₄ : tag'₀ == tag'₁)
  (eq₅ : σ₀ Het.== σ₁)
  (eq₆ : C₀ Het.== C₁)
  → ----------------------------------------
  sub-1-hole-ctx k₀ σ₀ p₀ q₀ C₀
  Het.==
  sub-1-hole-ctx k₁ σ₁ p₁ q₁ C₁
sub-1-hole-ctx== (Id-refl _)(Id-refl _)(Id-refl _)(Id-refl _)
  (Id-refl _)(Id-refl _)(Id-refl _)(Id-refl _)(Id-refl _)
  (Het.refl _)(Het.refl _) = Het.refl _

open import Function hiding (_$_)

sub-1-hole-ctx-id : ∀ k {m m' tag₀ tag₁}
  (p : m' == k + m)
  (C : 1-hole-ctx tag₀ m' tag₁ m)
  → ----------------------------------------
  sub-1-hole-ctx k var p p C Het.== C
sub-1-hole-ctx-id k p ([ σ x: C ↓]→ T) =
  ap2 [ σ x:_↓]→_
    (sub-1-hole-ctx-id k p C)
    (proof sub (lift var) T
       === sub var T :by: ap (λ — → sub — T) lift-var
       het== T       :by: ==→~ sub-id T
     qed)
sub-1-hole-ctx-id k p ⌊ C ⌋ = ap ⌊_⌋ $ sub-1-hole-ctx-id k p C
sub-1-hole-ctx-id k p (f ` C ↓) =
  ap2 _`_↓ (subrel {_P_ = Het._==_} $ ap (λ — → — f) sub-id)
           (sub-1-hole-ctx-id k p C)
sub-1-hole-ctx-id k p (C ↓` s) =
  ap2 _↓`_ (sub-1-hole-ctx-id k p C)
           (subrel {_P_ = Het._==_} $ ap (λ — → — s) sub-id)
sub-1-hole-ctx-id k p (s ꞉ C ↓) =
  ap2 _꞉_↓ (subrel {_P_ = Het._==_} $ ap (λ — → — s) sub-id)
           (sub-1-hole-ctx-id k p C)
sub-1-hole-ctx-id k p (C ↓꞉ S) =
  ap2 _↓꞉_ (sub-1-hole-ctx-id k p C)
           (subrel {_P_ = Het._==_} $ ap (λ — → — S) sub-id)
sub-1-hole-ctx-id zero {m}{m'} p (λx, C) =
  ⊥-recursion _ $ irrefl (m +1) (
  proof m +1
    〉 _≤_ 〉 m'   :by: 1-hole-ctx-inhabited C
    〉 _==_ 〉 m   :by: p
    〉 _<_ 〉 m +1 :by: postfix suc m
  qed)
sub-1-hole-ctx-id (k +1){m}{m'} p (λx, C) =
  proof sub-1-hole-ctx (k +1) var p p (λx, C)
    === λx, sub-1-hole-ctx k (lift var) _ _ C
      :by: Id-refl _
    === λx, sub-1-hole-ctx k var _ _ C
      :by: ap (λ — → λx, sub-1-hole-ctx k — p' p' C) lift-var
    het== λx, C
      :by: ap λx,_ $ sub-1-hole-ctx-id k p' C
  qed
  where p' = proof m'
               === k + m +1   :by: p
               === k + (m +1) :by: sym (+-suc k m)
             qed
sub-1-hole-ctx-id zero {m}{m'} p [ σ x: S ]→ C ↓ =
  ⊥-recursion _ $ irrefl (m +1) (
  proof m +1
    〉 _≤_ 〉 m'   :by: 1-hole-ctx-inhabited C
    〉 _==_ 〉 m   :by: p
    〉 _<_ 〉 m +1 :by: postfix suc m
  qed)
sub-1-hole-ctx-id (k +1){m}{m'} p [ π x: S ]→ C ↓ =
  proof sub-1-hole-ctx (k +1) var p p ([ π x: S ]→ C ↓)
    === [ π x: sub var S ]→ sub-1-hole-ctx k (lift var) _ _ C ↓
      :by: Id-refl _
    === [ π x: S ]→ sub-1-hole-ctx k var _ _ C ↓
      :by: ap2 (λ S σ → [ π x: S ]→ sub-1-hole-ctx k σ p' p' C ↓)
               (ap (λ — → — S) sub-id)
               lift-var
    het== [ π x: S ]→ C ↓
      :by: ap [ π x: S ]→_↓ $ sub-1-hole-ctx-id k p' C
  qed
  where p' = proof m'
               === k + m +1   :by: p
               === k + (m +1) :by: sym (+-suc k m)
             qed
sub-1-hole-ctx-id zero {m' = m'}{tag} p — =
  coe-eval (ap (1-hole-ctx tag m' tag) p) —
sub-1-hole-ctx-id (k +1) {m} p — = ⊥-recursion _ $ irrefl m (
  proof m
    〉 _≤_ 〉 k + m    :by: postfix (k +_) m
    〉 _<_ 〉 k + m +1 :by: postfix suc (k + m) 
    === m           :by: sym p
  qed)

sub-1-hole-ctx-∘ : ∀ k {m m' n n' l l' tag₀ tag₁}
  (σ : Sub n l)
  (τ : Sub m n)
  (pm : m' == k + m)
  (pn : n' == k + n)
  (pl : l' == k + l)
  (C : 1-hole-ctx tag₀ m' tag₁ m)
  → ----------------------------------------
  sub-1-hole-ctx k (σ ⍟ τ) pm pl C
  Het.==
  sub-1-hole-ctx k σ pn pl (sub-1-hole-ctx k τ pm pn C)
sub-1-hole-ctx-∘ k σ τ pm pn pl ([ δ x: C ↓]→ T) =
  ap2 [ δ x:_↓]→_
    (sub-1-hole-ctx-∘ k σ τ pm pn pl C)
    (proof sub (lift (σ ⍟ τ)) T
       === sub (lift σ ⍟ lift τ) T
         :by: ap (λ — → sub — T) $ sym {R = _==_} $ lift-⍟ σ τ
       het== sub (lift σ) (sub (lift τ) T)
         :by: sym (==→~ $ sub-∘ (lift σ) (lift τ)) T
     qed)
sub-1-hole-ctx-∘ k σ τ pm pn pl ⌊ C ⌋ =
  ap ⌊_⌋ $ sub-1-hole-ctx-∘ k σ τ pm pn pl C
sub-1-hole-ctx-∘ k σ τ pm pn pl (f ` C ↓) =
  ap2 _`_↓ (sym (==→~ (sub-∘ σ τ)) f)
           (sub-1-hole-ctx-∘ k σ τ pm pn pl C)
sub-1-hole-ctx-∘ k σ τ pm pn pl (C ↓` s) =
  ap2 _↓`_ (sub-1-hole-ctx-∘ k σ τ pm pn pl C)
           (sym (==→~ (sub-∘ σ τ)) s)
sub-1-hole-ctx-∘ k σ τ pm pn pl (s ꞉ C ↓) =
  ap2 _꞉_↓ (sym (==→~ (sub-∘ σ τ)) s)
           (sub-1-hole-ctx-∘ k σ τ pm pn pl C)
sub-1-hole-ctx-∘ k σ τ pm pn pl (C ↓꞉ S) =
  ap2 _↓꞉_ (sub-1-hole-ctx-∘ k σ τ pm pn pl C)
           (sym (==→~ (sub-∘ σ τ)) S)
sub-1-hole-ctx-∘ zero σ τ (Id-refl _)(Id-refl _)(Id-refl _) — =
  proof coe (Id-refl _) —
    het== —
      :by: coe-eval (Id-refl _) —
    het== sub-1-hole-ctx zero σ (Id-refl _)(Id-refl _) —
      :by: sym {R = Het._==_} $ coe-eval (Id-refl _) —
    het== sub-1-hole-ctx zero σ _ _ (coe (Id-refl _) —)
      :by: ap (sub-1-hole-ctx zero σ _ _) $ sym {R = Het._==_} $
           coe-eval (Id-refl _) —
  qed
sub-1-hole-ctx-∘ (k +1) {m} σ τ pm pn pl — =
  ⊥-recursion _ $ irrefl m (
  proof m
    〉 _≤_ 〉 k + m    :by: postfix (k +_) m
    〉 _<_ 〉 k + m +1 :by: postfix suc (k + m) 
    === m           :by: sym pm
  qed)
sub-1-hole-ctx-∘ zero {m}{m'} σ τ pm pn pl [ δ x: S ]→ C ↓ =
  ⊥-recursion _ $ irrefl (m +1) (
  proof m +1
    〉 _≤_ 〉 m'   :by: 1-hole-ctx-inhabited C
    〉 _==_ 〉 m   :by: pm
    〉 _<_ 〉 m +1 :by: postfix suc m
  qed)
sub-1-hole-ctx-∘ (k +1) {m}{_}{n}{_}{l} σ τ pm pn pl [ δ x: S ]→ C ↓ =
  proof [ δ x: sub (σ ⍟ τ) S ]→ sub-1-hole-ctx k (lift (σ ⍟ τ)) pm' pl' C ↓
    === [ δ x: sub σ (sub τ S) ]→
          sub-1-hole-ctx k (lift σ ⍟ lift τ) pm' pl' C ↓
      :by: ap2 (λ renS τ' → [ δ x: renS S ]→ sub-1-hole-ctx k τ' pm' pl' C ↓)
             (sym $ sub-∘ σ τ) (sym {R = _==_} $ lift-⍟ σ τ)
    het== [ δ x: sub σ (sub τ S) ]→
            sub-1-hole-ctx k (lift σ) pn' pl' (
              sub-1-hole-ctx k (lift τ) pm' pn' C) ↓
      :by: ap (λ — → [ δ x: sub σ (sub τ S) ]→ — ↓) $
           sub-1-hole-ctx-∘ k (lift σ) (lift τ) pm' pn' pl' C
  qed
  where pm' = trans pm (sym $ +-suc k m)
        pn' = trans pn (sym $ +-suc k n)
        pl' = trans pl (sym $ +-suc k l)
sub-1-hole-ctx-∘ zero {m}{m'} σ τ pm pn pl (λx, C) =
  ⊥-recursion _ $ irrefl (m +1) (
  proof m +1
    〉 _≤_ 〉 m'   :by: 1-hole-ctx-inhabited C
    〉 _==_ 〉 m   :by: pm
    〉 _<_ 〉 m +1 :by: postfix suc m
  qed)
sub-1-hole-ctx-∘ (k +1) {m}{_}{n}{_}{l} σ τ pm pn pl (λx, C) =
  proof λx, sub-1-hole-ctx k (lift (σ ⍟ τ)) pm' pl' C
    === λx, sub-1-hole-ctx k (lift σ ⍟ lift τ) pm' pl' C
      :by: ap (λ — → λx, sub-1-hole-ctx k — pm' pl' C) $ sym {R = _==_} $
           lift-⍟ σ τ
    het== λx, sub-1-hole-ctx k (lift σ) pn' pl' (
              sub-1-hole-ctx k (lift τ) pm' pn' C)
      :by: ap λx,_ $ sub-1-hole-ctx-∘ k (lift σ) (lift τ) pm' pn' pl' C
  qed
  where pm' = trans pm (sym $ +-suc k m)
        pn' = trans pn (sym $ +-suc k n)
        pl' = trans pl (sym $ +-suc k l)

open import Axiom.FunctionExtensionality

SubstitutableContext {n = n} =
  DirectSubstitutable
    (λ σ → sub-1-hole-ctx n σ (Id-refl _)(Id-refl _))
    (λ {m} → subrel {_P_ = _==_} $ fun-ext $
             sub-1-hole-ctx-id n (Id-refl (n + m)))
    λ σ τ → subrel {_P_ = _==_} $ fun-ext $ sym $
            sub-1-hole-ctx-∘ n σ τ (Id-refl _)(Id-refl _)(Id-refl _)

private
  subst = λ {tag}{m}{n} →
    sub ⦃ subst = SubstitutableExpr {tag = tag} ⦄ {m = m}{n}
  _[_/new] = Subs._[_/new] ⦃ subst = SubstitutableElim ⦄
infix 180 _[_/new]

open import Function.Coercion

sub-ctx-aux : ∀{l m n tag tag'}
  (σ : Sub m n)
  (e : expr-of-type tag l)
  (C[—] : 1-hole-ctx tag l tag' m)
  (k : ℕ)
  (p : l == k + m)
  → ----------------------------------------
  subst σ (C[—] [ e /—])
  ==
  sub ⦃ subst = SubstitutableContext ⦄ σ
      (coe (ap (λ — → 1-hole-ctx tag — tag' m) p) C[—])
    [ subst (lift-by k σ) (coe (ap (expr-of-type tag) p) e) /—]
sub-ctx-aux σ e — zero (Id-refl l) =
  proof subst σ e
    === sub-1-hole-ctx zero σ (Id-refl _)(Id-refl _) — [ subst σ e /—]
      :by: ap (λ — → — [ subst σ e /—]) $
           sym {R = _==_} $ subrel {_P_ = _==_} $
           coe-eval (Id-refl _) —
    === sub-1-hole-ctx zero σ _ _ (coe (Id-refl _) —)
          [ subst σ (coe (Id-refl _) e) /—]
      :by: sym {R = _==_} $ subrel {_P_ = _==_} $
           ap2 (λ C e → sub-1-hole-ctx zero σ (Id-refl _)(Id-refl _) C
                          [ subst σ e /—])
               (coe-eval (Id-refl _) —)
               (coe-eval (Id-refl _) e)
  qed
sub-ctx-aux {l} σ e — (k +1) p =
  ⊥-recursion _ $ irrefl l (
  proof l
    〉 _≤_ 〉 k + l    :by: postfix (k +_) l
    〉 _<_ 〉 k + l +1 :by: postfix suc (k + l)
    === l           :by: sym p
  qed)
sub-ctx-aux σ e (λx, C[—]) zero (Id-refl m) =
  ⊥-recursion _ $ irrefl (m +1) (
  proof m +1
    〉 _≤_ 〉 m    :by: 1-hole-ctx-inhabited C[—]
    〉 _<_ 〉 m +1 :by: postfix suc m
  qed)
sub-ctx-aux {_}{m}{n}{tag} σ e (λx, C[—])(k +1)(Id-refl _) =
  proof subst σ (λx, C[—] [ e /—])
    === λx, subst (lift σ) (C[—] [ e /—])
      :by: Id-refl _
    === λx, sub-1-hole-ctx k (lift σ)(Id-refl _)(Id-refl _)(
              coe (ap (λ — → 1-hole-ctx tag — term (m +1)) p') C[—])
            [ e' /—]
      :by: ap λx,_ $ sub-ctx-aux (lift σ) e C[—] k p'
    === λx, sub-1-hole-ctx k (lift σ) p' (sym $ +-suc k n)
                (coe (Id-refl _) C[—])
              [ e″ /—]
      :by: subrel {_P_ = _==_} $
           Het.ap3 (λ i (C : 1-hole-ctx tag i term (n +1))
                        (e : expr-of-type tag i) → λx, C [ e /—])
             (+-suc k n)
             transform-C
             transform-e
    === sub-1-hole-ctx (k +1) σ (Id-refl _)(Id-refl _)
            (coe (Id-refl _) (λx, C[—]))
          [ e″ /—]
      :by: ap (λ — → sub-1-hole-ctx (k +1) σ (Id-refl _) (Id-refl _) — [ e″ /—])
             move-coe
  qed
  where p' = sym $ +-suc k m
        e' = subst (lift-by k (lift σ)) (coe (ap (expr-of-type tag) p') e)
        e″ = subst (lift-by (k +1) σ) (coe (Id-refl _) e)
        transform-C :
          sub-1-hole-ctx k (lift σ)(Id-refl _)(Id-refl _)(
            coe (ap (λ — → 1-hole-ctx tag — term (m +1)) p') C[—])
          Het.==
          sub-1-hole-ctx k (lift σ) p' (sym $ +-suc k n) (
            coe (Id-refl _) C[—])
        transform-C =
          proof sub-1-hole-ctx k (lift σ)(Id-refl _)(Id-refl _)
                  (coe (ap (λ — → 1-hole-ctx tag — term (m +1)) p') C[—])
            het== sub-1-hole-ctx k (lift σ) p' (sym $ +-suc k n) C[—]
              :by: sub-1-hole-ctx==
                    (Id-refl _)(Id-refl _) p' (sym $ +-suc k n)
                    (Id-refl k)(Id-refl (m +1))(Id-refl (n +1))
                    (Id-refl term)(Id-refl tag)
                    (Het.refl (lift σ))
                    (coe-eval (ap (λ — → 1-hole-ctx tag — term (m +1)) p') C[—])
            het== sub-1-hole-ctx k (lift σ) p' (sym $ +-suc k n)
                    (coe (Id-refl _) C[—])
              :by: ap (sub-1-hole-ctx k (lift σ) p' (sym $ +-suc k n)) $
                   sym {R = Het._==_} $
                   coe-eval (Id-refl _) C[—]
          qed
        transform-e : e' Het.== e″
        transform-e = 
          proof subst (lift-by k (lift σ)) (coe (ap (expr-of-type tag) p') e)
            het== subst (lift-by k (lift σ) ∘ coe (ap Var $ sym $ +-suc k m))
                      (coe (Id-refl _) e)
              :by: Het.ap3 (λ i (σ : Sub i (k + (n +1)))
                                (e : expr-of-type tag i) → subst σ e)
                     (+-suc k m)
                     (isym $ ∘-coe (ap Var $ sym $ +-suc k m)
                                   (lift-by k (lift σ)))
                     (proof coe (ap (expr-of-type tag) p') e
                        het== e
                          :by: coe-eval (ap (expr-of-type tag) p') e
                        het== (coe (Id-refl _) e)
                          :by: isym $ coe-eval (Id-refl _) e
                      qed)
            het== subst (lift-by (k +1) σ) (coe (Id-refl _) e)
              :by: Id.ap2 (λ i (σ : Sub (k + m +1) i) →
                               subst {n = i} σ (coe (Id-refl _) e))
                          (+-suc k n)
                          (isym $ fun-ext $ lift-by-lift~ k σ)
          qed
        move-coe :
          λx, coe (Id-refl _) C[—]
          ==
          coe (Id-refl _) (λx, C[—])
        move-coe = subrel {_P_ = _==_} (
          proof λx,_ {e = tag}{k + m +1}{m} (coe (Id-refl _) C[—])
            het== λx,_ {e = tag}{k + m +1}{m} C[—]
              :by: Id.ap2 {K = λ i _ → 1-hole-ctx tag i term m}
                     (λ i (C : 1-hole-ctx tag i term (m +1)) →
                          λx,_ {e = tag}{i}{m} C)
                     (Id-refl _) (coe-eval (Id-refl _) C[—])
            het== coe (Id-refl _) (λx, C[—])
              :by: isym $ coe-eval (Id-refl _) (λx, C[—])
          qed)
sub-ctx-aux σ e [ π x: S ]→ C[—] ↓ zero (Id-refl m) =
  ⊥-recursion _ $ irrefl (m +1) (
  proof m +1
    〉 _≤_ 〉 m    :by: 1-hole-ctx-inhabited C[—]
    〉 _<_ 〉 m +1 :by: postfix suc m
  qed)
sub-ctx-aux {_}{m}{n}{tag} σ e [ π x: S ]→ C[—] ↓ (k +1)(Id-refl _) =
  proof subst σ ([ π x: S ]→ C[—] [ e /—])
    === [ π x: subst σ S ]→ subst (lift σ) (C[—] [ e /—])
      :by: Id-refl _
    === [ π x: subst σ S ]→
          (sub-1-hole-ctx k (lift σ) (Id-refl _)(Id-refl _)
            (coe (ap (λ — → 1-hole-ctx tag — term (m +1)) p') C[—]) [ e' /—])
      :by: ap [ π x: subst σ S ]→_ $
           sub-ctx-aux (lift σ) e C[—] k p'
    === [ π x: subst σ S ]→
          sub-1-hole-ctx k (lift σ) p' (sym $ +-suc k n)
            (coe (Id-refl _) C[—]) [ e″ /—]
      :by: subrel {_P_ = _==_} $
           Het.ap3 (λ i (C : 1-hole-ctx tag i term (n +1))
                        (e : expr-of-type tag i) → [ π x: subst σ S ]→ C [ e /—])
             (+-suc k n)
             transform-C
             transform-e
    === sub-1-hole-ctx (k +1) σ (Id-refl _)(Id-refl _)(
            coe (Id-refl _) [ π x: S ]→ C[—] ↓) [ e″ /—]
      :by: ap (λ — → sub-1-hole-ctx (k +1) σ (Id-refl _)(Id-refl _) — [ e″ /—])
           move-coe
  qed
  where p' = sym $ +-suc k m
        e' = subst (lift-by k (lift σ)) (coe (ap (expr-of-type tag) p') e)
        e″ = subst (lift-by (k +1) σ) (coe (Id-refl _) e)
        transform-C :
          sub-1-hole-ctx k (lift σ)(Id-refl _)(Id-refl _)(
            coe (ap (λ — → 1-hole-ctx tag — term (m +1)) p') C[—])
          Het.==
          sub-1-hole-ctx k (lift σ) p' (sym $ +-suc k n) (
            coe (Id-refl _) C[—])
        transform-C =
          proof sub-1-hole-ctx k (lift σ)(Id-refl _)(Id-refl _)
                  (coe (ap (λ — → 1-hole-ctx tag — term (m +1)) p') C[—])
            het== sub-1-hole-ctx k (lift σ) p' (sym $ +-suc k n) C[—]
              :by: sub-1-hole-ctx==
                    (Id-refl _)(Id-refl _) p' (sym $ +-suc k n)
                    (Id-refl k)(Id-refl (m +1))(Id-refl (n +1))
                    (Id-refl term)(Id-refl tag)
                    (Het.refl (lift σ))
                    (coe-eval (ap (λ — → 1-hole-ctx tag — term (m +1)) p') C[—])
            het== sub-1-hole-ctx k (lift σ) p' (sym $ +-suc k n)
                    (coe (Id-refl _) C[—])
              :by: ap (sub-1-hole-ctx k (lift σ) p' (sym $ +-suc k n)) $
                   sym {R = Het._==_} $
                   coe-eval (Id-refl _) C[—]
          qed
        transform-e : e' Het.== e″
        transform-e = 
          proof subst (lift-by k (lift σ)) (coe (ap (expr-of-type tag) p') e)
            het== subst (lift-by k (lift σ) ∘ coe (ap Var $ sym $ +-suc k m))
                      (coe (Id-refl _) e)
              :by: Het.ap3 (λ i (σ : Sub i (k + (n +1)))
                                (e : expr-of-type tag i) → subst σ e)
                     (+-suc k m)
                     (isym $ ∘-coe (ap Var $ sym $ +-suc k m)
                                   (lift-by k (lift σ)))
                     (proof coe (ap (expr-of-type tag) p') e
                        het== e
                          :by: coe-eval (ap (expr-of-type tag) p') e
                        het== (coe (Id-refl _) e)
                          :by: isym $ coe-eval (Id-refl _) e
                      qed)
            het== subst (lift-by (k +1) σ) (coe (Id-refl _) e)
              :by: Id.ap2 (λ i (σ : Sub (k + m +1) i) →
                               subst {n = i} σ (coe (Id-refl _) e))
                          (+-suc k n)
                          (isym $ fun-ext $ lift-by-lift~ k σ)
          qed
        move-coe :
          [ π x: S ]→ coe (Id-refl _) C[—] ↓
          ==
          coe (Id-refl _) ([ π x: S ]→ C[—] ↓)
        move-coe = subrel {_P_ = _==_} (
          proof [ π x: S ]→ coe (Id-refl _) C[—] ↓
            het== [ π x: S ]→ C[—] ↓
              :by: Id.ap2 {K = λ i _ → 1-hole-ctx tag i term m}
                     (λ i (C : 1-hole-ctx tag i term (m +1)) →
                          [ π x: S ]→ C ↓)
                     (Id-refl _) (coe-eval (Id-refl _) C[—])
            het== coe (Id-refl _) ([ π x: S ]→ C[—] ↓)
              :by: isym $ coe-eval (Id-refl _) ([ π x: S ]→ C[—] ↓)
          qed)
sub-ctx-aux σ e ([ π x: C[—] ↓]→ T) k (Id-refl _) =
  proof [ π x: subst σ (C[—] [ e /—]) ]→ T'
    === [ π x: f (coe (Id-refl _) C[—]) [ r (coe (Id-refl _) e) /—] ]→ T'
      :by: ap ([ π x:_]→ T') $ sub-ctx-aux σ e C[—] k (Id-refl _)
    === [ π x: f C[—] [ r (coe (Id-refl _) e) /—] ]→ T'
      :by: ap (λ C → [ π x: f C [ r (coe (Id-refl _) e) /—] ]→ T') $
           subrel {_P_ = _==_} $ coe-eval (Id-refl _) C[—]
    === f (coe (Id-refl _) ([ π x: C[—] ↓]→ T)) [ r (coe (Id-refl _) e) /—]
      :by: ap (λ C → f C [ r (coe (Id-refl _) e) /—]) $
           subrel {_P_ = _==_} $ sym {R = Het._==_} $
           coe-eval (Id-refl _) ([ π x: C[—] ↓]→ T)
  qed
  where f = sub-1-hole-ctx k σ (Id-refl _)(Id-refl _)
        r = subst (lift-by k σ)
        T' = subst (lift σ) T
sub-ctx-aux σ e ⌊ C[—] ⌋ k (Id-refl _) =
  proof ⌊ subst σ  (C[—] [ e /—]) ⌋
    === ⌊ f (coe (Id-refl _) C[—]) [ r (coe (Id-refl _) e) /—] ⌋
      :by: ap ⌊_⌋ $ sub-ctx-aux σ e C[—] k (Id-refl _)
    === ⌊ f C[—] [ r (coe (Id-refl _) e) /—] ⌋
      :by: ap (λ C → ⌊ f C [ r (coe (Id-refl _) e) /—] ⌋) $
           subrel {_P_ = _==_} $ coe-eval (Id-refl _) C[—]
    === f (coe (Id-refl _) ⌊ C[—] ⌋) [ r (coe (Id-refl _) e) /—]
      :by: ap (λ C → f C [ r (coe (Id-refl _) e) /—]) $
           subrel {_P_ = _==_} $ sym $
           coe-eval (Id-refl _) ⌊ C[—] ⌋
  qed
  where f = sub-1-hole-ctx k σ (Id-refl _)(Id-refl _)
        r = subst (lift-by k σ)
sub-ctx-aux σ e (f″ ` C[—] ↓) k (Id-refl _) =
  proof f' ` subst σ (C[—] [ e /—])
    === f' ` f (coe (Id-refl _) C[—]) [ r (coe (Id-refl _) e) /—]
      :by: ap (f' `_) $ sub-ctx-aux σ e C[—] k (Id-refl _)
    === f' ` (f C[—] [ r (coe (Id-refl _) e) /—])
      :by: ap (λ C → f' ` f C [ r (coe (Id-refl _) e) /—]) $
           subrel {_P_ = _==_} $ coe-eval (Id-refl _) C[—]
    === f (coe (Id-refl _) (f″ ` C[—] ↓)) [ r (coe (Id-refl _) e) /—]
      :by: ap (λ C → f C [ r (coe (Id-refl _) e) /—]) $
           subrel {_P_ = _==_} $ sym {R = Het._==_} $
           coe-eval (Id-refl _) (f″ ` C[—] ↓)
  qed
  where f = sub-1-hole-ctx k σ (Id-refl _)(Id-refl _)
        r = subst (lift-by k σ)
        f' = subst σ f″
sub-ctx-aux σ e (C[—] ↓` s) k (Id-refl _) =
  proof subst σ (C[—] [ e /—]) ` s'
    === f (coe (Id-refl _) C[—]) [ r (coe (Id-refl _) e) /—] ` s'
      :by: ap (_` s') $ sub-ctx-aux σ e C[—] k (Id-refl _)
    === f C[—] [ r (coe (Id-refl _) e) /—] ` s'
      :by: ap (λ C → f C [ r (coe (Id-refl _) e) /—] ` s') $
           subrel {_P_ = _==_} $ coe-eval (Id-refl _) C[—]
    === f (coe (Id-refl _) (C[—] ↓` s)) [ r (coe (Id-refl _) e) /—]
      :by: ap (λ C → f C [ r (coe (Id-refl _) e) /—]) $
           subrel {_P_ = _==_} $ sym {R = Het._==_} $
           coe-eval (Id-refl _) (C[—] ↓` s)
  qed
  where f = sub-1-hole-ctx k σ (Id-refl _)(Id-refl _)
        r = subst (lift-by k σ)
        s' = subst σ s
sub-ctx-aux σ e (s ꞉ C[—] ↓) k (Id-refl _)=
  proof s' ꞉ subst σ (C[—] [ e /—])
    === s' ꞉ f (coe (Id-refl _) C[—]) [ r (coe (Id-refl _) e) /—]
      :by: ap (s' ꞉_) $ sub-ctx-aux σ e C[—] k (Id-refl _)
    === s' ꞉ (f C[—] [ r (coe (Id-refl _) e) /—])
      :by: ap (λ C → s' ꞉ f C [ r (coe (Id-refl _) e) /—]) $
           subrel {_P_ = _==_} $ coe-eval (Id-refl _) C[—]
    === f (coe (Id-refl _) (s ꞉ C[—] ↓)) [ r (coe (Id-refl _) e) /—]
      :by: ap (λ C → f C [ r (coe (Id-refl _) e) /—]) $
           subrel {_P_ = _==_} $ sym {R = Het._==_} $
           coe-eval (Id-refl _) (s ꞉ C[—] ↓)
  qed
  where f = sub-1-hole-ctx k σ (Id-refl _)(Id-refl _)
        r = subst (lift-by k σ)
        s' = subst σ s
sub-ctx-aux σ e (C[—] ↓꞉ S) k (Id-refl _)=
  proof subst σ (C[—] [ e /—]) ꞉ S'
    === f (coe (Id-refl _) C[—]) [ r (coe (Id-refl _) e) /—] ꞉ S'
      :by: ap (_꞉ S') $ sub-ctx-aux σ e C[—] k (Id-refl _)
    === f C[—] [ r (coe (Id-refl _) e) /—] ꞉ S'
      :by: ap (λ C → f C [ r (coe (Id-refl _) e) /—] ꞉ S') $
           subrel {_P_ = _==_} $ coe-eval (Id-refl _) C[—]
    === f (coe (Id-refl _) (C[—] ↓꞉ S)) [ r (coe (Id-refl _) e) /—]
      :by: ap (λ C → f C [ r (coe (Id-refl _) e) /—]) $
           subrel {_P_ = _==_} $ sym {R = Het._==_} $
           coe-eval (Id-refl _) (C[—] ↓꞉ S)
  qed
  where f = sub-1-hole-ctx k σ (Id-refl _)(Id-refl _)
        r = subst (lift-by k σ)
        S' = subst σ S

sub-ctx-prop : ∀ {k m n tag tag'}
  (σ : Sub m n)
  (e : expr-of-type tag (k + m))
  (C[—] : 1-hole-ctx tag (k + m) tag' m)
  → ----------------------------------------
  subst σ (C[—] [ e /—])
  ==
  sub ⦃ subst = SubstitutableContext ⦄ σ C[—] [ subst (lift-by k σ) e /—]
sub-ctx-prop {k} σ e C[—] =
  proof subst σ (C[—] [ e /—])
    === sub σ (coe (Id-refl _) C[—])
          [ subst (lift-by k σ) (coe (Id-refl _) e) /—]
      :by: sub-ctx-aux σ e C[—] k (Id-refl _)
    === sub σ C[—] [ subst (lift-by k σ) e /—]
      :by: subrel {_P_ = _==_} $
           ap2 (λ C e → sub σ C [ subst (lift-by k σ) e /—])
               (coe-eval (Id-refl _) C[—]) (coe-eval (Id-refl _) e)
  qed

-}
