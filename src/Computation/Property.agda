{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic

module Computation.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Computation.Definition

open import Proposition.Identity hiding (refl)
open import Data.Nat
open import Syntax

sorts-don't-reduce : {i : S}{e e' : Term n}
  (p : e ⇝ e')
  → --------------------------------
  e ≠ ⋆ {n = n} i
sorts-don't-reduce (v-exact (v _ _)) ()
sorts-don't-reduce (hole — p) = sorts-don't-reduce p

open import Logic
open import Proof

pi-reduct-forms : ∀ {π : R}
  {e e' S : Term n}{T}
  (p : e ⇝ e')
  (q : e == [ π x: S ]→ T)
  → --------------------------------
  (∃ λ S' → S ⇝ S' ∧ e' == [ π x: S' ]→ T)
  ∨
  (∃ λ T' → T ⇝ T' ∧ e' == [ π x: S ]→ T')
pi-reduct-forms (v-exact (v _ _)) ()
pi-reduct-forms (hole — p) q = pi-reduct-forms p q
pi-reduct-forms (hole {s = s}{t} [ ρ x: S ]→ C[—] ↓ p)
  (Id-refl ([ ρ x: S ]→ .(C[—] [ s /—]))) =
  ∨right (C[—] [ t /—] , (hole C[—] p , Id-refl _))
pi-reduct-forms (hole {s = s} {t} ([ ρ x: C[—] ↓]→ T) p)
  (Id-refl ([ ρ x: .(C[—] [ s /—]) ]→ T)) =
  ∨left (C[—] [ t /—] , (hole C[—] p , Id-refl _))

open import Type.Sum hiding (_,_)
open import Relation.Binary.ReflexiveTransitiveClosure

pi-compute-forms : ∀ {π : R}
  {S : Term n}{T}{e'}
  (p : [ π x: S ]→ T ↠ e')
  → --------------------------------
  ∃ {X = Term n × Term (n +1)}
    (λ {(S' Σ., T') → S ↠ S' ∧ T ↠ T' ∧ e' == [ π x: S' ]→ T'})
pi-compute-forms (rfl ([ π x: S ]→ T)) =
  (S Σ., T) , (refl S , refl T , refl ([ π x: S ]→ T))
pi-compute-forms (step [πx:S]→T⇝e″ p)
  with pi-reduct-forms [πx:S]→T⇝e″ (Id-refl _)
pi-compute-forms (step [πx:S]→T⇝e″ p)
  | ∨left (S″ , (S⇝S″ , Id-refl _)) with pi-compute-forms p
pi-compute-forms (step [πx:S]→T⇝e″ p)
  | ∨left (S″ , (S⇝S″ , Id-refl _))
  | (S' Σ., T') , (S″↠S' , T↠T' , Id-refl _) =
  (S' Σ., T') , (step S⇝S″ S″↠S' , T↠T' , Id-refl _)
pi-compute-forms (step [πx:S]→T⇝e″ p)
  | ∨right (T″ , (T⇝T″ , Id-refl _)) with pi-compute-forms p
pi-compute-forms (step [πx:S]→T⇝e″ p)
  | ∨right (T″ , (T⇝T″ , Id-refl _))
  | (S' Σ., T') , (S↠S' , T″↠T' , Id-refl _) =
  (S' Σ., T') , (S↠S' , step T⇝T″ T″↠T' , Id-refl _)

mk-pi-compute : ∀ (π : R){S S' : Term n}{T T'}
  (p : S ↠ S')
  (q : T ↠ T')
  → ----------------
  [ π x: S ]→ T ↠ [ π x: S' ]→ T'
mk-pi-compute π (rfl S) q = ctx-closed q ([ π x: S ]→ — ↓)
mk-pi-compute π {T = T} (step S⇝S″ S″↠S') q =
  step (hole ([ π x: — ↓]→ T) S⇝S″) (mk-pi-compute π S″↠S' q)

open import Renaming
open import Liftable
open import Substitution as Subs
  hiding (_[_/new])
open import Computation.Proof

instance
  RenameableContext : ∀{tag₀ tag₁ n} →
    Renameable (λ m → 1-hole-ctx tag₀ (n + m) tag₁ m)

open import Data.Nat.Proof
open import Function.Proof

open import Proposition.Identity.Coercion

1-hole-ctx-inhabited : ∀{m n tag₀ tag₁}
  (C : 1-hole-ctx tag₀ m tag₁ n)
  → ----------------------------------------
  n ≤ m

1-hole-ctx-inhabited {m} — = refl m
1-hole-ctx-inhabited {m}{n} [ π x: S ]→ C ↓ =
  proof n
    〉 _≤_ 〉 n +1 :by: postfix suc n
    〉 _≤_ 〉 m    :by: 1-hole-ctx-inhabited C
  qed
1-hole-ctx-inhabited ([ ρ x: C ↓]→ T) = 1-hole-ctx-inhabited C
1-hole-ctx-inhabited {m}{n} (λx, C) =
  proof n
    〉 _≤_ 〉 n +1 :by: postfix suc n
    〉 _≤_ 〉 m    :by: 1-hole-ctx-inhabited C
  qed
1-hole-ctx-inhabited ⌊ C ⌋ = 1-hole-ctx-inhabited C
1-hole-ctx-inhabited (f ` C ↓) = 1-hole-ctx-inhabited C
1-hole-ctx-inhabited (C ↓` s) = 1-hole-ctx-inhabited C
1-hole-ctx-inhabited (s ꞉ C ↓) = 1-hole-ctx-inhabited C
1-hole-ctx-inhabited (C ↓꞉ S) = 1-hole-ctx-inhabited C

open import Proposition.Empty
  renaming (⊥-recursion to ⊥ₜ-recursion) using ()
open import Relation.Binary

ren-1-hole-ctx : ∀ k {m m' n n'}
  (ρ : Ren m n)
  (p : m' == k + m)
  (q : n' == k + n)
  {tag₀ tag₁}
  (C : 1-hole-ctx tag₀ m' tag₁ m)
  → ----------------------------------------
  1-hole-ctx tag₀ n' tag₁ n
ren-1-hole-ctx k ρ p q ([ π x: C ↓]→ T) =
  [ π x: ren-1-hole-ctx k ρ p q C ↓]→ rename (lift ρ) T
ren-1-hole-ctx k ρ p q ⌊ C ⌋ = ⌊ ren-1-hole-ctx k ρ p q C ⌋
ren-1-hole-ctx k ρ p q (f ` C ↓) = rename ρ f ` ren-1-hole-ctx k ρ p q C ↓
ren-1-hole-ctx k ρ p q (C ↓` s) = ren-1-hole-ctx k ρ p q C ↓` rename ρ s
ren-1-hole-ctx k ρ p q (s ꞉ C ↓) = rename ρ s ꞉ ren-1-hole-ctx k ρ p q C ↓
ren-1-hole-ctx k ρ p q (C ↓꞉ S) = ren-1-hole-ctx k ρ p q C ↓꞉ rename ρ S
ren-1-hole-ctx zero {n' = n'} ρ p q {tag} — =
  coe (ap (1-hole-ctx tag n' tag) q) —
ren-1-hole-ctx (k +1) {m} ρ p q — = ⊥ₜ-recursion _ (irrefl m (
  proof m
    〉 _≤_ 〉 k + m    :by: postfix (k +_) m
    〉 _<_ 〉 k + m +1 :by: postfix suc (k + m) 
    === m           :by: sym p
  qed))
ren-1-hole-ctx zero {m}{m'} ρ p q (λx, C) = ⊥ₜ-recursion _ (irrefl (m +1) (
  proof m +1
    〉 _≤_ 〉 m'   :by: 1-hole-ctx-inhabited C
    〉 _==_ 〉 m   :by: p
    〉 _<_ 〉 m +1 :by: postfix suc m
  qed))
ren-1-hole-ctx (k +1) {m}{_}{n} ρ p q (λx, C) =
  λx, ren-1-hole-ctx k (lift ρ)
        (trans p (sym $ +-suc k m))
        (trans q (sym $ +-suc k n)) C
ren-1-hole-ctx zero {m}{m'} ρ p q [ π x: S ]→ C ↓ =
  ⊥ₜ-recursion _ (irrefl (m +1) (
    proof m +1
      〉 _≤_ 〉 m'   :by: 1-hole-ctx-inhabited C
      〉 _==_ 〉 m   :by: p
      〉 _<_ 〉 m +1 :by: postfix suc m
    qed))
ren-1-hole-ctx (k +1) {m}{_}{n} ρ p q [ π x: S ]→ C ↓ =
  [ π x: rename ρ S ]→
    ren-1-hole-ctx k (lift ρ)
      (trans p (sym $ +-suc k m))
      (trans q (sym $ +-suc k n)) C ↓

ren-1-hole-ctx== :
  ∀{k₀ k₁ m₀ m₁ m'₀ m'₁ n₀ n₁ n'₀ n'₁ tag₀ tag₁ tag'₀ tag'₁}
  {ρ₀ : Ren m₀ n₀}
  {ρ₁ : Ren m₁ n₁}
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
  (eq₅ : ρ₀ Het.== ρ₁)
  (eq₆ : C₀ Het.== C₁)
  → ----------------------------------------
  ren-1-hole-ctx k₀ ρ₀ p₀ q₀ C₀
  Het.==
  ren-1-hole-ctx k₁ ρ₁ p₁ q₁ C₁
ren-1-hole-ctx== (Id-refl _)(Id-refl _)(Id-refl _)(Id-refl _)
  (Id-refl _)(Id-refl _)(Id-refl _)(Id-refl _)(Id-refl _)
  (Het.refl _)(Het.refl _) = Het.refl _

open import Function hiding (_$_)

ren-1-hole-ctx-id : ∀ k {m m' tag₀ tag₁}
  (p : m' == k + m)
  (C : 1-hole-ctx tag₀ m' tag₁ m)
  → ----------------------------------------
  ren-1-hole-ctx k id p p C Het.== C

ren-1-hole-ctx-id k p ([ ρ x: C ↓]→ T) =
  ap2 [ ρ x:_↓]→_
    (ren-1-hole-ctx-id k p C)
    (proof rename (lift id) T
       === rename id T :by: ap (λ — → rename — T) lift-id==id
       het== T         :by: ==→~ rename-id T
     qed)
ren-1-hole-ctx-id k p ⌊ C ⌋ = ap ⌊_⌋ $ ren-1-hole-ctx-id k p C
ren-1-hole-ctx-id k p (f ` C ↓) =
  ap2 _`_↓ (subrel {_P_ = Het._==_} $ ap (λ — → — f) rename-id)
           (ren-1-hole-ctx-id k p C)
ren-1-hole-ctx-id k p (C ↓` s) =
  ap2 _↓`_ (ren-1-hole-ctx-id k p C)
           (subrel {_P_ = Het._==_} $ ap (λ — → — s) rename-id)
ren-1-hole-ctx-id k p (s ꞉ C ↓) =
  ap2 _꞉_↓ (subrel {_P_ = Het._==_} $ ap (λ — → — s) rename-id)
           (ren-1-hole-ctx-id k p C)
ren-1-hole-ctx-id k p (C ↓꞉ S) =
  ap2 _↓꞉_ (ren-1-hole-ctx-id k p C)
           (subrel {_P_ = Het._==_} $ ap (λ — → — S) rename-id)
ren-1-hole-ctx-id zero {m}{m'} p (λx, C) =
  ⊥-recursion _ $ irrefl (m +1) (
  proof m +1
    〉 _≤_ 〉 m'   :by: 1-hole-ctx-inhabited C
    〉 _==_ 〉 m   :by: p
    〉 _<_ 〉 m +1 :by: postfix suc m
  qed)
ren-1-hole-ctx-id (k +1){m}{m'} p (λx, C) =
  proof ren-1-hole-ctx (k +1) id p p (λx, C)
    === λx, ren-1-hole-ctx k (lift id) _ _ C
      :by: Id-refl _
    === λx, ren-1-hole-ctx k id _ _ C
      :by: ap (λ — → λx, ren-1-hole-ctx k — p' p' C) lift-id==id
    het== λx, C
      :by: ap λx,_ $ ren-1-hole-ctx-id k p' C
  qed
  where p' = proof m'
               === k + m +1   :by: p
               === k + (m +1) :by: sym (+-suc k m)
             qed
ren-1-hole-ctx-id zero {m}{m'} p [ ρ x: S ]→ C ↓ =
  ⊥-recursion _ $ irrefl (m +1) (
  proof m +1
    〉 _≤_ 〉 m'   :by: 1-hole-ctx-inhabited C
    〉 _==_ 〉 m   :by: p
    〉 _<_ 〉 m +1 :by: postfix suc m
  qed)
ren-1-hole-ctx-id (k +1){m}{m'} p [ π x: S ]→ C ↓ =
  proof ren-1-hole-ctx (k +1) id p p ([ π x: S ]→ C ↓)
    === [ π x: rename id S ]→ ren-1-hole-ctx k (lift id) _ _ C ↓
      :by: Id-refl _
    === [ π x: S ]→ ren-1-hole-ctx k id _ _ C ↓
      :by: ap2 (λ S ρ → [ π x: S ]→ ren-1-hole-ctx k ρ p' p' C ↓)
               (ap (λ — → — S) rename-id)
               lift-id==id
    het== [ π x: S ]→ C ↓
      :by: ap [ π x: S ]→_↓ $ ren-1-hole-ctx-id k p' C
  qed
  where p' = proof m'
               === k + m +1   :by: p
               === k + (m +1) :by: sym (+-suc k m)
             qed
ren-1-hole-ctx-id zero {m' = m'}{tag} p — =
  coe-eval (ap (1-hole-ctx tag m' tag) p) —
ren-1-hole-ctx-id (k +1) {m} p — = ⊥-recursion _ $ irrefl m (
  proof m
    〉 _≤_ 〉 k + m    :by: postfix (k +_) m
    〉 _<_ 〉 k + m +1 :by: postfix suc (k + m) 
    === m           :by: sym p
  qed)

ren-1-hole-ctx-∘ : ∀ k {m m' n n' l l' tag₀ tag₁}
  (π : Ren n l)
  (ρ : Ren m n)
  (pm : m' == k + m)
  (pn : n' == k + n)
  (pl : l' == k + l)
  (C : 1-hole-ctx tag₀ m' tag₁ m)
  → ----------------------------------------
  ren-1-hole-ctx k (π ∘ ρ) pm pl C
  Het.==
  ren-1-hole-ctx k π pn pl (ren-1-hole-ctx k ρ pm pn C)

ren-1-hole-ctx-∘ k π ρ pm pn pl ([ δ x: C ↓]→ T) =
  ap2 [ δ x:_↓]→_
    (ren-1-hole-ctx-∘ k π ρ pm pn pl C)
    (proof rename (lift (π ∘ ρ)) T
       === rename (lift π ∘ lift ρ) T
         :by: ap (λ — → rename — T) $ lift-∘ π ρ
       het== rename (lift π) (rename (lift ρ) T)
         :by: ==→~ (rename-∘ (lift π) (lift ρ)) T
     qed)
ren-1-hole-ctx-∘ k π ρ pm pn pl ⌊ C ⌋ =
  ap ⌊_⌋ $ ren-1-hole-ctx-∘ k π ρ pm pn pl C
ren-1-hole-ctx-∘ k π ρ pm pn pl (f ` C ↓) =
  ap2 _`_↓ (==→~ (rename-∘ π ρ) f )
           (ren-1-hole-ctx-∘ k π ρ pm pn pl C)
ren-1-hole-ctx-∘ k π ρ pm pn pl (C ↓` s) =
  ap2 _↓`_ (ren-1-hole-ctx-∘ k π ρ pm pn pl C)
           (==→~ (rename-∘ π ρ) s)
ren-1-hole-ctx-∘ k π ρ pm pn pl (s ꞉ C ↓) =
  ap2 _꞉_↓ (==→~ (rename-∘ π ρ) s)
           (ren-1-hole-ctx-∘ k π ρ pm pn pl C)
ren-1-hole-ctx-∘ k π ρ pm pn pl (C ↓꞉ S) =
  ap2 _↓꞉_ (ren-1-hole-ctx-∘ k π ρ pm pn pl C)
           (==→~ (rename-∘ π ρ) S)
ren-1-hole-ctx-∘ zero π ρ (Id-refl _)(Id-refl _)(Id-refl _) — =
  proof coe (Id-refl _) —
    het== —
      :by: coe-eval (Id-refl _) —
    het== ren-1-hole-ctx zero π (Id-refl _)(Id-refl _) —
      :by: sym {R = Het._==_} $ coe-eval (Id-refl _) —
    het== ren-1-hole-ctx zero π _ _ (coe (Id-refl _) —)
      :by: ap (ren-1-hole-ctx zero π _ _) $ sym {R = Het._==_} $
           coe-eval (Id-refl _) —
  qed
ren-1-hole-ctx-∘ (k +1) {m} π ρ pm pn pl — =
  ⊥-recursion _ $ irrefl m (
  proof m
    〉 _≤_ 〉 k + m    :by: postfix (k +_) m
    〉 _<_ 〉 k + m +1 :by: postfix suc (k + m) 
    === m           :by: sym pm
  qed)
ren-1-hole-ctx-∘ zero {m}{m'} π ρ pm pn pl [ δ x: S ]→ C ↓ =
  ⊥-recursion _ $ irrefl (m +1) (
  proof m +1
    〉 _≤_ 〉 m'   :by: 1-hole-ctx-inhabited C
    〉 _==_ 〉 m   :by: pm
    〉 _<_ 〉 m +1 :by: postfix suc m
  qed)
ren-1-hole-ctx-∘ (k +1) {m}{_}{n}{_}{l} π ρ pm pn pl [ δ x: S ]→ C ↓ =
  proof [ δ x: rename (π ∘ ρ) S ]→ ren-1-hole-ctx k (lift (π ∘ ρ)) pm' pl' C ↓
    === [ δ x: rename π (rename ρ S) ]→
          ren-1-hole-ctx k (lift π ∘ lift ρ) pm' pl' C ↓
      :by: ap2 (λ renS ρ' → [ δ x: renS S ]→ ren-1-hole-ctx k ρ' pm' pl' C ↓)
             (rename-∘ π ρ) (lift-∘ π ρ)
    het== [ δ x: rename π (rename ρ S) ]→
            ren-1-hole-ctx k (lift π) pn' pl' (
              ren-1-hole-ctx k (lift ρ) pm' pn' C) ↓
      :by: ap (λ — → [ δ x: rename π (rename ρ S) ]→ — ↓) $
           ren-1-hole-ctx-∘ k (lift π) (lift ρ) pm' pn' pl' C
  qed
  where pm' = trans pm (sym $ +-suc k m)
        pn' = trans pn (sym $ +-suc k n)
        pl' = trans pl (sym $ +-suc k l)
ren-1-hole-ctx-∘ zero {m}{m'} π ρ pm pn pl (λx, C) =
  ⊥-recursion _ $ irrefl (m +1) (
  proof m +1
    〉 _≤_ 〉 m'   :by: 1-hole-ctx-inhabited C
    〉 _==_ 〉 m   :by: pm
    〉 _<_ 〉 m +1 :by: postfix suc m
  qed)
ren-1-hole-ctx-∘ (k +1) {m}{_}{n}{_}{l} π ρ pm pn pl (λx, C) =
  proof λx, ren-1-hole-ctx k (lift (π ∘ ρ)) pm' pl' C
    === λx, ren-1-hole-ctx k (lift π ∘ lift ρ) pm' pl' C
      :by: ap (λ — → λx, ren-1-hole-ctx k — pm' pl' C) $ lift-∘ π ρ
    het== λx, ren-1-hole-ctx k (lift π) pn' pl' (
              ren-1-hole-ctx k (lift ρ) pm' pn' C)
      :by: ap λx,_ $ ren-1-hole-ctx-∘ k (lift π) (lift ρ) pm' pn' pl' C
  qed
  where pm' = trans pm (sym $ +-suc k m)
        pn' = trans pn (sym $ +-suc k n)
        pl' = trans pl (sym $ +-suc k l)

open import Axiom.FunctionExtensionality

rename ⦃ RenameableContext {n = n} ⦄ ρ C[—] =
  ren-1-hole-ctx n ρ (Id-refl _) (Id-refl _) C[—]
rename-id ⦃ RenameableContext {n = n} ⦄ {m} =
  subrel {_P_ = _==_} $ fun-ext $ ren-1-hole-ctx-id n (Id-refl (n + m))
rename-∘ ⦃ RenameableContext {n = n} ⦄ π ρ =
  subrel {_P_ = _==_} $ fun-ext $
  ren-1-hole-ctx-∘ n π ρ (Id-refl _)(Id-refl _)(Id-refl _)

private
  ren = λ {tag}{m}{n} → rename ⦃ r = RenameableExpr {tag = tag} ⦄ {m = m}{n}
  _[_/new] = Subs._[_/new] ⦃ subst = SubstitutableElim ⦄
infix 180 _[_/new]

open import Function.Coercion

rename-ctx-aux : ∀{l m n tag tag'}
  (ρ : Ren m n)
  (e : expr-of-type tag l)
  (C[—] : 1-hole-ctx tag l tag' m)
  (k : ℕ)
  (p : l == k + m)
  → ----------------------------------------
  ren ρ (C[—] [ e /—])
  ==
  rename ⦃ r = RenameableContext ⦄ ρ
      (coe (ap (λ —₁ → 1-hole-ctx tag —₁ tag' m) p) C[—])
    [ ren (lift-by k ρ) (coe (ap (expr-of-type tag) p) e) /—]

rename-ctx-aux ρ e — zero (Id-refl l) =
  proof ren ρ e
    === ren-1-hole-ctx zero ρ (Id-refl _)(Id-refl _) — [ ren ρ e /—]
      :by: ap (λ — → — [ ren ρ e /—]) $
           sym {R = _==_} $ subrel {_P_ = _==_} $
           coe-eval (Id-refl _) —
    === ren-1-hole-ctx zero ρ _ _ (coe (Id-refl _) —)
          [ ren ρ (coe (Id-refl _) e) /—]
      :by: sym {R = _==_} $ subrel {_P_ = _==_} $
           ap2 (λ C e → ren-1-hole-ctx zero ρ (Id-refl _)(Id-refl _) C
                          [ ren ρ e /—])
               (coe-eval (Id-refl _) —)
               (coe-eval (Id-refl _) e)
  qed
rename-ctx-aux {l} ρ e — (k +1) p =
  ⊥-recursion _ $ irrefl l (
  proof l
    〉 _≤_ 〉 k + l    :by: postfix (k +_) l
    〉 _<_ 〉 k + l +1 :by: postfix suc (k + l)
    === l           :by: sym p
  qed)
rename-ctx-aux ρ e (λx, C[—]) zero (Id-refl m) =
  ⊥-recursion _ $ irrefl (m +1) (
  proof m +1
    〉 _≤_ 〉 m    :by: 1-hole-ctx-inhabited C[—]
    〉 _<_ 〉 m +1 :by: postfix suc m
  qed)
rename-ctx-aux {_}{m}{n}{tag} ρ e (λx, C[—])(k +1)(Id-refl _) =
  proof ren ρ (λx, C[—] [ e /—])
    === λx, ren (lift ρ) (C[—] [ e /—])
      :by: Id-refl _
    === λx, ren-1-hole-ctx k (lift ρ)(Id-refl _)(Id-refl _)(
              coe (ap (λ — → 1-hole-ctx tag — term (m +1)) p') C[—])
            [ e' /—]
      :by: ap λx,_ $ rename-ctx-aux (lift ρ) e C[—] k p'
    === λx, ren-1-hole-ctx k (lift ρ) p' (sym $ +-suc k n)
                (coe (Id-refl _) C[—])
              [ e″ /—]
      :by: subrel {_P_ = _==_} $
           Het.ap3 (λ i (C : 1-hole-ctx tag i term (n +1))
                        (e : expr-of-type tag i) → λx, C [ e /—])
             (+-suc k n)
             transform-C
             transform-e
    === ren-1-hole-ctx (k +1) ρ (Id-refl _)(Id-refl _)
            (coe (Id-refl _) (λx, C[—]))
          [ e″ /—]
      :by: ap (λ — → ren-1-hole-ctx (k +1) ρ (Id-refl _) (Id-refl _) — [ e″ /—])
             move-coe
  qed
  where p' = sym $ +-suc k m
        e' = ren (lift-by k (lift ρ)) (coe (ap (expr-of-type tag) p') e)
        e″ = ren (lift-by (k +1) ρ) (coe (Id-refl _) e)
        transform-C :
          ren-1-hole-ctx k (lift ρ)(Id-refl _)(Id-refl _)(
            coe (ap (λ — → 1-hole-ctx tag — term (m +1)) p') C[—])
          Het.==
          ren-1-hole-ctx k (lift ρ) p' (sym $ +-suc k n) (
            coe (Id-refl _) C[—])
        transform-C =
          proof ren-1-hole-ctx k (lift ρ)(Id-refl _)(Id-refl _)
                  (coe (ap (λ — → 1-hole-ctx tag — term (m +1)) p') C[—])
            het== ren-1-hole-ctx k (lift ρ) p' (sym $ +-suc k n) C[—]
              :by: ren-1-hole-ctx==
                    (Id-refl _)(Id-refl _) p' (sym $ +-suc k n)
                    (Id-refl k)(Id-refl (m +1))(Id-refl (n +1))
                    (Id-refl term)(Id-refl tag)
                    (Het.refl (lift ρ))
                    (coe-eval (ap (λ — → 1-hole-ctx tag — term (m +1)) p') C[—])
            het== ren-1-hole-ctx k (lift ρ) p' (sym $ +-suc k n)
                    (coe (Id-refl _) C[—])
              :by: ap (ren-1-hole-ctx k (lift ρ) p' (sym $ +-suc k n)) $
                   sym {R = Het._==_} $
                   coe-eval (Id-refl _) C[—]
          qed
        transform-e : e' Het.== e″
        transform-e = 
          proof ren (lift-by k (lift ρ)) (coe (ap (expr-of-type tag) p') e)
            het== ren (lift-by k (lift ρ) ∘ coe (ap Var $ sym $ +-suc k m))
                      (coe (Id-refl _) e)
              :by: Het.ap3 (λ i (ρ : Ren i (k + (n +1)))
                                (e : expr-of-type tag i) → ren ρ e)
                     (+-suc k m)
                     (isym $ ∘-coe (ap Var $ sym $ +-suc k m)
                                   (lift-by k (lift ρ)))
                     (proof coe (ap (expr-of-type tag) p') e
                        het== e
                          :by: coe-eval (ap (expr-of-type tag) p') e
                        het== (coe (Id-refl _) e)
                          :by: isym $ coe-eval (Id-refl _) e
                      qed)
            het== ren (lift-by (k +1) ρ) (coe (Id-refl _) e)
              :by: Id.ap2 (λ i (ρ : Ren (k + m +1) i) →
                               ren {n = i} ρ (coe (Id-refl _) e))
                          (+-suc k n)
                          (isym $ fun-ext $ lift-by-lift~ k ρ)
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
rename-ctx-aux ρ e [ π x: S ]→ C[—] ↓ zero (Id-refl m) =
  ⊥-recursion _ $ irrefl (m +1) (
  proof m +1
    〉 _≤_ 〉 m    :by: 1-hole-ctx-inhabited C[—]
    〉 _<_ 〉 m +1 :by: postfix suc m
  qed)
rename-ctx-aux {_}{m}{n}{tag} ρ e [ π x: S ]→ C[—] ↓ (k +1)(Id-refl _) =
  proof ren ρ ([ π x: S ]→ C[—] [ e /—])
    === [ π x: ren ρ S ]→ ren (lift ρ) (C[—] [ e /—])
      :by: Id-refl _
    === [ π x: ren ρ S ]→
          (ren-1-hole-ctx k (lift ρ) (Id-refl _)(Id-refl _)
            (coe (ap (λ — → 1-hole-ctx tag — term (m +1)) p') C[—]) [ e' /—])
      :by: ap [ π x: ren ρ S ]→_ $
           rename-ctx-aux (lift ρ) e C[—] k p'
    === [ π x: ren ρ S ]→
          ren-1-hole-ctx k (lift ρ) p' (sym $ +-suc k n)
            (coe (Id-refl _) C[—]) [ e″ /—]
      :by: subrel {_P_ = _==_} $
           Het.ap3 (λ i (C : 1-hole-ctx tag i term (n +1))
                        (e : expr-of-type tag i) → [ π x: ren ρ S ]→ C [ e /—])
             (+-suc k n)
             transform-C
             transform-e
    === ren-1-hole-ctx (k +1) ρ (Id-refl _)(Id-refl _)(
            coe (Id-refl _) [ π x: S ]→ C[—] ↓) [ e″ /—]
      :by: ap (λ — → ren-1-hole-ctx (k +1) ρ (Id-refl _)(Id-refl _) — [ e″ /—])
           move-coe
  qed
  where p' = sym $ +-suc k m
        e' = ren (lift-by k (lift ρ)) (coe (ap (expr-of-type tag) p') e)
        e″ = ren (lift-by (k +1) ρ) (coe (Id-refl _) e)
        transform-C :
          ren-1-hole-ctx k (lift ρ)(Id-refl _)(Id-refl _)(
            coe (ap (λ — → 1-hole-ctx tag — term (m +1)) p') C[—])
          Het.==
          ren-1-hole-ctx k (lift ρ) p' (sym $ +-suc k n) (
            coe (Id-refl _) C[—])
        transform-C =
          proof ren-1-hole-ctx k (lift ρ)(Id-refl _)(Id-refl _)
                  (coe (ap (λ — → 1-hole-ctx tag — term (m +1)) p') C[—])
            het== ren-1-hole-ctx k (lift ρ) p' (sym $ +-suc k n) C[—]
              :by: ren-1-hole-ctx==
                    (Id-refl _)(Id-refl _) p' (sym $ +-suc k n)
                    (Id-refl k)(Id-refl (m +1))(Id-refl (n +1))
                    (Id-refl term)(Id-refl tag)
                    (Het.refl (lift ρ))
                    (coe-eval (ap (λ — → 1-hole-ctx tag — term (m +1)) p') C[—])
            het== ren-1-hole-ctx k (lift ρ) p' (sym $ +-suc k n)
                    (coe (Id-refl _) C[—])
              :by: ap (ren-1-hole-ctx k (lift ρ) p' (sym $ +-suc k n)) $
                   sym {R = Het._==_} $
                   coe-eval (Id-refl _) C[—]
          qed
        transform-e : e' Het.== e″
        transform-e = 
          proof ren (lift-by k (lift ρ)) (coe (ap (expr-of-type tag) p') e)
            het== ren (lift-by k (lift ρ) ∘ coe (ap Var $ sym $ +-suc k m))
                      (coe (Id-refl _) e)
              :by: Het.ap3 (λ i (ρ : Ren i (k + (n +1)))
                                (e : expr-of-type tag i) → ren ρ e)
                     (+-suc k m)
                     (isym $ ∘-coe (ap Var $ sym $ +-suc k m)
                                   (lift-by k (lift ρ)))
                     (proof coe (ap (expr-of-type tag) p') e
                        het== e
                          :by: coe-eval (ap (expr-of-type tag) p') e
                        het== (coe (Id-refl _) e)
                          :by: isym $ coe-eval (Id-refl _) e
                      qed)
            het== ren (lift-by (k +1) ρ) (coe (Id-refl _) e)
              :by: Id.ap2 (λ i (ρ : Ren (k + m +1) i) →
                               ren {n = i} ρ (coe (Id-refl _) e))
                          (+-suc k n)
                          (isym $ fun-ext $ lift-by-lift~ k ρ)
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
rename-ctx-aux ρ e ([ π x: C[—] ↓]→ T) k (Id-refl _) =
  proof [ π x: ren ρ (C[—] [ e /—]) ]→ T'
    === [ π x: f (coe (Id-refl _) C[—]) [ r (coe (Id-refl _) e) /—] ]→ T'
      :by: ap ([ π x:_]→ T') $ rename-ctx-aux ρ e C[—] k (Id-refl _)
    === [ π x: f C[—] [ r (coe (Id-refl _) e) /—] ]→ T'
      :by: ap (λ C → [ π x: f C [ r (coe (Id-refl _) e) /—] ]→ T') $
           subrel {_P_ = _==_} $ coe-eval (Id-refl _) C[—]
    === f (coe (Id-refl _) ([ π x: C[—] ↓]→ T)) [ r (coe (Id-refl _) e) /—]
      :by: ap (λ C → f C [ r (coe (Id-refl _) e) /—]) $
           subrel {_P_ = _==_} $ sym {R = Het._==_} $
           coe-eval (Id-refl _) ([ π x: C[—] ↓]→ T)
  qed
  where f = ren-1-hole-ctx k ρ (Id-refl _)(Id-refl _)
        r = ren (lift-by k ρ)
        T' = ren (lift ρ) T
rename-ctx-aux ρ e ⌊ C[—] ⌋ k (Id-refl _) =
  proof ⌊ ren ρ  (C[—] [ e /—]) ⌋
    === ⌊ f (coe (Id-refl _) C[—]) [ r (coe (Id-refl _) e) /—] ⌋
      :by: ap ⌊_⌋ $ rename-ctx-aux ρ e C[—] k (Id-refl _)
    === ⌊ f C[—] [ r (coe (Id-refl _) e) /—] ⌋
      :by: ap (λ C → ⌊ f C [ r (coe (Id-refl _) e) /—] ⌋) $
           subrel {_P_ = _==_} $ coe-eval (Id-refl _) C[—]
    === f (coe (Id-refl _) ⌊ C[—] ⌋) [ r (coe (Id-refl _) e) /—]
      :by: ap (λ C → f C [ r (coe (Id-refl _) e) /—]) $
           subrel {_P_ = _==_} $ sym $
           coe-eval (Id-refl _) ⌊ C[—] ⌋
  qed
  where f = ren-1-hole-ctx k ρ (Id-refl _)(Id-refl _)
        r = ren (lift-by k ρ)
rename-ctx-aux ρ e (f″ ` C[—] ↓) k (Id-refl _) =
  proof f' ` ren ρ (C[—] [ e /—])
    === f' ` f (coe (Id-refl _) C[—]) [ r (coe (Id-refl _) e) /—]
      :by: ap (f' `_) $ rename-ctx-aux ρ e C[—] k (Id-refl _)
    === f' ` (f C[—] [ r (coe (Id-refl _) e) /—])
      :by: ap (λ C → f' ` f C [ r (coe (Id-refl _) e) /—]) $
           subrel {_P_ = _==_} $ coe-eval (Id-refl _) C[—]
    === f (coe (Id-refl _) (f″ ` C[—] ↓)) [ r (coe (Id-refl _) e) /—]
      :by: ap (λ C → f C [ r (coe (Id-refl _) e) /—]) $
           subrel {_P_ = _==_} $ sym {R = Het._==_} $
           coe-eval (Id-refl _) (f″ ` C[—] ↓)
  qed
  where f = ren-1-hole-ctx k ρ (Id-refl _)(Id-refl _)
        r = ren (lift-by k ρ)
        f' = ren ρ f″
rename-ctx-aux ρ e (C[—] ↓` s) k (Id-refl _) =
  proof ren ρ (C[—] [ e /—]) ` s'
    === f (coe (Id-refl _) C[—]) [ r (coe (Id-refl _) e) /—] ` s'
      :by: ap (_` s') $ rename-ctx-aux ρ e C[—] k (Id-refl _)
    === f C[—] [ r (coe (Id-refl _) e) /—] ` s'
      :by: ap (λ C → f C [ r (coe (Id-refl _) e) /—] ` s') $
           subrel {_P_ = _==_} $ coe-eval (Id-refl _) C[—]
    === f (coe (Id-refl _) (C[—] ↓` s)) [ r (coe (Id-refl _) e) /—]
      :by: ap (λ C → f C [ r (coe (Id-refl _) e) /—]) $
           subrel {_P_ = _==_} $ sym {R = Het._==_} $
           coe-eval (Id-refl _) (C[—] ↓` s)
  qed
  where f = ren-1-hole-ctx k ρ (Id-refl _)(Id-refl _)
        r = ren (lift-by k ρ)
        s' = ren ρ s
rename-ctx-aux ρ e (s ꞉ C[—] ↓) k (Id-refl _)=
  proof s' ꞉ ren ρ (C[—] [ e /—])
    === s' ꞉ f (coe (Id-refl _) C[—]) [ r (coe (Id-refl _) e) /—]
      :by: ap (s' ꞉_) $ rename-ctx-aux ρ e C[—] k (Id-refl _)
    === s' ꞉ (f C[—] [ r (coe (Id-refl _) e) /—])
      :by: ap (λ C → s' ꞉ f C [ r (coe (Id-refl _) e) /—]) $
           subrel {_P_ = _==_} $ coe-eval (Id-refl _) C[—]
    === f (coe (Id-refl _) (s ꞉ C[—] ↓)) [ r (coe (Id-refl _) e) /—]
      :by: ap (λ C → f C [ r (coe (Id-refl _) e) /—]) $
           subrel {_P_ = _==_} $ sym {R = Het._==_} $
           coe-eval (Id-refl _) (s ꞉ C[—] ↓)
  qed
  where f = ren-1-hole-ctx k ρ (Id-refl _)(Id-refl _)
        r = ren (lift-by k ρ)
        s' = ren ρ s
rename-ctx-aux ρ e (C[—] ↓꞉ S) k (Id-refl _)=
  proof ren ρ (C[—] [ e /—]) ꞉ S'
    === f (coe (Id-refl _) C[—]) [ r (coe (Id-refl _) e) /—] ꞉ S'
      :by: ap (_꞉ S') $ rename-ctx-aux ρ e C[—] k (Id-refl _)
    === f C[—] [ r (coe (Id-refl _) e) /—] ꞉ S'
      :by: ap (λ C → f C [ r (coe (Id-refl _) e) /—] ꞉ S') $
           subrel {_P_ = _==_} $ coe-eval (Id-refl _) C[—]
    === f (coe (Id-refl _) (C[—] ↓꞉ S)) [ r (coe (Id-refl _) e) /—]
      :by: ap (λ C → f C [ r (coe (Id-refl _) e) /—]) $
           subrel {_P_ = _==_} $ sym {R = Het._==_} $
           coe-eval (Id-refl _) (C[—] ↓꞉ S)
  qed
  where f = ren-1-hole-ctx k ρ (Id-refl _)(Id-refl _)
        r = ren (lift-by k ρ)
        S' = ren ρ S

rename-ctx : ∀ {k m n tag tag'}
  (ρ : Ren m n)
  (e : expr-of-type tag (k + m))
  (C[—] : 1-hole-ctx tag (k + m) tag' m)
  → ----------------------------------------
  ren ρ (C[—] [ e /—])
  ==
  rename ⦃ r = RenameableContext ⦄ ρ C[—] [ ren (lift-by k ρ) e /—]
rename-ctx {k} ρ e C[—] =
  proof ren ρ (C[—] [ e /—])
    === rename ρ (coe (Id-refl _) C[—])
          [ ren (lift-by k ρ) (coe (Id-refl _) e) /—]
      :by: rename-ctx-aux ρ e C[—] k (Id-refl _)
    === rename ρ C[—] [ ren (lift-by k ρ) e /—]
      :by: subrel {_P_ = _==_} $
           ap2 (λ C e → rename ρ C [ ren (lift-by k ρ) e /—])
               (coe-eval (Id-refl _) C[—]) (coe-eval (Id-refl _) e)
  qed

rename-compute : ∀{m n tag}
  (ρ : Ren m n)
  {e e' : expr-of-type tag m}
  (p : e ⇝ e')
  → ------------------------------
  ren ρ e ⇝ ren ρ e'
rename-compute ρ (β-exact (β π s S t T)) =
  proof (λx, ren (lift ρ) t ꞉ [ π x: ren ρ S ]→ ren (lift ρ) T) ` ren ρ s
    〉 _⇝_ 〉 (ren (lift ρ) (t ꞉ T)) [ ren ρ (s ꞉ S) /new]
      :by: β-exact (β π (ren ρ s) (ren ρ S) (ren (lift ρ) t) (ren (lift ρ) T))
    === ren ρ ((t ꞉ T) [ s ꞉ S /new])
      :by: sym {R = _==_} $ rename-[-/new] ρ (t ꞉ T) (s ꞉ S)
  qed
rename-compute ρ (v-exact (v t T)) = v-exact (v (ren ρ t) (ren ρ T))
rename-compute ρ (hole C[—] p) with ⟶ ≤-↔-∃+ $ 1-hole-ctx-inhabited C[—]
rename-compute {m}{n} ρ (hole {m'}{n'}{tag₀}{tag₁}{s}{t} C[—] p) | k , q =
  proof ren ρ (C[—] [ s /—])
    === C' [ s' /—]
      :by: rename-ctx-aux ρ s C[—] k (sym q)
    === C' [ s″ /—]
      :by: ap (C' [_/—]) $ move-coe s
    〉 _⇝_ 〉 C' [ t″ /—]
      :by: hole C' $ rename-compute ρ' p
    === C' [ t' /—]
      :by: sym {R = _==_} $ ap (C' [_/—]) $ move-coe t
    === ren ρ (C[—] [ t /—])
      :by: sym {R = _==_} $ rename-ctx-aux ρ t C[—] k (sym q)
  qed
  where C' = rename ρ (coe (ap (λ — → 1-hole-ctx tag₀ — tag₁ m) $ sym q) C[—])
        s' t' s″ t″ : expr-of-type tag₀ (k + n)
        coer = ap (expr-of-type tag₀) $ sym q
        s' = ren (lift-by k ρ) (coe coer s)
        t' = ren (lift-by k ρ) (coe coer t)
        ρ-coer = ap (λ —₁ → Var —₁ → Var (k + n)) q
        ρ' = coe ρ-coer (lift-by k ρ)
        s″ = ren ρ' s
        t″ = ren ρ' t
        move-coe :
          (e : expr-of-type tag₀ m')
          → ----------------------------------------
          ren (lift-by k ρ) (coe coer e) == ren ρ' e
        move-coe e =
          subrel {_P_ = _==_} $
          Het.ap3 (λ i (ρ : Ren i (k + n))(e : expr-of-type tag₀ i) → ren ρ e)
                  q
                  (isym $ coe-eval ρ-coer (lift-by k ρ) )
                  (coe-eval coer e)

instance
  RelatingRename⇝ : ∀{m n tag}{ρ : Ren m n} →
    Relating (ren {tag} ρ) _⇝_ _⇝_

rel-preserv ⦃ RelatingRename⇝ {ρ = ρ} ⦄ = rename-compute ρ

