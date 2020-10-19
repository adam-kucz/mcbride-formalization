{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Syntax.Context.Property.Substitutable
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax.Context.Arbitrary renaming ([_] to [[_]])

open import Type.Sum renaming (_,_ to _Σ,_; 〈_×_〉 to [_×_])
open import Data.Nat hiding (-comm)
open import Data.Maybe hiding (dmap)
open import Data.Tree.Binary hiding (dmap)
open import Function hiding (_$_)

open import Syntax
open import Renaming
open import Liftable
open import Substitution as Subs
  hiding (_[_/new])

private
  module Functor where
    import Data.Functor as F
    open import Data.Functor.Construction
    open import Data.Maybe.Functor
    open import Data.Tree.Binary.Functor

    open F.Functor
      (ComposeFunctor ⦃ BinaryTreeFunctor ⦄ ⦃ MaybeFunctor ⦄)
      public
open Functor

instance
  SubstitutableContext : ∀{t : Holes}{tag} →
    Substitutable (
      λ n → Context (fmap [ id × _+ n ] t) tag n)

open import Collection hiding (_-_; _~_)
open import Proof
open import Function.Proof

context-inhabited : ∀{tag n}{t : Holes}
  (C : Context t tag n)
  → --------------------------------------------------
  ∀{tag : ExprTag}{k : ℕ}(p : just (tag Σ, k) ∈ t) → n ≤ k
context-inhabited — (_ ∈leaf) = refl _
context-inhabited ([ π x: C₀ ]→ C₁) (_ ∈left p /\ r) =
  context-inhabited C₀ p
context-inhabited {n = n} ([ π x: C₀ ]→ C₁) {k = k} (_ ∈right l /\ p) =
  proof n
    〉 _≤_ 〉 n +1 :by: postfix suc n
    〉 _≤_ 〉 k    :by: context-inhabited C₁ p
  qed
context-inhabited {n = n} (λx, C) {k = k} p =
  proof n
    〉 _≤_ 〉 n +1 :by: postfix suc n
    〉 _≤_ 〉 k    :by: context-inhabited C p
  qed
context-inhabited ⌊ C ⌋ p = context-inhabited C p
context-inhabited (C₀ ` C₁) (_ ∈left p /\ r) = context-inhabited C₀ p
context-inhabited (C₀ ` C₁) (_ ∈right l /\ p) = context-inhabited C₁ p
context-inhabited (C₀ ꞉ C₁) (_ ∈left p /\ r) = context-inhabited C₀ p
context-inhabited (C₀ ꞉ C₁) (_ ∈right l /\ p) = context-inhabited C₁ p

open import Data.Nat.Arithmetic.Subtraction.Unsafe
open import Operation.Binary using (assoc; comm)
open import Logic

open import Axiom.FunctionExtensionality

module Auxiliary where
  f : ∀(m n : ℕ)
    (hole : ExprTag × ℕ)
    → -------------------------------
    ExprTag × ℕ
  f-id : ∀ m → f m m == id

  f m n = [ id × (λ l → n + l - m) ]

  f-id m = subrel $ fun-ext λ { (tag Σ, l) →
    subrel $ Σ== (Id.refl tag) (
      proof m + l - m
        === l + m - m :by: ap (_- m) $ comm m l [: _==_ ]
        het== l       :by: left-inverse-of (_+ m) l
      qed)}

open Auxiliary

open import Proposition.Identity.Coercion

sub-context : ∀{m n}
  (σ : Sub m n)
  {t : Holes}
  {tag}
  (C : Context t tag m)
  → ----------------------------------------
  Context (fmap (f m n) t) tag n
sub-context σ (term t) = term (sub σ t)
sub-context σ (elim e) = elim (sub σ e)
sub-context {m}{n} σ {tag = tag} — =
  coe (ap (λ k → Context [[ tag Σ, k ]] tag n)
          (sym $ subrel {sup = _==_} $ left-inverse-of (_+ m) n))
      —
sub-context σ ([ π x: C₀ ]→ C₁) =
  [ π x: sub-context σ C₀ ]→ sub-context (lift σ) C₁
sub-context σ (λx, C) = λx, sub-context (lift σ) C
sub-context σ ⌊ C ⌋ = ⌊ sub-context σ C ⌋
sub-context σ (C₀ ` C₁) = sub-context σ C₀ ` sub-context σ C₁
sub-context σ (C₀ ꞉ C₁) = sub-context σ C₀ ꞉ sub-context σ C₁

private
  fmap-aux : ∀ m n l
    (t : Holes)
    (p : ∀{tag : ExprTag}{k : ℕ}(q : just (tag Σ, k) ∈ t) → m ≤ k)
    → ------------------------------
    fmap (f n l) (fmap (f m n) t) == fmap (f m l) t
fmap-aux m n l ◻ p = Id.refl ◻
fmap-aux m n l [[ tag Σ, k ]] p = ap (λ x → [[ tag Σ, x ]]){r = _==_}(
  proof l + (n + k - m) - n
    === n + k - m + l - n
      :by: ap (_- n) $ comm l _
    === n + k - m [ p' ] + l - n
      :by: ap (λ — → — + l - n) $ unsafe-is-safe p'
    === n + k + l - m [ _ ] - n
      :by: ap (_- n) $ -+comm p'
    === n + k + l - m - n
      :by: ap (_- n) $ sym $ unsafe-is-safe {n + k + l}{m} _
    === l + k + n - m - n
      :by: ap (λ — → — - m - n){r = _==_}(
           proof n + k + l
             === k + n + l   :by: ap (_+ l) $ comm n k
             === l + (k + n) :by: comm (k + n) l
             === l + k + n   :by: assoc l k n
           qed)
    === l + k + n - n - m
      :by: -comm (l + k + n) m n
    === l + k - m
      :by: ap (_- m) $ subrel $
           left-inverse-of (_+ n) (l + k)
  qed)
  where p' : m ≤ n + k
        p' = proof m
               〉 _≤_ 〉 k     :by: p $ (just (tag Σ, k)) ∈leaf
               〉 _≤_ 〉 n + k :by: postfix (n +_) k
             qed
fmap-aux m n l (l' /\ r') p =
  ap2 _/\_ (fmap-aux m n l l' λ q → p $ _ ∈left q /\ r')
           (fmap-aux m n l r' λ q → p $ _ ∈right l' /\ q)

private
  fmap-f-id : ∀ m t
    → --------------------
    fmap (f m m) t == t

fmap-f-id m t =
  proof fmap (f m m) t
    === fmap id t      :by: ap (λ f → fmap f t) $ f-id m
    === t              :by: ap (λ f → f t) fmap-id
  qed

sub-context-id : ∀{m t tag}
  (C : Context t tag m)
  → ----------------------------------------
  sub-context var C Het.== C
sub-context-id (term t) = subrel $ ap (λ — → term (— t)) sub-id
sub-context-id (elim e) = subrel $ ap (λ — → elim (— e)) sub-id
sub-context-id {m}{t}{tag} — =
  coe-eval (ap (λ t → Context t tag m) (sym $ fmap-f-id m t)) —
sub-context-id {m}{l /\ r} ([ π x: C₀ ]→ C₁) =
  proof [ π x: sub-context var C₀ ]→ sub-context (lift var) C₁
    === [ π x: sub-context var C₀ ]→ sub-context var C₁
      :by: ap (λ — → [ π x: sub-context var C₀ ]→ sub-context — C₁) lift-var
    het== [ π x: sub-context var C₀ ]→ C₁
      :by: Id.ap2 {K = λ r _ → Context (_ /\ r) term m}
             (λ t (C : Context t term (m +1)) → [ π x: sub-context var C₀ ]→ C)
             (fmap-f-id m r)
             (sub-context-id C₁)
    het== [ π x: C₀ ]→ C₁
      :by: Id.ap2 {K = λ l _ → Context (l /\ _) term m}
             (λ t (C : Context t term m) → [ π x: C ]→ C₁)
             (fmap-f-id m l)
             (sub-context-id C₀)
  qed
sub-context-id {m}{t} (λx, C) =
  proof λx, sub-context (lift var) C
    === λx, sub-context var C
      :by: ap (λ — → λx, sub-context — C) lift-var [: _==_ ]
    het== λx, C
      :by: Id.ap2 {K = λ t _ → Context t term m}
                  (λ t (C : Context t term (m +1)) → λx, C)
                  (fmap-f-id m t)
                  (sub-context-id C)
  qed
sub-context-id {m}{t} ⌊ C ⌋ =
  Id.ap2 {K = λ t _ → Context t term m}
         (λ t (C : Context t elim m) → ⌊ C ⌋)
         (fmap-f-id m t)
         (sub-context-id C)
sub-context-id {m}{l /\ r} (C₀ ` C₁) =
  proof sub-context var C₀ ` sub-context var C₁
    het== sub-context var C₀ ` C₁
      :by: Id.ap2 {K = λ r _ → Context (_ /\ r) elim m}
             (λ t (C : Context t term m) → sub-context var C₀ ` C)
             (fmap-f-id m r)
             (sub-context-id C₁)
    het== C₀ ` C₁
      :by: Id.ap2 {K = λ l _ → Context (l /\ _) elim m}
             (λ t (C : Context t elim m) → C ` C₁)
             (fmap-f-id m l)
             (sub-context-id C₀)
  qed
sub-context-id {m}{l /\ r} (C₀ ꞉ C₁) =
  proof sub-context var C₀ ꞉ sub-context var C₁
    het== sub-context var C₀ ꞉ C₁
      :by: Id.ap2 {K = λ r _ → Context (_ /\ r) elim m}
             (λ t (C : Context t term m) → sub-context var C₀ ꞉ C)
             (fmap-f-id m r)
             (sub-context-id C₁)
    het== C₀ ꞉ C₁
      :by: Id.ap2 {K = λ l _ → Context (l /\ _) elim m}
             (λ t (C : Context t term m) → C ꞉ C₁)
             (fmap-f-id m l)
             (sub-context-id C₀)
  qed

sub-context-∘ : ∀{m n l}
  (σ : Sub n l)
  (τ : Sub m n)
  {t : Holes}{tag}
  (C : Context t tag m)
  → ----------------------------------------
  sub-context σ (sub-context τ C)
  Het.==
  sub-context (σ ⍟ τ) C
sub-context-∘ σ τ (term t) = subrel $ ap (λ — → term (— t)) $ sub-∘ σ τ
sub-context-∘ σ τ (elim e) = subrel $ ap (λ — → elim (— e)) $ sub-∘ σ τ
sub-context-∘ {m}{n}{l} σ τ {tag = tag} — =
  proof sub-context σ (coe (coer m n) —)
    het== coe (coer n l) —
      :by: Het.ap2 (λ k (C : Context [[ tag Σ, k ]] tag n) → sub-context σ C)
             (left-inverse-of (_+ m) n)
             (coe-eval (coer m n) —)
    het== —
      :by: coe-eval (coer n l) —
    het== coe (coer m l) —
      :by: isym $ coe-eval (coer m l) —
  qed
  where coer = λ m n →
          ap (λ k → Context [[ tag Σ, k ]] tag n){r = _==_}
             (sym $ subrel $ left-inverse-of (_+ m) n)
sub-context-∘ {m}{n}{l} σ τ {l' /\ r'} ([ π x: C₀ ]→ C₁) =
  proof [ π x: sub-context σ (sub-context τ C₀) ]→
               sub-context (lift σ) (sub-context (lift τ) C₁)
    het== [ π x: sub-context σ (sub-context τ C₀) ]→
                 sub-context (lift σ ⍟ lift τ) C₁
      :by: Id.ap2 {K = λ r _ → Context (_ /\ r) term l}
             (λ t (C : Context t term (l +1)) →
                [ π x: sub-context σ (sub-context τ C₀) ]→ C)
             (fmap-aux m n l r' $ context-inhabited (λx, C₁))
             (sub-context-∘ (lift σ) (lift τ) C₁)
    === [ π x: sub-context σ (sub-context τ C₀) ]→
               sub-context (lift (σ ⍟ τ)) C₁
      :by: ap (λ — →
             [ π x: sub-context σ (sub-context τ C₀) ]→ sub-context — C₁) $
           lift-⍟ σ τ
    het== [ π x: sub-context (σ ⍟ τ) C₀ ]→ sub-context (lift (σ ⍟ τ)) C₁
      :by: Id.ap2 {K = λ l' _ → Context (l' /\ _) term l}
             (λ t (C : Context t term l) →
                [ π x: C ]→ sub-context (lift (σ ⍟ τ)) C₁)
             (fmap-aux m n l l' $ context-inhabited C₀)
             (sub-context-∘ σ τ C₀)
  qed
sub-context-∘ {m}{n}{l} σ τ {t} (λx, C) =
  Id.ap2 {K = λ t _ → Context t term l}
         (λ t (C : Context t term (l +1)) → λx, C)
         (fmap-aux m n l t $ context-inhabited (λx, C))
         (proof sub-context (lift σ) (sub-context (lift τ) C)
            het== sub-context (lift σ ⍟ lift τ) C
              :by: sub-context-∘ (lift σ) (lift τ) C
            === sub-context (lift (σ ⍟ τ)) C
              :by: ap (λ — → sub-context — C) $ lift-⍟ σ τ
          qed)
sub-context-∘ {m}{n}{l} σ τ {t} ⌊ C ⌋ =
  Id.ap2 {K = λ t _ → Context t term l}
         (λ t (C : Context t elim l) → ⌊ C ⌋)
         (fmap-aux m n l t $ context-inhabited C)
         (sub-context-∘ σ τ C)
sub-context-∘ {m}{n}{l} σ τ {l' /\ r'} (C₀ ` C₁) =
  proof sub-context σ (sub-context τ C₀) `
        sub-context σ (sub-context τ C₁)
    het== sub-context σ (sub-context τ C₀) `
          sub-context (σ ⍟ τ) C₁
      :by: Id.ap2 {K = λ r _ → Context (_ /\ r) elim l}
             (λ t (C : Context t term l) → sub-context σ (sub-context τ C₀) ` C)
             (fmap-aux m n l r' $ context-inhabited C₁)
             (sub-context-∘ σ τ C₁)
    het== sub-context (σ ⍟ τ) C₀ `
          sub-context (σ ⍟ τ) C₁
      :by: Id.ap2 {K = λ l' _ → Context (l' /\ _) elim l}
             (λ t (C : Context t elim l) → C ` sub-context (σ ⍟ τ) C₁)
             (fmap-aux m n l l' $ context-inhabited C₀)
             (sub-context-∘ σ τ C₀)
  qed
sub-context-∘ {m}{n}{l} σ τ {l' /\ r'} (C₀ ꞉ C₁) =
  proof sub-context σ (sub-context τ C₀) ꞉
        sub-context σ (sub-context τ C₁)
    het== sub-context σ (sub-context τ C₀) ꞉
          sub-context (σ ⍟ τ) C₁
      :by: Id.ap2 {K = λ r _ → Context (_ /\ r) elim l}
             (λ t (C : Context t term l) → sub-context σ (sub-context τ C₀) ꞉ C)
             (fmap-aux m n l r' $ context-inhabited C₁)
             (sub-context-∘ σ τ C₁)
    het== sub-context (σ ⍟ τ) C₀ ꞉
          sub-context (σ ⍟ τ) C₁
      :by: Id.ap2 {K = λ l' _ → Context (l' /\ _) elim l}
             (λ t (C : Context t term l) → C ꞉ sub-context (σ ⍟ τ) C₁)
             (fmap-aux m n l l' $ context-inhabited C₀)
             (sub-context-∘ σ τ C₀)
  qed

SubstitutableContext {t}{tag} =
  DirectSubstitutable
    (λ {_}{n} σ C → coe (coer n C) (sub-context σ C))
    (λ {m} → subrel {sup = _==_} $ fun-ext λ C →
       proof coe (coer m C) (sub-context var C)
         het== sub-context var C :by: coe-eval (coer m C) (sub-context var C) 
         het== C                 :by: sub-context-id C
       qed)
    (λ {m}{n}{k} σ τ → subrel {sup = _==_} $ fun-ext λ C →
      let C' = coe (coer n C) (sub-context τ C) in
      proof coe (coer k C') (sub-context σ C')
        het== sub-context σ C'
          :by: coe-eval (coer k C') (sub-context σ C') 
        het== sub-context σ (sub-context τ C)
          :by: Het.ap2 {K = λ t _ → Context (fmap (f n k) t) tag k}
                 (λ _ C → sub-context σ C)
                 (sym go t)
                 (coe-eval (coer n C) (sub-context τ C))
        het== sub-context (σ ⍟ τ) C
          :by: sub-context-∘ σ τ C
        het== coe (coer k C) (sub-context (σ ⍟ τ) C)
          :by: isym $ coe-eval (coer k C) (sub-context (σ ⍟ τ) C)
      qed)
  where go : ∀{m n} →
          fmap (f m n) ∘ fmap [ id × _+ m ] ~ fmap [ id × _+ n ]
        go ◻ = Het.refl ◻
        go {m}{n} [[ tag Σ, k ]] =
          ap (λ — → [[ tag Σ, — ]]){r = Het._==_}(
          proof n + (k + m) - m
            === n + k + m - m   :by: ap (_- m) $ assoc n k m [: _==_ ]
            het== n + k         :by: left-inverse-of (_+ m) (n + k)
            === k + n           :by: comm n k
          qed)
        go (l /\ r) = ap2 _/\_ (go l) (go r)
        coer = λ {m} n (C : Context (fmap [ id × _+ m ] t) tag m) →
          ap (λ f → Context (f t) tag n) $ subrel $ fun-ext go
