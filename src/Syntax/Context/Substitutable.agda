{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Syntax.Context.Substitutable
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
      λ n → Context (map [ id × _+ n ] v) tag n)

open import Collection hiding (_++_)

context-inhabited : ∀{tag m n}{v : Holes m}
  (C : Context v tag n)
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

context-inhabited-vec : ∀{tag m n}{v : Holes m}
  (C : Context v tag n)
  → --------------------------------------------------
  ∃ λ v' → v == map [ id × _+ n ] v'
context-inhabited-vec {m = m}{n}{v} C = go v (refl ⦃ Reflexive⊆ ⦄ v)
  where open import Collection.Property
        go : ∀{k}
          (v' : Holes k)
          (p : v' ⊆ v)
          → ----------------------------------
          ∃ λ v″ → v' == map [ id × _+ n ] v″
        go [] p = [] , Id-refl []
        go (h ∷ v') p with (go v' λ x q → p x $ x∈tail h q)
          | ⟶ ≤-↔-∃+ $ context-inhabited C h $ p h (x∈x∷ v')
        go ((tag Σ., .(l + n)) ∷ v') p | v″ , Id-refl _ | l , Id-refl _ =
          (tag Σ., l) ∷ v″ , Id-refl _

open import Operation.Binary

open import Axiom.FunctionExtensionality
open import Proposition.Identity.Coercion

module Auxiliary where
  f : ∀(n : ℕ)
    {m k}{v : Holes k}
    (q : ∀{hole : ExprTag × ℕ}(p : hole ∈ v) → m ≤ pr₂ hole)
    (hole : ExprTag × ℕ)
    (p : hole ∈ v)
    → -------------------------------
    ExprTag × ℕ
  f' : ∀(n : ℕ)
    {m k tag}{v : Holes k}
    (C : Context v tag m)
    (hole : ExprTag × ℕ)
    (p : hole ∈ v)
    → -------------------------------
    ExprTag × ℕ
  f-id : ∀{m k}
    {v : Holes k}
    (q : ∀{hole : ExprTag × ℕ}(p : hole ∈ v) → m ≤ pr₂ hole)
    → -------------------------------
    f m q == λ x _ → x


  f n {m} q hole@(tag Σ., l) p =
    tag Σ., n + l - m [ p' ]
    where p' : m ≤ n + l
          p' = proof m
                 〉 _≤_ 〉 l     :by: q p
                 〉 _≤_ 〉 n + l :by: postfix (n +_) l
               qed
  
  f' n C = f n (λ {hole} → context-inhabited C hole)

  f-id {m = m} _ =
    subrel $ fun-ext λ hole → fun-extₚ λ p →
    subrel $ Σ==
      (Id-refl _)
      (subrel (
       proof m + pr₂ hole - m [ _ ]
         === pr₂ hole :by: +==→-== $ comm m (pr₂ hole)
       qed))

open Auxiliary

sub-context : ∀{m n}
  (σ : Sub m n)
  {k}
  {v : Holes k}
  {tag}
  (C : Context v tag m)
  → ----------------------------------------
  Context (dmap v (f' n C)) tag n
sub-context σ (term t) = term (sub σ t)
sub-context σ (elim e) = elim (sub σ e)
sub-context {m}{n} σ {tag = tag} — =
  coe (ap (λ — → Context V.[ tag Σ., — ] tag n) $
       sym $ +==→-== $ Id-refl (n + m))
      —
sub-context {n = n} σ ([_x:_]→_ {v₀ = v₀}{v₁} π C₀ C₁) =
  coe (ap (λ — → Context — term n) p')
      ([ π x: sub-context σ C₀ ]→ sub-context (lift σ) C₁)
  where p' : dmap v₀ (f' n C₀) ++ dmap v₁ (f' (n +1) C₁)
             ==
             dmap (v₀ ++ v₁) (f' n ([ π x: C₀ ]→ C₁))
        p' = dmap++ v₀ v₁ (f' n ([ π x: C₀ ]→ C₁))
sub-context {n = n} σ (λx, C) =
  λx, sub-context (lift σ) C
sub-context σ ⌊ C ⌋ = ⌊ sub-context σ C ⌋
sub-context {n = n} σ (_`_ {v₀ = v₀}{v₁} C₀ C₁) =
  coe (ap (λ — → Context — elim n) p')
      (sub-context σ C₀ ` sub-context σ C₁)
  where p' : dmap v₀ (f' n C₀) ++ dmap v₁ (f' n C₁)
             ==
             dmap (v₀ ++ v₁) (f' n (C₀ ` C₁))
        p' = dmap++ v₀ v₁ (f' n (C₀ ` C₁))
sub-context {n = n} σ (_꞉_ {v₀ = v₀}{v₁} C₀ C₁) =
  coe (ap (λ — → Context — elim n) p')
      (sub-context σ C₀ ꞉ sub-context σ C₁)
  where p' : dmap v₀ (f' n C₀) ++ dmap v₁ (f' n C₁)
             ==
             dmap (v₀ ++ v₁) (f' n (C₀ ꞉ C₁))
        p' = dmap++ v₀ v₁ (f' n (C₀ ꞉ C₁))

sub-context-id : ∀{m k}
  {v : Holes k}
  {tag}
  (C : Context v tag m)
  → ----------------------------------------
  sub-context var C Het.== C
sub-context-id (term {m} t) =
  subrel {_R_ = _==_}{_P_ = Het._==_} $
  ap (λ — → term (— t)) sub-id
sub-context-id (elim e) =
  subrel {_R_ = _==_}{_P_ = Het._==_} $
  ap (λ — → elim (— e)) sub-id
sub-context-id {m}{tag = tag} — =
  coe-eval (ap (λ — → Context V.[ tag Σ., — ] tag m) $
            sym $ +==→-== $ Id-refl (m + m)) —
sub-context-id {m} ([_x:_]→_ {m₀ = m₀}{m₁}{v₀}{v₁} π C₀ C₁) =
  proof coe coer ([ π x: sub-context var C₀ ]→ sub-context (lift var) C₁)
    het== [ π x: sub-context var C₀ ]→ sub-context (lift var) C₁
      :by: coe-eval coer ([ π x: sub-context var C₀ ]→ sub-context (lift var) C₁)
    === [ π x: sub-context var C₀ ]→ sub-context var C₁
      :by: ap (λ — → [ π x: sub-context var C₀ ]→ sub-context — C₁) lift-var
    het== [ π x: C₀ ]→ sub-context var C₁
      :by: Id.ap2 {K = λ v C → Context (v ++ dmap v₁ (f' (m +1) C₁)) term m}
             (λ (v : Holes m₀)(C : Context v term m) → [ π x: C ]→ sub-context var C₁)
             (proof dmap v₀ (f' m C₀)
                === dmap v₀ (λ x _ → x)
                  :by: ap (dmap v₀) (f-id λ {hole} → context-inhabited C₀ hole)
                === v₀                  :by: dmap-id v₀
              qed)
             (sub-context-id C₀)
    het== [ π x: C₀ ]→ C₁
      :by: Id.ap2 {K = λ v C → Context (v₀ ++ v) term m}
             (λ (v : Holes m₁)(C : Context v term (m +1)) → [ π x: C₀ ]→ C)
             (proof dmap v₁ (f' (m +1) C₁)
                === dmap v₁ (λ x _ → x)
                  :by: ap (dmap v₁) (f-id λ {hole} → context-inhabited C₁ hole)
                === v₁                  :by: dmap-id v₁
              qed)
             (sub-context-id C₁)
  qed
  where coer = ap (λ — → Context — term m) $ dmap++ v₀ v₁ (f' m ([ π x: C₀ ]→ C₁))
sub-context-id {m}{k}{v} (λx, C) =
  Id.ap2 {K = λ v _ → Context v term m}
         (λ (v : Holes k)(C : Context v term (m +1)) → λx, C)
         (proof dmap v (f' m (λx, C))
            === dmap v (λ x _ → x)
              :by: ap (dmap v) (f-id λ {hole} → context-inhabited (λx, C) hole)
            === v                  :by: dmap-id v
          qed)
         (proof sub-context (lift var) C
           === sub-context var C :by: ap (λ — → sub-context — C) lift-var
           het== C               :by: sub-context-id C
         qed)
sub-context-id {m}{k}{v} ⌊ C ⌋ =
  Id.ap2 {K = λ v _ → Context v term m}
         (λ (v : Holes k)(C : Context v elim m) → ⌊ C ⌋)
         (proof dmap v (f' m C)
            === dmap v (λ x _ → x)
              :by: ap (dmap v) (f-id λ {hole} → context-inhabited C hole)
            === v                  :by: dmap-id v
          qed)
         (sub-context-id C)
sub-context-id {m} (_`_ {m₀ = m₀}{m₁}{v₀}{v₁} C₀ C₁) =
  proof coe coer (sub-context var C₀ ` sub-context var C₁)
    het== sub-context var C₀ ` sub-context var C₁
      :by: coe-eval coer (sub-context var C₀ ` sub-context var C₁)
    het== sub-context var C₀ ` C₁
      :by: Id.ap2 {K = λ v _ → Context (dmap v₀ (f' m C₀) ++ v) elim m}
             (λ (v : Holes m₁)(C : Context v term m) → sub-context var C₀ ` C)
             (proof dmap v₁ (f' m C₁)
                === dmap v₁ (λ x _ → x)
                  :by: ap (dmap v₁) (f-id λ {hole} → context-inhabited C₁ hole)
                === v₁                  :by: dmap-id v₁
              qed)
             (sub-context-id C₁)
    het== C₀ ` C₁
      :by: Id.ap2 {K = λ v _ → Context (v ++ v₁) elim m}
             (λ (v : Holes m₀)(C : Context v elim m) → C ` C₁)
             (proof dmap v₀ (f' m C₀)
                === dmap v₀ (λ x _ → x)
                  :by: ap (dmap v₀) (f-id λ {hole} → context-inhabited C₀ hole)
                === v₀                  :by: dmap-id v₀
              qed)
             (sub-context-id C₀)
  qed
  where coer = ap (λ — → Context — elim m) $ dmap++ v₀ v₁ (f' m (C₀ ` C₁))
sub-context-id {m} (_꞉_ {m₀ = m₀}{m₁}{v₀}{v₁} C₀ C₁) =
  proof coe coer (sub-context var C₀ ꞉ sub-context var C₁)
    het== sub-context var C₀ ꞉ sub-context var C₁
      :by: coe-eval coer (sub-context var C₀ ꞉ sub-context var C₁)
    het== sub-context var C₀ ꞉ C₁
      :by: Id.ap2 {K = λ v _ → Context (dmap v₀ (f' m C₀) ++ v) elim m}
             (λ (v : Holes m₁)(C : Context v term m) → sub-context var C₀ ꞉ C)
             (proof dmap v₁ (f' m C₁)
                === dmap v₁ (λ x _ → x)
                  :by: ap (dmap v₁) (f-id λ {hole} → context-inhabited C₁ hole)
                === v₁                  :by: dmap-id v₁
              qed)
             (sub-context-id C₁)
    het== C₀ ꞉ C₁
      :by: Id.ap2 {K = λ v _ → Context (v ++ v₁) elim m}
             (λ (v : Holes m₀)(C : Context v term m) → C ꞉ C₁)
             (proof dmap v₀ (f' m C₀)
                === dmap v₀ (λ x _ → x)
                  :by: ap (dmap v₀) (f-id λ {hole} → context-inhabited C₀ hole)
                === v₀                  :by: dmap-id v₀
              qed)
             (sub-context-id C₀)
  qed
  where coer = ap (λ — → Context — elim m) $ dmap++ v₀ v₁ (f' m (C₀ ꞉ C₁))

sub-context-∘ : ∀{m n l k}
  (σ : Sub n l)
  (τ : Sub m n)
  {v : Holes k}
  {tag}
  (C : Context v tag m)
  → ----------------------------------------
  sub-context σ (sub-context τ C)
  Het.==
  sub-context (σ ⍟ τ) C

open import Proposition.Proof hiding (id)

sub-dmap-∘ : ∀{m n l k}
  (σ : Sub n l)
  (τ : Sub m n)
  {v : Holes k}
  {tag}
  (C : Context v tag m)
  → ---------------------
  dmap (dmap v (f' n C)) (f' l (sub-context τ C))
  ==
  dmap v (f' l C)
sub-dmap-∘ {m}{n}{l} σ τ {v} C =
  proof dmap (dmap v (f' n C)) (f' l (sub-context τ C))
    === dmap v (λ x p → f' l (sub-context τ C) (f' n C x p) (∈dmap (f' n C) p))
      :by: dmap-∘ v (f' n C) (f' l (sub-context τ C))
    === dmap v (f' l C)
      :by: ap (dmap v) $ subrel $
           fun-ext (λ {(tag Σ., k) → fun-extₚ λ p → subrel {_R_ = _==_} $
           Σ== (Id-refl tag)
               (subrel (
                have l + (n + k - m [ _ ]) == l + k - m [ _ ] + n
                  :from: proof l + (n + k - m [ _ ])
                           === n + k - m [ _ ] + l
                             :by: comm l _
                           === n + k + l - m [ _ ]
                             :by: comm-+ {n + k}{m}{l} _
                           === l + k + n - m [ _ ]
                             :by: -== (
                               proof n + k + l
                                 === l + (n + k) :by: comm (n + k) l
                                 === l + (k + n) :by: ap (l +_) $ comm n k
                                 === l + k + n   :by: assoc l k n
                               qed) (Id-refl m)
                           === l + k - m [ _ ] + n
                             :by: sym $ comm-+ {l + k}{m}{n} _
                         qed
                ⟶ l + (n + k - m [ _ ]) - n [ _ ]
                   ==
                   l + k - m [ _ ]
                  :by: +==→-== {n = n}))})
  qed

sub-context-∘ σ τ (term t) = 
  subrel {_R_ = _==_}{_P_ = Het._==_} $
  ap (λ — → term (— t)) $ sub-∘ σ τ
sub-context-∘ σ τ (elim e) =
  subrel {_R_ = _==_}{_P_ = Het._==_} $
  ap (λ — → elim (— e)) $ sub-∘ σ τ
sub-context-∘ {m}{n}{l} σ τ {tag = tag} — =
  proof sub-context σ (coe (coer m n) —)
    het== sub-context σ —
      :by: Het.ap2
             (λ m (C : Context V.[ tag Σ., m ] tag n) → sub-context σ C)
             (subrel $ +==→-== $ Id-refl (n + m))
             (coe-eval (coer m n) —)
    het== —
      :by: coe-eval (coer n l) —
    het== coe (coer m l) —
      :by: isym $ coe-eval (coer m l) —
  qed
  where coer : (m n : ℕ) →
          Context V.[ tag Σ., n ] tag n
          ==
          Context V.[ tag Σ., n + m - m [ _ ] ] tag n
        coer m n = ap (λ — → Context V.[ tag Σ., — ] tag n) $
                   sym $ +==→-== $ Id-refl (n + m)
sub-context-∘ {m}{n}{l} σ τ ([_x:_]→_ {v₀ = v₀}{v₁} π C₀ C₁) =
  proof sub-context σ (coe (coer n) ([ π x: sub-context τ C₀ ]→
                                       sub-context (lift τ) C₁))
    het== sub-context σ ([ π x: sub-context τ C₀ ]→ sub-context (lift τ) C₁)
      :by: Id.ap2 (λ v C → sub-context σ {v = v} C)
             (sym $ p n)
             (coe-eval (coer n)
                ([ π x: sub-context τ C₀ ]→ sub-context (lift τ) C₁))
    === coe coer' e
      :by: Id-refl _
    het== e
      :by: coe-eval coer' e
    het== [ π x: sub-context (σ ⍟ τ) C₀ ]→
                 sub-context (lift σ) (sub-context (lift τ) C₁)
      :by: Id.ap2 {K = λ v _ → Context (v ++ _) term l}
             (λ v (C : Context v term l) →
               [ π x: C ]→ sub-context (lift σ) (sub-context (lift τ) C₁))
             (sub-dmap-∘ σ τ C₀)
             (sub-context-∘ σ τ C₀)
    het== [ π x: sub-context (σ ⍟ τ) C₀ ]→ sub-context (lift σ ⍟ lift τ) C₁
      :by: Id.ap2 {K = λ v _ → Context (_ ++ v) term l}
             (λ v (C : Context v term (l +1)) →
               [ π x: sub-context (σ ⍟ τ) C₀ ]→ C)
             (sub-dmap-∘ (lift σ) (lift τ) C₁)
             (sub-context-∘ (lift σ) (lift τ) C₁)
    === e'
      :by: ap (λ —₁ → [ π x: sub-context (σ ⍟ τ) C₀ ]→ sub-context —₁ C₁) $
           lift-⍟ σ τ
    het== coe (coer l) e'
      :by: isym $ coe-eval (coer l) e'
  qed
  where e = [ π x: sub-context σ (sub-context τ C₀) ]→
                   sub-context (lift σ) (sub-context (lift τ) C₁)
        e' = [ π x: sub-context (σ ⍟ τ) C₀ ]→ sub-context (lift (σ ⍟ τ)) C₁
        p : ∀ m →
          dmap v₀ (f' m C₀) ++ dmap v₁ (f' (m +1) C₁)
          ==
          dmap (v₀ ++ v₁) (f' m ([ π x: C₀ ]→ C₁))
        p m = dmap++ v₀ v₁ (f' m ([ π x: C₀ ]→ C₁))
        coer = λ m → ap (λ — → Context — term m) (p m)
        coer' = ap (λ — → Context — term l) (
          proof dmap (dmap v₀ (f' n C₀)) (f' l (sub-context τ C₀)) ++
                dmap (dmap v₁ (f' (n +1) C₁))
                     (f' (l +1) (sub-context (lift τ) C₁))
            === dmap (dmap v₀ (f' n C₀) ++ dmap v₁ (f' (n +1) C₁)) f″
              :by: dmap++ (dmap v₀ (f' n C₀)) (dmap v₁ (f' (n +1) C₁)) f″
          qed)
          where f″ = f' l ([ π x: sub-context τ C₀ ]→ sub-context (lift τ) C₁)
sub-context-∘ {l = l} σ τ (λx, C) =
  Id.ap2 {K = λ v _ → Context v term l}
    (λ v (C : Context v term (l +1)) → λx, C)
    (sub-dmap-∘ σ τ (λx, C))
    (proof sub-context (lift σ) (sub-context (lift τ) C)
       het== sub-context (lift σ ⍟ lift τ) C
         :by: sub-context-∘ (lift σ) (lift τ) C
       === sub-context (lift (σ ⍟ τ)) C
         :by: ap (λ — → sub-context — C) $ lift-⍟ σ τ
     qed)
sub-context-∘ {n = n}{l} σ τ {v} ⌊ C ⌋ =
  Id.ap2 {K = λ v _ → Context v term l}
    (λ v (C : Context v elim l) → ⌊ C ⌋)
    (sub-dmap-∘ σ τ C)
    (sub-context-∘ σ τ C)
sub-context-∘ {m}{n}{l} σ τ (_`_ {v₀ = v₀}{v₁} C₀ C₁) =
  proof sub-context σ (coe (coer n) (sub-context τ C₀ ` sub-context τ C₁))
    het== sub-context σ (sub-context τ C₀ ` sub-context τ C₁)
      :by: Id.ap2 (λ v C → sub-context σ {v = v} C)
             (sym $ p n)
             (coe-eval (coer n) (sub-context τ C₀ ` sub-context τ C₁))
    === coe coer' (sub-context σ (sub-context τ C₀) `
                   sub-context σ (sub-context τ C₁))
      :by: Id-refl _
    het== sub-context σ (sub-context τ C₀) ` sub-context σ (sub-context τ C₁)
      :by: coe-eval coer' (sub-context σ (sub-context τ C₀) `
                           sub-context σ (sub-context τ C₁))
    het== sub-context σ (sub-context τ C₀) ` sub-context (σ ⍟ τ) C₁
      :by: Id.ap2 {K = λ v _ → Context (_ ++ v) elim l}
             (λ v (C : Context v term l) → sub-context σ (sub-context τ C₀) ` C)
             (sub-dmap-∘ σ τ C₁)
             (sub-context-∘ σ τ C₁)
    het== sub-context (σ ⍟ τ) C₀ ` sub-context (σ ⍟ τ) C₁
      :by: Id.ap2 {K = λ v _ → Context (v ++ _) elim l}
             (λ v (C : Context v elim l) → C ` sub-context (σ ⍟ τ) C₁)
             (sub-dmap-∘ σ τ C₀)
             (sub-context-∘ σ τ C₀)
    het== coe (coer l) (sub-context (σ ⍟ τ) C₀ ` sub-context (σ ⍟ τ) C₁)
      :by: isym $
           coe-eval (coer l) (sub-context (σ ⍟ τ) C₀ ` sub-context (σ ⍟ τ) C₁)
  qed
  where p : ∀ m →
          dmap v₀ (f' m C₀) ++ dmap v₁ (f' m C₁)
          ==
          dmap (v₀ ++ v₁) (f' m (C₀ ` C₁))
        p m = dmap++ v₀ v₁ (f' m (C₀ ` C₁))
        coer = λ m → ap (λ — → Context — elim m) (p m)
        coer' = ap (λ — → Context — elim l) (
          proof dmap (dmap v₀ (f' n C₀)) (f' l (sub-context τ C₀)) ++
                dmap (dmap v₁ (f' n C₁)) (f' l (sub-context τ C₁))
            === dmap (dmap v₀ (f' n C₀) ++ dmap v₁ (f' n C₁)) f″
              :by: dmap++ (dmap v₀ (f' n C₀)) (dmap v₁ (f' n C₁)) f″
          qed)
          where f″ = f' l (sub-context τ C₀ ` sub-context τ C₁)
sub-context-∘ {m}{n}{l} σ τ (_꞉_ {v₀ = v₀}{v₁} C₀ C₁) =
  proof sub-context σ (coe (coer n) (sub-context τ C₀ ꞉ sub-context τ C₁))
    het== sub-context σ (sub-context τ C₀ ꞉ sub-context τ C₁)
      :by: Id.ap2 (λ v C → sub-context σ {v = v} C)
             (sym $ p n)
             (coe-eval (coer n) (sub-context τ C₀ ꞉ sub-context τ C₁))
    === coe coer' (sub-context σ (sub-context τ C₀) ꞉
                   sub-context σ (sub-context τ C₁))
      :by: Id-refl _
    het== sub-context σ (sub-context τ C₀) ꞉ sub-context σ (sub-context τ C₁)
      :by: coe-eval coer' (sub-context σ (sub-context τ C₀) ꞉
                           sub-context σ (sub-context τ C₁))
    het== sub-context σ (sub-context τ C₀) ꞉ sub-context (σ ⍟ τ) C₁
      :by: Id.ap2 {K = λ v _ → Context (_ ++ v) elim l}
             (λ v (C : Context v term l) → sub-context σ (sub-context τ C₀) ꞉ C)
             (sub-dmap-∘ σ τ C₁)
             (sub-context-∘ σ τ C₁)
    het== sub-context (σ ⍟ τ) C₀ ꞉ sub-context (σ ⍟ τ) C₁
      :by: Id.ap2 {K = λ v _ → Context (v ++ _) elim l}
             (λ v (C : Context v term l) → C ꞉ sub-context (σ ⍟ τ) C₁)
             (sub-dmap-∘ σ τ C₀)
             (sub-context-∘ σ τ C₀)
    het== coe (coer l) (sub-context (σ ⍟ τ) C₀ ꞉ sub-context (σ ⍟ τ) C₁)
      :by: isym $
           coe-eval (coer l) (sub-context (σ ⍟ τ) C₀ ꞉ sub-context (σ ⍟ τ) C₁)
  qed
  where p : ∀ m →
          dmap v₀ (f' m C₀) ++ dmap v₁ (f' m C₁)
          ==
          dmap (v₀ ++ v₁) (f' m (C₀ ꞉ C₁))
        p m = dmap++ v₀ v₁ (f' m (C₀ ꞉ C₁))
        coer = λ m → ap (λ — → Context — elim m) (p m)
        coer' = ap (λ — → Context — elim l) (
          proof dmap (dmap v₀ (f' n C₀)) (f' l (sub-context τ C₀)) ++
                dmap (dmap v₁ (f' n C₁)) (f' l (sub-context τ C₁))
            === dmap (dmap v₀ (f' n C₀) ++ dmap v₁ (f' n C₁)) f″
              :by: dmap++ (dmap v₀ (f' n C₀)) (dmap v₁ (f' n C₁)) f″
          qed)
          where f″ = f' l (sub-context τ C₀ ꞉ sub-context τ C₁)

dmap-map : ∀{k m} n
  (v : Holes k)
  → let v' = map [ id × _+ m ] v in
  (q : ∀{hole : ExprTag × ℕ}(p : hole ∈ v') → m ≤ pr₂ hole)
  → -------------------------------------------------------
  dmap v' (f n q)
  ==
  map [ id × _+ n ] v
dmap-map {m = m} n [] q = Id-refl []
dmap-map {m = m} n ((tag Σ., m') ∷ v) q = ap2 _∷_
  (Σ== (Id-refl tag) $ subrel $ +==→-== {n + (m' + m)}{m' + n}{m} (
     proof n + (m' + m)
       === n + m' + m :by: assoc n m' m
       === m' + n + m :by: ap (_+ m) $ comm n m'
     qed))
  (dmap-map n v (λ p → q (x∈tail _ p)))

SubstitutableContext {tag = tag}{v = v} =
  DirectSubstitutable
    (λ {_}{n} σ C → coe (coer n C) (sub-context σ C))
    (λ {m} → subrel {_P_ = _==_} $ fun-ext λ C → 
       proof coe (coer m C) (sub-context var C)
         het== sub-context var C
           :by: coe-eval (coer m C) (sub-context var C)
         het== C :by: sub-context-id C
       qed)
    λ {m}{n}{k} σ τ → subrel {_P_ = _==_} $ fun-ext λ C →
      let C' = coe (coer n C) (sub-context τ C) in
      proof coe (coer k C') (sub-context σ C')
        het== sub-context σ C'
          :by: coe-eval (coer k C') (sub-context σ C')
        het== sub-context σ (sub-context τ C )
          :by: Id.ap2 {K = λ v C → Context (dmap v (f' k C)) tag k}
                      (λ v C → sub-context σ C)
                      (sym $ dmap-map n v (λ {hole} → context-inhabited C hole))
                      (coe-eval (coer n C) (sub-context τ C))
        het== sub-context (σ ⍟ τ) C
          :by: sub-context-∘ σ τ C
        het== coe (coer k C) (sub-context (σ ⍟ τ) C)
          :by: isym $ coe-eval (coer k C) (sub-context (σ ⍟ τ) C)
      qed
  where coer = λ {m} n (C : Context (map [ id × _+ m ] v) tag m) →
          ap (λ — → Context — tag n)
             (dmap-map n v (λ {hole} → context-inhabited C hole))

