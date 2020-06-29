{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Syntax.Context.Property.Relation
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax.Context.Arbitrary renaming ([_] to [[_]])

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
infix 180 _[_/new]

open import Type.Unit
open import Proposition.Sum
open import Proof

subst-as-fill-holes : ∀{tag}{m n}
  (σ : Sub m n)
  (t : expr-of-type tag m)
  → -------------------------
  Σₚ {X = Σ λ (t : Holes) → Context t tag n × all-types t}
     λ (_ Σ, (C Σ, es)) → fill-holes es C == subst σ t
subst-as-fill-holes {term} σ (⋆ i) =
  (◻ Σ, (term (⋆ i) Σ, ↑type ⋆)) , Id.refl _
subst-as-fill-holes {term} σ ([ π x: S ]→ T) =
  (t₀ /\ t₁ Σ, ([ π x: C₀ ]→ C₁ Σ, (es₀ Σ, es₁))) , ap2 [ π x:_]→_ p₀ p₁
  where c₀ = subst-as-fill-holes σ S
        p₀ = prop c₀
        t₀ = pr₁ (elem c₀)
        C₀ = pr₁ (pr₂ (elem c₀))
        es₀ = pr₂ (pr₂ (elem c₀))
        c₁ = subst-as-fill-holes (lift σ) T
        p₁ = prop c₁
        t₁ = pr₁ (elem c₁)
        C₁ = pr₁ (pr₂ (elem c₁))
        es₁ = pr₂ (pr₂ (elem c₁))
subst-as-fill-holes {term} σ (λx, t) = (h Σ, (λx, C Σ, es)) , ap λx,_ p
  where c = subst-as-fill-holes (lift σ) t
        p = prop c
        h = pr₁ (elem c)
        C = pr₁ (pr₂ (elem c))
        es = pr₂ (pr₂ (elem c))
subst-as-fill-holes {term} σ ⌊ e ⌋  = (t Σ, (⌊ C ⌋ Σ, es)) , ap ⌊_⌋ p
  where c = subst-as-fill-holes σ e
        p = prop c
        t = pr₁ (elem c)
        C = pr₁ (pr₂ (elem c))
        es = pr₂ (pr₂ (elem c))
subst-as-fill-holes {elim}{m}{n} σ (var v) =
  ([[ elim Σ, n ]] Σ, (— Σ, σ v)) , Id.refl _
subst-as-fill-holes {elim} σ (f ` s) =
  (t₀ /\ t₁ Σ, (C₀ ` C₁ Σ, (es₀ Σ, es₁))) , ap2 _`_ p₀ p₁
  where c₀ = subst-as-fill-holes σ f
        p₀ = prop c₀
        t₀ = pr₁ (elem c₀)
        C₀ = pr₁ (pr₂ (elem c₀))
        es₀ = pr₂ (pr₂ (elem c₀))
        c₁ = subst-as-fill-holes σ s
        p₁ = prop c₁
        t₁ = pr₁ (elem c₁)
        C₁ = pr₁ (pr₂ (elem c₁))
        es₁ = pr₂ (pr₂ (elem c₁))
subst-as-fill-holes {elim} σ (s ꞉ S) =
  (t₀ /\ t₁ Σ, (C₀ ꞉ C₁ Σ, (es₀ Σ, es₁))) , ap2 _꞉_ p₀ p₁
  where c₀ = subst-as-fill-holes σ s
        p₀ = prop c₀
        t₀ = pr₁ (elem c₀)
        C₀ = pr₁ (pr₂ (elem c₀))
        es₀ = pr₂ (pr₂ (elem c₀))
        c₁ = subst-as-fill-holes σ S
        p₁ = prop c₁
        t₁ = pr₁ (elem c₁)
        C₁ = pr₁ (pr₂ (elem c₁))
        es₁ = pr₂ (pr₂ (elem c₁))

holes-indep-of-sub : ∀{tag}{m n}
  (σ σ' : Sub m n)
  (t : expr-of-type tag m)
  → ----------------------------------------
  pr₁ (elem (subst-as-fill-holes σ t))
  ==
  pr₁ (elem (subst-as-fill-holes σ' t))
holes-indep-of-sub {term} σ σ' (⋆ i) = Id.refl _
holes-indep-of-sub {term} σ σ' ([ _ x: S ]→ T) =
  ap2 _/\_ (holes-indep-of-sub σ σ' S)(holes-indep-of-sub (lift σ)(lift σ') T)
holes-indep-of-sub {term} σ σ' (λx, t) =
  holes-indep-of-sub (lift σ) (lift σ') t
holes-indep-of-sub {term} σ σ' ⌊ e ⌋ = holes-indep-of-sub σ σ' e
holes-indep-of-sub {elim} σ σ' (var v) = Id.refl _
holes-indep-of-sub {elim} σ σ' (f ` s) =
  ap2 _/\_ (holes-indep-of-sub σ σ' f)(holes-indep-of-sub σ σ' s)
holes-indep-of-sub {elim} σ σ' (s ꞉ S) =
  ap2 _/\_ (holes-indep-of-sub σ σ' s)(holes-indep-of-sub σ σ' S)

open import Logic

ctx-indep-of-sub : ∀{tag}{m n}
  (σ σ' : Sub m n)
  (t : expr-of-type tag m)
  → ----------------------------------------
  pr₁ (pr₂ (elem (subst-as-fill-holes σ t)))
  Het.==
  pr₁ (pr₂ (elem (subst-as-fill-holes σ' t)))
ctx-indep-of-sub {term} σ σ' (⋆ i) = Het.refl _
ctx-indep-of-sub {term} σ σ' e@([ _ x: S ]→ T)
  with ctx-indep-of-sub σ σ' S | ctx-indep-of-sub (lift σ)(lift σ') T
... | q | q'
  with (_ Σ, (_ Σ, _)) , _ ← subst-as-fill-holes σ S
     | (_ Σ, (_ Σ, _)) , _ ← subst-as-fill-holes (lift σ) T
     | (_ Σ, (_ Σ, _)) , _ ← subst-as-fill-holes σ' S
     | (_ Σ, (_ Σ, _)) , _ ← subst-as-fill-holes (lift σ') T
     | Id.refl _ ← holes-indep-of-sub σ σ' e
     | Het.refl _ ← q | Het.refl _ ← q' = Het.refl _
ctx-indep-of-sub {term} σ σ' (λx, t) with ctx-indep-of-sub (lift σ)(lift σ') t
... | q with (_ Σ, (_ Σ, _)) , _ ← subst-as-fill-holes (lift σ) t
           | (_ Σ, (_ Σ, _)) , _ ← subst-as-fill-holes (lift σ') t
           | Id.refl _ ← holes-indep-of-sub (lift σ)(lift σ') t
           | Het.refl _ ← q = Het.refl _
ctx-indep-of-sub {term} σ σ' ⌊ e ⌋ with ctx-indep-of-sub σ σ' e
... | q with (_ Σ, (_ Σ, _)) , _ ← subst-as-fill-holes σ e
           | (_ Σ, (_ Σ, _)) , _ ← subst-as-fill-holes σ' e
           | Id.refl _ ← holes-indep-of-sub σ σ' e
           | Het.refl _ ← q = Het.refl _
ctx-indep-of-sub {elim} σ σ' (var v) = Het.refl _
ctx-indep-of-sub {elim}{m}{n} σ σ' e@(f ` s)
  with ctx-indep-of-sub σ σ' f | ctx-indep-of-sub σ σ' s
... | q | q'
  with (_ Σ, (_ Σ, _)) , _ ← subst-as-fill-holes σ f
     | (_ Σ, (_ Σ, _)) , _ ← subst-as-fill-holes σ s
     | (_ Σ, (_ Σ, _)) , _ ← subst-as-fill-holes σ' f
     | (_ Σ, (_ Σ, _)) , _ ← subst-as-fill-holes σ' s
     | Id.refl _ ← holes-indep-of-sub σ σ' e
     | Het.refl _ ← q | Het.refl _ ← q' = Het.refl _
ctx-indep-of-sub {elim} σ σ' e@(s ꞉ S)
  with ctx-indep-of-sub σ σ' s | ctx-indep-of-sub σ σ' S
... | q | q'
  with (_ Σ, (_ Σ, _)) , _ ← subst-as-fill-holes σ s
     | (_ Σ, (_ Σ, _)) , _ ← subst-as-fill-holes σ S
     | (_ Σ, (_ Σ, _)) , _ ← subst-as-fill-holes σ' s
     | (_ Σ, (_ Σ, _)) , _ ← subst-as-fill-holes σ' S
     | Id.refl _ ← holes-indep-of-sub σ σ' e
     | Het.refl _ ← q | Het.refl _ ← q' = Het.refl _

open import Renaming

open import Relation.Binary hiding (_~_)
open import Function.Proof

instance
  RelatingLiftPtwise :
    {Rel : RelOnExpr 𝒳}
    ⦃ refl-Rel : ∀{n} → Reflexive (Rel {n}{elim}) ⦄
    ⦃ Relating-rename-Rel :
        ∀{m n}{tag}{ρ : Ren m n}
        → ------------------------------
        Relating (rename ρ) (Rel {m}{tag})(Rel {n}{tag}) ⦄
    → ------------------------------------------------------------
    Relating (lift {m = m}{n}) (Pointwise Rel) (Pointwise Rel)

rel-preserv ⦃ RelatingLiftPtwise ⦄ rab new = refl (var new)
rel-preserv ⦃ RelatingLiftPtwise ⦄ rab (old v) = ap shift $ rab v

open import Proposition.Identity.Coercion

sub-relating-holes : ∀{tag}{m n}
  (Rel : RelOnExpr 𝒳)
  ⦃ refl-Rel : ∀{n tag} → Reflexive (Rel {n}{tag}) ⦄
  ⦃ Relating-rename-Rel : ∀{m n}{tag}{ρ : Ren m n}
      → --------------------------------------------
      Relating (rename ρ) (Rel {m}{tag})(Rel {n}{tag}) ⦄
  (σ σ' : Sub m n)
  (pt-Rel-e-e' : Pointwise Rel σ σ')
  (t : expr-of-type tag m)
  → ----------------------------------------
  let c = subst-as-fill-holes σ t
      c' = subst-as-fill-holes σ' t
      coer = ap all-types $ sym $ holes-indep-of-sub σ σ' t
  in
  all-related Rel (pr₁ (elem c))
    (pr₂ (pr₂ (elem c)))
    (coe coer (pr₂ (pr₂ (elem c'))))
sub-relating-holes {tag = term} _ _ _ p (⋆ i) = ↑prop ⋆ₚ
sub-relating-holes {tag = term} Rel σ σ' p e@([ _ x: S ]→ T) =
  Id.coe (ap (all-related Rel (pr₁ (elem c₀)) (pr₂ (pr₂ (elem c₀)))) $
          subrel {_R_ = Het._==_}{_P_ = _==_} (
          proof coe coer₀ (pr₂ (pr₂ (elem c₀')))
            het== pr₂ (pr₂ (elem c₀'))
              :by: coe-eval coer₀ (pr₂ (pr₂ (elem c₀')))
            het== pr₁ (pr₂ (pr₂ (elem c')))
              :by: Het.refl _
            het== pr₁ (coe coer (pr₂ (pr₂ (elem c'))))
              :by: Het.ap3 (λ X Y (σ : X × Y) → pr₁ σ)
                     coer₀ (subrel $ coer₁)
                     (isym $ coe-eval coer (pr₂ (pr₂ (elem c'))))
          qed)) $
  sub-relating-holes Rel σ σ' p S ,
  Id.coe (ap (all-related Rel (pr₁ (elem c₁)) (pr₂ (pr₂ (elem c₁)))) $
          subrel {_R_ = Het._==_}{_P_ = _==_} (
          proof coe coer₁ (pr₂ (pr₂ (elem c₁')))
            het== pr₂ (pr₂ (elem c₁'))
              :by: coe-eval coer₁ (pr₂ (pr₂ (elem c₁')))
            het== pr₂ (pr₂ (pr₂ (elem c')))
              :by: Het.refl _
            het== pr₂ (coe coer (pr₂ (pr₂ (elem c'))))
              :by: Het.ap3 (λ X Y (σ : X × Y) → pr₂ σ)
                     coer₀ (subrel $ coer₁)
                     (isym $ coe-eval coer (pr₂ (pr₂ (elem c'))))
          qed)) $
  sub-relating-holes Rel (lift σ)(lift σ')(ap lift p) T
  where c = subst-as-fill-holes σ e
        c' = subst-as-fill-holes σ' e
        coer = ap all-types $ sym $ holes-indep-of-sub σ σ' e
        c₀ = subst-as-fill-holes σ S
        c₀' = subst-as-fill-holes σ' S
        coer₀ = ap all-types $ sym $ holes-indep-of-sub σ σ' S
        c₁ = subst-as-fill-holes (lift σ) T
        c₁' = subst-as-fill-holes (lift σ') T
        coer₁ = ap all-types $ sym {R = _==_} $
                holes-indep-of-sub (lift σ)(lift σ') T
sub-relating-holes {tag = term} Rel σ σ' p (λx, t) =
  sub-relating-holes Rel (lift σ)(lift σ') (ap lift p) t
sub-relating-holes {tag = term} Rel σ σ' p ⌊ e ⌋ =
  sub-relating-holes Rel σ σ' p e
sub-relating-holes {tag = elim} Rel σ σ' p (var v) =
  Id.coe (ap (Rel (σ v)) $ sym $ coe-eval-hom (σ' v)) $ p v
sub-relating-holes {tag = elim} Rel σ σ' p e@(f ` s) =
  Id.coe (ap (all-related Rel (pr₁ (elem c₀)) (pr₂ (pr₂ (elem c₀)))) $
          subrel {_R_ = Het._==_}{_P_ = _==_} (
          proof coe coer₀ (pr₂ (pr₂ (elem c₀')))
            het== pr₂ (pr₂ (elem c₀'))
              :by: coe-eval coer₀ (pr₂ (pr₂ (elem c₀')))
            het== pr₁ (pr₂ (pr₂ (elem c')))
              :by: Het.refl _
            het== pr₁ (coe coer (pr₂ (pr₂ (elem c'))))
              :by: Het.ap3 (λ X Y (σ : X × Y) → pr₁ σ)
                     coer₀ (subrel $ coer₁)
                     (isym $ coe-eval coer (pr₂ (pr₂ (elem c'))))
          qed)) $
  sub-relating-holes Rel σ σ' p f ,
  Id.coe (ap (all-related Rel (pr₁ (elem c₁)) (pr₂ (pr₂ (elem c₁)))) $
          subrel {_R_ = Het._==_}{_P_ = _==_} (
          proof coe coer₁ (pr₂ (pr₂ (elem c₁')))
            het== pr₂ (pr₂ (elem c₁'))
              :by: coe-eval coer₁ (pr₂ (pr₂ (elem c₁')))
            het== pr₂ (pr₂ (pr₂ (elem c')))
              :by: Het.refl _
            het== pr₂ (coe coer (pr₂ (pr₂ (elem c'))))
              :by: Het.ap3 (λ X Y (σ : X × Y) → pr₂ σ)
                     coer₀ (subrel $ coer₁)
                     (isym $ coe-eval coer (pr₂ (pr₂ (elem c'))))
          qed)) $
  sub-relating-holes Rel σ σ' p s
  where c = subst-as-fill-holes σ e
        c' = subst-as-fill-holes σ' e
        coer = ap all-types $ sym $ holes-indep-of-sub σ σ' e
        c₀ = subst-as-fill-holes σ f
        c₀' = subst-as-fill-holes σ' f
        coer₀ = ap all-types $ sym $ holes-indep-of-sub σ σ' f
        c₁ = subst-as-fill-holes σ s
        c₁' = subst-as-fill-holes σ' s
        coer₁ = ap all-types $ sym $ holes-indep-of-sub σ σ' s
sub-relating-holes {tag = elim} Rel σ σ' p e@(s ꞉ S) =
  Id.coe (ap (all-related Rel (pr₁ (elem c₀)) (pr₂ (pr₂ (elem c₀)))) $
          subrel {_R_ = Het._==_}{_P_ = _==_} (
          proof coe coer₀ (pr₂ (pr₂ (elem c₀')))
            het== pr₂ (pr₂ (elem c₀'))
              :by: coe-eval coer₀ (pr₂ (pr₂ (elem c₀')))
            het== pr₁ (pr₂ (pr₂ (elem c')))
              :by: Het.refl _
            het== pr₁ (coe coer (pr₂ (pr₂ (elem c'))))
              :by: Het.ap3 (λ X Y (σ : X × Y) → pr₁ σ)
                     coer₀ (subrel $ coer₁)
                     (isym $ coe-eval coer (pr₂ (pr₂ (elem c'))))
          qed)) $
  sub-relating-holes Rel σ σ' p s ,
  Id.coe (ap (all-related Rel (pr₁ (elem c₁)) (pr₂ (pr₂ (elem c₁)))) $
          subrel {_R_ = Het._==_}{_P_ = _==_} (
          proof coe coer₁ (pr₂ (pr₂ (elem c₁')))
            het== pr₂ (pr₂ (elem c₁'))
              :by: coe-eval coer₁ (pr₂ (pr₂ (elem c₁')))
            het== pr₂ (pr₂ (pr₂ (elem c')))
              :by: Het.refl _
            het== pr₂ (coe coer (pr₂ (pr₂ (elem c'))))
              :by: Het.ap3 (λ X Y (σ : X × Y) → pr₂ σ)
                     coer₀ (subrel $ coer₁)
                     (isym $ coe-eval coer (pr₂ (pr₂ (elem c'))))
          qed)) $
  sub-relating-holes Rel σ σ' p S
  where c = subst-as-fill-holes σ e
        c' = subst-as-fill-holes σ' e
        coer = ap all-types $ sym $ holes-indep-of-sub σ σ' e
        c₀ = subst-as-fill-holes σ s
        c₀' = subst-as-fill-holes σ' s
        coer₀ = ap all-types $ sym $ holes-indep-of-sub σ σ' s
        c₁ = subst-as-fill-holes σ S
        c₁' = subst-as-fill-holes σ' S
        coer₁ = ap all-types $ sym $ holes-indep-of-sub σ σ' S

liftSub-refl : ∀{tag}{m n}
  {Rel : RelOnExpr 𝒳}
  ⦃ Rel-ctx-closed : ContextClosed Rel ⦄
  ⦃ Relating-rename-Rel : ∀{m n}{tag}{ρ : Ren m n}
      → --------------------------------------------
      Relating (rename ρ) (Rel {m}{tag})(Rel {n}{tag}) ⦄
  (σ σ' : Sub m n)
  (t : expr-of-type tag m)
  (pt-Rel-e-e' : Pointwise Rel σ σ')
  → ------------------------------
  Rel (subst σ t) (subst σ' t)
liftSub-refl {Rel = Rel} σ σ' t pt-Rel-e-e'
  with sub-relating-holes Rel ⦃ ReflexiveRel ⦄ σ σ' pt-Rel-e-e' t
  where ReflexiveRel : ∀{tag n} → Reflexive (Rel {n}{tag})
        refl ⦃ ReflexiveRel {term} ⦄ t = ctx-closed (term t) $ ↑prop ⋆ₚ
        refl ⦃ ReflexiveRel {elim} ⦄ e = ctx-closed (elim e) $ ↑prop ⋆ₚ
... | r with (t₀ Σ, (C₀ Σ, es₀)) , p₀ ← subst-as-fill-holes σ t
           | (t₁ Σ, (C₁ Σ, es₁)) , p₁ ← subst-as-fill-holes σ' t
           | Id.refl _ ← holes-indep-of-sub σ σ' t
           | Het.refl _ ← ctx-indep-of-sub σ σ' t =
  Id.coe (ap2 Rel p₀ p₁) $ ctx-closed C₀ $
  Id.coe (ap (all-related Rel t₀ es₀) $ coe-eval-hom es₁) r

-- RelatingContextClosed-sub : ∀{m n}{tag}
--   {Rel : RelOnExpr 𝒳}
--   ⦃ Rel-ctx-closed : ContextClosed Rel ⦄
--   {σ : Sub m n}
--   → ---------------------------
--   Relating (subst σ) (Rel {n = m}{tag}) (Rel {n = n}{tag})
-- rel-preserv ⦃ RelatingContextClosed-sub {Rel = Rel}{σ = σ} ⦄ {a}{b} rab
--   with (t₀ Σ, (C₀ Σ, es₀)) , p₀ ← subst-as-fill-holes σ a
--      | (t₁ Σ, (C₁ Σ, es₁)) , p₁ ← subst-as-fill-holes σ b =
--   Id.coe (ap2 Rel p₀ p₁) {!!}
