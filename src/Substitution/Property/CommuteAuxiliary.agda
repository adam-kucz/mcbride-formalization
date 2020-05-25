{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import Basic using (Rig; wfs)
open import PropUniverses
open import Data.Nat hiding (l)

module Substitution.Property.CommuteAuxiliary
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Substitution.Basic
open import Substitution.Definition
open import Substitution.Syntax
open import Substitution.Property.NthVarAuxiliary

open import Proposition.Comparable
open import Relation.Binary hiding (_~_)
open import Function hiding (_$_)
open import Logic
open import Proof

open import Liftable
open import Renaming
open import Syntax

open import Proposition.Identity.Coercion
open import Axiom.FunctionExtensionality

open import Type.BinarySum hiding (_+_)

private
  aux-nthSub-inner :
    (x : X)(f : X → Y)(p : k < m +1)(v : Var (m +1))
    → --------------------------------------------------
    [ f + id ] (aux-nthSub x k p v)
    ==
    aux-nthSub (f x) k p v

aux-nthSub-inner {k = zero} x f p new = Id-refl (inl (f x))
aux-nthSub-inner {k = zero} x f p (old v) = Id-refl (inr (var v))
aux-nthSub-inner {k = k +1} {zero} x f p new =
  ⊥-recursion _ $ ¬-<0 k $ s<s→-<- p
aux-nthSub-inner {k = k +1} {m +1} x f p new = Id-refl (inr (var new))
aux-nthSub-inner {k = k +1} {m +1} x f p (old v) =
  subrel {_R_ = Het._==_} (
  proof [ f + id ] ([ id + shift ] e₀)
    het== [ f + shift ] e₀
      :by: [ f + id ]∘[ id + shift ] e₀
    het== [ id + shift ] ([ f + id ] e₀)
      :by: sym {R = Het._==_} $ [ id + shift ]∘[ f + id ] e₀
    === [ id + shift ] e₁
      :by: ap [ id + shift ] $ aux-nthSub-inner x f (s<s→-<- p) v
  qed)
  where e₀ = aux-nthSub x k (s<s→-<- p) v
        e₁ = aux-nthSub (f x) k (s<s→-<- p) v

lift-nthSub : ∀{k m}
  (f : Elim m)
  (p : k < m +1)
  → --------------------------------------------------
  lift (nthSub k p f)
  ==
  nthSub (k +1) (s<s p) (shift f)
lift-nthSub {k = k}{m} f p =
  subrel {_R_ = Het._==_} $ fun-ext
  λ { new → Het.refl (var new)
    ; (old v) →
        proof lift (nthSub k p f) (old v)
          === shift ([ id , id ] (aux-nthSub f k p v))
            :by: Id-refl _
          het== [ shift , shift ] (aux-nthSub f k p v)
            :by: (shift ∘[ id , id ]) (aux-nthSub f k p v)
          het== [ id , shift ] ([ shift + id ] (aux-nthSub f k p v))
            :by: sym {𝒰 = 𝒰 ⁺ ⊔ 𝒱}{𝒰 ⁺ ⊔ 𝒱} $
                 [ id , shift ]∘[ shift + id ] (aux-nthSub f k p v)
          === [ id , shift ] (aux-nthSub (shift f) k p v)
            :by: ap [ id , shift ] (aux-nthSub-inner f shift p v)
          het== [ id , id ] ([ id + shift ] (aux-nthSub (shift f) k p v))
            :by: sym {𝒰 = 𝒰 ⁺ ⊔ 𝒱}{𝒰 ⁺ ⊔ 𝒱} $
                 [ id , id ]∘[ id + shift ] (aux-nthSub (shift f) k p v)
          === nthSub (k +1) (s<s p) (shift f) (shift v)
            :by: Id-refl _
        qed}

open import Collection hiding (_~_)
open import Data.Functor
open import Data.Monad
open import Data.List as L hiding ([_]; index; _++_)
open import Data.List.Functor

private
  module Tag {tag : ExprTag} where
    open WithInstanceArgs ⦃ subst = SubstitutableExpr {tag = tag} ⦄ public

open Tag

nthSub-neutral : ∀ {k m}
  (f : Elim m)
  {tag}
  (e : expr-of-type tag (m +1))
  (p : k < m +1)
  (q : nth-var k p ∉ fv e)
  → --------------------------------------------------
  sub (nthSub k p f) e == del-nth k e p q
nthSub-neutral f {term} (⋆ i) p q = Id-refl (⋆ i)
nthSub-neutral {k} f {term} ([ ρ x: S ]→ T) p q =
  ap2 [ ρ x:_]→_
    (nthSub-neutral f S p λ q' → q $ ⟵ (++-prop {l' = l'}) $ ∨left q')
    (proof sub (lift (nthSub k p f)) T
       === sub (nthSub (k +1) (s<s p) (shift f)) T
         :by: ap (λ — → sub — T) $ lift-nthSub f p
       === del-nth (k +1) T (s<s p) q'
         :by: nthSub-neutral (shift f) T (s<s p) q'
     qed)
  where l' = fv T >>= prevSafe
        q' = λ q' → q $ ⟵ extend-prop $ ∨left $ del-nth-aux {p = p} q'
nthSub-neutral {k} f {term} (λx, t) p q =
  proof sub (nthSub k p f) (λx, t)
    === λx, sub (lift (nthSub k p f)) t
      :by: Id-refl _
    === λx, sub (nthSub (k +1) (s<s p) (shift f)) t
      :by: ap (λ — → λx, sub — t) $ lift-nthSub f p
    === λx, del-nth (k +1) t (s<s p) _
      :by: ap λx,_ $
           nthSub-neutral (shift f) t (s<s p)
           (λ q' → q $ del-nth-aux {n = k}{p} q')
    === del-nth k (λx, t) p q
      :by: Id-refl _
  qed
nthSub-neutral f {term} ⌊ e ⌋ p q = ap ⌊_⌋ $ nthSub-neutral f e p q
nthSub-neutral f {elim} (f' ` s) p q =
  ap2 _`_
    (nthSub-neutral f f' p λ q' → q $ ⟵ (++-prop {l' = fv s}) $ ∨left q')
    (nthSub-neutral f s p λ q' → q $ ⟵ (++-prop {l = fv f'}) $ ∨right q')
nthSub-neutral f {elim} (s ꞉ S) p q = 
  ap2 _꞉_
    (nthSub-neutral f s p λ q' → q $ ⟵ (++-prop {l' = fv S}) $ ∨left q')
    (nthSub-neutral f S p λ q' → q $ ⟵ (++-prop {l = fv s}) $ ∨right q')
nthSub-neutral {k} f {elim} (var v) p q =
  ap [ id , id ] $
  delVar-aux k v f p λ {(Id-refl _) → q $ x∈x∷ []}
  where delVar-aux : ∀ {m} k (v : Var (m +1)) (x : X) p q →
          aux-nthSub x k p v == inr (var (delVar k v p q))
        delVar-aux zero new _ p q = ⊥-recursion _ $ q $ Id-refl new
        delVar-aux zero (old v) _ p q = Id-refl (inr (var v))
        delVar-aux {m = zero}(k +1) new _ p q = ⊥-recursion _ $ ¬-<0 k $ s<s→-<- p
        delVar-aux {m = m +1}(k +1) new _ p q = Id-refl (inr (var new))
        delVar-aux {m = m +1}(k +1) (old v) x p q = 
          proof aux-nthSub x (k +1) p (old v)
            === [ id + shift ] (aux-nthSub x k (s<s→-<- p) v)
              :by: Id-refl _
            === [ id + shift ] (inr (var (delVar k v (s<s→-<- p) q')))
              :by: ap [ id + shift ] (delVar-aux k v x (s<s→-<- p) q')
            === inr (var (old (delVar k v _ _)))
              :by: Id-refl _
          qed
          where q' : nth-var k (s<s→-<- p) ≠ v
                q' nth-var==v = q $ ap old nth-var==v

sub-newSub :
  (σ : Sub m n)
  (f : Elim m)
  → ----------------------------------------------------------------------
  σ ⍟ newSub f == newSub (sub σ f) ⍟ lift σ
sub-newSub {m}{n} σ f = subrel {_R_ = Het._==_} $ fun-ext
  λ { new → Het.refl (sub σ f)
    ; (old v) →
      proof (σ ⍟ newSub f) (old v)
        het== σ v
          :by: Het.refl (σ v)
        === del-nth
              0
              (coe (Id-refl _) (rename (lift-by 0 old) (σ v)))
              (z<s _)
              (q v)
          :by: sym {R = _==_} $ del-k-shift~id 0 (σ v) (q v)
        === del-nth 0 (shift (σ v)) (z<s _) (nth-var∉shift 0 (σ v))
          :by: subrel {_P_ = _==_} $
               del-nth== (Id-refl elim)(Id-refl n)(Id-refl 0)
                 (proof coe (Id-refl _) (rename (lift-by 0 old) (σ v))
                    het== rename (lift-by 0 old) (σ v)
                      :by: coe-eval (Id-refl _) (rename (lift-by 0 old) (σ v))
                    het== shift (σ v)
                      :by: ==→~ ren-lift-0-old (σ v)
                  qed)
        === sub (newSub (sub σ f)) (shift (σ v))
          :by: sym {𝒰 = 𝒰 ⁺ ⊔ 𝒱} $
               nthSub-neutral (sub σ f) (shift (σ v)) (z<s n) _
        === (newSub (sub σ f) ⍟ lift σ) (old v)
          :by: Id-refl _
      qed}
  where e' : ∀ v → Elim (n +1)
        e' v = rename (lift-by 0 old) (σ v)
        ren-lift-0-old : ∀ {m : ℕ} →
          rename ⦃ r = RenameableElim ⦄ (lift-by {m = m} 0 old) == shift
        ren-lift-0-old =
          proof rename (lift-by 0 old)
            === rename (rename id ∘ old)
              :by: Id-refl _
            === shift
              :by: ap (λ — → rename (— ∘ old)) rename-id
          qed
        q : ∀ v → new ∉ fv (coe (Id-refl _) (e' v))
        q v p = nth-var∉shift 0 (σ v) $
          Id.coe (ap (λ — → new ∈ fv —) $
                  subrel {_P_ = _==_} $
                  coe-eval (Id-refl _) (e' v)) p

