{-# OPTIONS --exact-split --prop #-}
open import Basic
open import PropUniverses

module Subtyping.Stability
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Subtyping.Definition
open import Subtyping.Property
open import Subtyping.Proof

-- Lemma 21 (subtyping stability)

open import Syntax
open import Renaming
open import Substitution using (nthSub; lift-nth)
private
  module Tag {tag : ExprTag} where
    open import Substitution
    open WithInstanceArgs ⦃ subst = SubstitutableExpr {tag = tag} ⦄ public
open Tag
open import Liftable

open import Type.BinarySum renaming (_+_ to _⊹_)
open import Data.Nat hiding (_⊔_)
open import Relation.Binary hiding (_~_)
open import Relation.Binary.Pointwise
open import Function hiding (_$_; _~_)
open import Logic
open import Proof
open import Function.Proof

open import Axiom.FunctionExtensionality

≼-stable : (r R R' : Term m)
  (q : n ≤ m)
  {S T : expr-of-type tag (m +1)}
  (p : S ≼ T)
  → ---------------
  S [ r ꞉ R / n [ q ]] ≼ T [ r ꞉ R' / n [ q ]]
≼-stable {n = n} r R R' q (similar p) =
  similar $
    liftSub-to-~ p (nthSub n q (r ꞉ R))
                   (nthSub n q (r ꞉ R'))
                   (p' q $ ~annot R R' $ refl r)
  where ~-both : ∀{m n} → BinRel (𝒰 ⁺ ⊔ 𝒱) (Elim n ⊹ Elim m)
        ~-both (inl x)(inl x') = x ~ x'
        ~-both (inl x)(inr y) = Lift𝒰ᵖ ⊥
        ~-both (inr y)(inl x) = Lift𝒰ᵖ ⊥
        ~-both (inr y)(inr y') = y ~ y'
        private
          instance
            Relating[id+shift]~-both : ∀{m n} →
              Relating [ id + (shift {m = m}) ] (~-both {n = n}) ~-both
        rel-preserv ⦃ Relating[id+shift]~-both ⦄
          {inl x}{inl x'} x~x' = x~x'
        rel-preserv ⦃ Relating[id+shift]~-both {m} ⦄
          {inr y}{inr y'} y~y' =
          ap (shift ⦃ ren = RenameableElim ⦄) y~y'
        open import Substitution.Basic using (aux-nthSub)
        p″ : ∀{n m m'}{e e' : Elim m'}(q : n ≤ m)(p : e ~ e')
           → --------------------------------------------------
           Pointwise ~-both (aux-nthSub e n q) (aux-nthSub e' n q)
        p″ {zero} q p new = p
        p″ {zero} q p (old x) = refl (var x)
        p″ {n +1}{m +1} q p new = refl (var new)
        p″ {n +1}{m +1} q p (old x) =
          ap [ id + shift ] $ p″ (ap pred q) p x
        p' : ∀{n m}{e e' : Elim m}(q : n ≤ m)(p : e ~ e')
           → --------------------------------------------------
           Pointwise _~_ (nthSub n q e) (nthSub n q e')
        p' {n}{_}{e}{e'} q p x with p″ q p x
        ... | _ with aux-nthSub e n q x | aux-nthSub e' n q x
        p' _ _ _ | p | inl x | inl x' = p
        p' _ _ _ | p | inr y | inr y' = p
≼-stable r R R' q (sort p) = sort p
≼-stable {n = n} r R R' q ([_x:_]→_ π {T = T}{T'} S'≼S T≼T') =
  [ π x: ≼-stable r R' R q S'≼S ]→ (
    proof sub (lift (nthSub n q (r ꞉ R))) T
      〉 _==_ 〉 sub (nthSub (n +1) (ap suc q) (shift (r ꞉ R))) T
        :by: ap (λ — → sub — T) $ subrel {_P_ = _==_}$ fun-ext $
             lift-nth (r ꞉ R) q
      〉 _≼_ 〉 sub (nthSub (n +1) (ap suc q) (shift (r ꞉ R'))) T'
        :by: ≼-stable (shift r) (shift R) (shift R') (ap suc q) T≼T'
      〉 _==_ 〉 sub (lift (nthSub n q (r ꞉ R'))) T'
        :by: ap (λ — → sub — T') $ sym $ subrel {_P_ = _==_} $ fun-ext $
             lift-nth (r ꞉ R') q
    qed)
