{-# OPTIONS --exact-split --prop #-}
open import Basic
open import PropUniverses

module Subtyping.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Subtyping.Definition

-- open import Syntax
-- open import Renaming
-- open import Liftable
-- open import Substitution using (Sub; nthSub)
-- private
--   module Tag {tag : ExprTag} where
--     open import Substitution
--     open WithInstanceArgs ⦃ subst = SubstitutableExpr {tag = tag} ⦄ public
-- open Tag
-- open import Subtyping.Proof

-- open import Data.Nat
-- open import Relation.Binary.Pointwise
-- open import Function hiding (_$_; _~_)
-- open import Proof
-- open import Function.Proof

-- instance
--   RelatingSub-~ : {σ : Sub m n}
--     → ---------------------------
--     Relating (sub {tag} σ) _~_ _~_

-- rel-preserv ⦃ RelatingSub-~ {σ = σ} ⦄ (~annot S S' s~s') =
--   ~annot (sub σ S) (sub σ S') (rel-preserv s~s')
-- rel-preserv ⦃ RelatingSub-~ ⦄ (⋆ i) = ⋆ i
-- rel-preserv ⦃ RelatingSub-~ {σ = σ} ⦄ (var v) = refl (σ v)
-- rel-preserv ⦃ RelatingSub-~ ⦄ ([ π x: S~S' ]→ T~T') =
--   [ π x: rel-preserv S~S' ]→ rel-preserv T~T'
-- rel-preserv ⦃ RelatingSub-~ ⦄ (λx, t~t') = λx, rel-preserv t~t'
-- rel-preserv ⦃ RelatingSub-~ ⦄ (f~f' ` s~s') =
--   rel-preserv f~f' ` rel-preserv s~s'
-- rel-preserv ⦃ RelatingSub-~ ⦄ ⌊ e~e' ⌋ = ⌊ rel-preserv e~e' ⌋

-- instance
--   RelatingRename-~ : ∀{tag}
--     {ρ : Ren m n}
--     → ---------------
--     Relating (rename ⦃ r = RenameableExpr {tag = tag} ⦄ ρ) _~_ _~_

-- rel-preserv ⦃ RelatingRename-~ {ρ = ρ} ⦄ {a}{b} a~b =
--   proof rename ρ a
--     === sub (var ∘ ρ) a
--       :by: ap (λ — → — a) $ rename-as-sub ρ
--     〉 _~_ 〉 sub (var ∘ ρ) b
--       :by: ap (sub (var ∘ ρ)) a~b
--     === rename ρ b
--       :by: ap (λ — → — b) $ sym {R = _==_} $ rename-as-sub ρ
--   qed


-- instance
--   RelatingLiftPtwise~ :
--     Relating (lift {m = m}{n}) (Pointwise _~_) (Pointwise _~_)

-- rel-preserv ⦃ RelatingLiftPtwise~ ⦄ σ~σ' new = refl (var new)
-- rel-preserv ⦃ RelatingLiftPtwise~ ⦄ σ~σ' (old x) =
--   ap (shift ⦃ ren = RenameableExpr ⦄) (σ~σ' x)

-- liftSub-to-~ : ∀
--   {e e' : expr-of-type tag m}
--   (p : e ~ e')
--   (σ σ' : Sub m n)
--   (q : Pointwise _~_ σ σ')
--   → ---------------
--   sub σ e ~ sub σ' e'
-- liftSub-to-~ (~annot S S' s~s') σ σ' q =
--   ~annot (sub σ S) (sub σ' S') (liftSub-to-~ s~s' σ σ' q)
-- liftSub-to-~ (⋆ i) σ σ' q = ⋆ i
-- liftSub-to-~ (var v) σ σ' q = q v
-- liftSub-to-~ ([ π x: S~S' ]→ T~T') σ σ' q =
--   [ π x: liftSub-to-~ S~S' σ σ' q ]→
--     liftSub-to-~ T~T' (lift σ)(lift σ')(ap lift q)
-- liftSub-to-~ (λx, t~t') σ σ' q =
--   λx, liftSub-to-~ t~t' (lift σ) (lift σ') (ap lift q)
-- liftSub-to-~ (f~f' ` s~s') σ σ' q =
--   liftSub-to-~ f~f' σ σ' q ` liftSub-to-~ s~s' σ σ' q
-- liftSub-to-~ ⌊ e~e' ⌋ σ σ' q = ⌊ liftSub-to-~ e~e' σ σ' q ⌋

