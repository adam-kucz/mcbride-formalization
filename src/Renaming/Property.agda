{-# OPTIONS --exact-split --prop #-}
open import Basic
open import Universes

module Renaming.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {𝑆 : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Renaming.Definition
open import Renaming.Syntax

open import Syntax
open import Liftable

open import Data.Nat
open import Proposition.Identity hiding (refl)
open import Proposition.Identity.Coercion
open import Function hiding (_$_)
open import Proof

old×-old : ∀ k → old× k ∘ old {n = m} ~ old× (k +1)
old×-old zero = refl old
old×-old {m} (k +1) v =
  Id.ap2 (λ i v' → old {n = i} v')
         (+-suc k m)
         (old×-old k v)

open import Collection
open import Data.List hiding (_++_)
open import Data.Functor
open import Data.Monad
open import Data.List.Functor

open import Axiom.FunctionExtensionality

private
  prevSafe-lift : (ρ : Ren m n)
    → ------------------------------------------------------
    prevSafe ∘ rename (lift ρ) == fmap (rename ρ) ∘ prevSafe
prevSafe-lift ρ = subrel $ fun-ext λ
  { new → Het.refl []
  ; (old v) → Het.refl [ ρ v ]}

fv-ren :
  (ρ : Ren m n)
  (e : expr-of-type tag m)
  → --------------------------------------------------
  fv (rename ⦃ r = RenameableExpr ⦄ ρ e) == rename ρ <$> fv e
fv-ren {tag = term} ρ (⋆ i) = Id-refl []
fv-ren {tag = term} ρ ([ _ x: S ]→ T) =
  proof fv (rename ⦃ r = RenameableTerm ⦄ ρ S) ++
        (fv (rename (lift ρ) T) >>= prevSafe)
    === (rename ρ <$> fv S) ++
        ((rename (lift ρ) <$> fv T) >>= prevSafe)
      :by: ap2 (λ s t → s ++ (t >>= prevSafe))
               (fv-ren ρ S) (fv-ren (lift ρ) T)
    === (rename ρ <$> fv S) ++ (fv T >>= prevSafe ∘ rename (lift ρ))
        :by: ap ((rename ρ <$> fv S) ++_) $
             fmap-bind₀ (fv T) (rename (lift ρ)) prevSafe
    === (rename ρ <$> fv S) ++ (fv T >>= fmap (rename ρ) ∘ prevSafe)
        :by: ap (λ — → (rename ρ <$> fv S) ++ (fv T >>= —)) $
             prevSafe-lift ρ
    === (rename ρ <$> fv S) ++ (rename ρ <$> (fv T >>= prevSafe))
        :by: ap ((rename ρ <$> fv S) ++_) $
             sym $ fmap-bind₁ (fv T) prevSafe (rename ρ)
    === rename ρ <$> (fv S ++ (fv T >>= prevSafe))
      :by: sym $ fmap-++ (rename ρ) (fv S) (fv T >>= prevSafe)
  qed
fv-ren {tag = term} ρ (λx, t) =
  proof fv (rename ⦃ r = RenameableTerm ⦄ ρ (λx, t))
    === fv (rename (lift ρ) t) >>= prevSafe
      :by: Id-refl _
    === (rename (lift ρ) <$> fv t) >>= prevSafe
      :by: ap (_>>= prevSafe) $ fv-ren (lift ρ) t
    === fv t >>= prevSafe ∘ rename (lift ρ)
      :by: fmap-bind₀ (fv t) (rename (lift ρ)) prevSafe
    === fv t >>= fmap (rename ρ) ∘ prevSafe
      :by: ap (fv t >>=_) $ prevSafe-lift ρ
    === rename ρ <$> (fv t >>= prevSafe)
      :by: sym $ fmap-bind₁ (fv t) prevSafe (rename ρ)
  qed
fv-ren {tag = term} ρ ⌊ e ⌋ = fv-ren ρ e
fv-ren {tag = elim} ρ (var v) = Id-refl [ ρ v ]
fv-ren {tag = elim} ρ (f ` s) =
  proof fv (rename ⦃ r = RenameableElim ⦄ ρ f) ++
        fv (rename ⦃ r = RenameableTerm ⦄ ρ s)
    === (rename ρ <$> fv f) ++ (rename ρ <$> fv s)
      :by: ap2 _++_ (fv-ren ρ f) (fv-ren ρ s)
    === rename ρ <$> fv f ++ fv s
      :by: sym $ fmap-++ (rename ρ) (fv f) (fv s)
  qed
fv-ren {tag = elim} ρ (s ꞉ S) =
  proof fv (rename ⦃ r = RenameableTerm ⦄ ρ s) ++
        fv (rename ⦃ r = RenameableTerm ⦄ ρ S)
    === (rename ρ <$> fv s) ++ (rename ρ <$> fv S)
      :by: ap2 _++_ (fv-ren ρ s) (fv-ren ρ S)
    === rename ρ <$> fv s ++ fv S
      :by: sym $ fmap-++ (rename ρ) (fv s) (fv S)
  qed
