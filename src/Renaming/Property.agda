{-# OPTIONS --exact-split #-}
open import Basic
open import Universes

module Renaming.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {𝑆 : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 𝑆 ⦄
  where

open import Renaming.Definition ⦃ rig ⦄ ⦃ wfs ⦄
open import Renaming.Syntax ⦃ rig ⦄ ⦃ wfs ⦄

open import Syntax ⦃ rig ⦄ ⦃ wfs ⦄
open import Liftable ⦃ rig ⦄ ⦃ wfs ⦄

open import Data.Nat
open import Function hiding (_$_)
open import Proof

old×-old : ∀ k → old× k ∘ old {n = m} ~ old× (k +1)
old×-old zero = refl old
old×-old {m} (k +1) v =
  Het.ap2 (λ i v' → old {n = i} v')
          (subrel $ +-suc k m)
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
  ren = λ {tag}{m}{n} → rename ⦃ r = RenameableExpr {tag = tag} ⦄ {m}{n}
  renv = λ {m}{n} → rename ⦃ r = RenameableVar ⦄ {m}{n}

prevSafe-lift ρ = subrel $ fun-ext λ
  { new → Het.refl []
  ; (old v) → Het.refl [ ρ v ]}

fv-ren :
  (ρ : Ren m n)
  (e : expr-of-type tag m)
  → --------------------------------------------------
  fv (ren ρ e) == renv ρ <$> fv e
fv-ren {tag = term} ρ (⋆ i) = Id.refl []
fv-ren {tag = term} ρ ([ _ x: S ]→ T) =
  proof fv (ren ρ S) ++ (fv (ren (lift ρ) T) >>= prevSafe)
    === (renv ρ <$> fv S) ++
        ((renv (lift ρ) <$> fv T) >>= prevSafe)
      :by: ap2 (λ s t → s ++ (t >>= prevSafe))
               (fv-ren ρ S) (fv-ren (lift ρ) T)
    === (renv ρ <$> fv S) ++ (fv T >>= prevSafe ∘ renv (lift ρ))
        :by: ap (fmap ⦃ ListFunctor ⦄ (renv ρ) (fv S) ++_) $
             fmap-bind₀ (fv T) (renv (lift ρ)) prevSafe
    === (renv ρ <$> fv S) ++ (fv T >>= fmap (renv ρ) ∘ prevSafe)
        :by: ap (λ — → (renv ρ <$> fv S) ++ (fv T >>= —)) $
             prevSafe-lift ρ
    === (renv ρ <$> fv S) ++ (renv ρ <$> (fv T >>= prevSafe))
        :by: ap (fmap ⦃ ListFunctor ⦄ (renv ρ) (fv S) ++_) $
             sym $ fmap-bind₁ (fv T) prevSafe (renv ρ)
    === renv ρ <$> (fv S ++ (fv T >>= prevSafe))
      :by: sym $ fmap-++ (renv ρ) (fv S) (fv T >>= prevSafe)
  qed
fv-ren {tag = term} ρ (λx, t) =
  proof fv (ren ρ (λx, t))
    === fv (ren (lift ρ) t) >>= prevSafe
      :by: Id.refl _
    === (renv (lift ρ) <$> fv t) >>= prevSafe
      :by: ap (_>>= prevSafe) $ fv-ren (lift ρ) t
    === fv t >>= prevSafe ∘ renv (lift ρ)
      :by: fmap-bind₀ (fv t) (renv (lift ρ)) prevSafe
    === fv t >>= fmap (renv ρ) ∘ prevSafe
      :by: ap (fv t >>=_) $ prevSafe-lift ρ
    === renv ρ <$> (fv t >>= prevSafe)
      :by: sym $ fmap-bind₁ (fv t) prevSafe (renv ρ)
  qed
fv-ren {tag = term} ρ ⌊ e ⌋ = fv-ren ρ e
fv-ren {tag = elim} ρ (var v) = Id.refl [ ρ v ]
fv-ren {tag = elim} ρ (f ` s) =
  proof fv (ren ρ f) ++ fv (ren ρ s)
    === (renv ρ <$> fv f) ++ (renv ρ <$> fv s)
      :by: ap2 _++_ (fv-ren ρ f) (fv-ren ρ s)
    === renv ρ <$> fv f ++ fv s
      :by: sym $ fmap-++ (renv ρ) (fv f) (fv s)
  qed
fv-ren {tag = elim} ρ (s ꞉ S) =
  proof fv (ren ρ s) ++ fv (ren ρ S)
    === (renv ρ <$> fv s) ++ (renv ρ <$> fv S)
      :by: ap2 _++_ (fv-ren ρ s) (fv-ren ρ S)
    === renv ρ <$> fv s ++ fv S
      :by: sym $ fmap-++ (renv ρ) (fv s) (fv S)
  qed
