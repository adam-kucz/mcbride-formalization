{-# OPTIONS --exact-split --prop --safe #-}
module Relation.Binary.Diamond where

open import PropUniverses

open import Relation.Binary using (Rel)
open import Relation.Binary using (
    refl ; _⊆_; subrel;
    refl-trans-close; rfl; step; subrel-rtc-to-rtc-subrel-rtc)
open import Logic
  using (∃; _∧_; _,_)

-- Definition 10 (diamond property)

diamond : {X : 𝒵 ˙} (R : Rel 𝒴 X X) → 𝒵 ⊔ 𝒴 ᵖ
diamond _R_ = ∀ {s p q}
  (sRp : s R p)
  (sRq : s R q)
  → ------------
  ∃ λ r → p R r ∧ q R r

-- Lemma 11 (parallelogram)

diamond-to-rtc-diamond :
  {R : Rel 𝒴 X X}
  (diamond-R : diamond R)
  → ----------------------
  diamond (refl-trans-close R)
diamond-to-rtc-diamond {R = _R_} diamond-R = go
  where _R*_ = refl-trans-close _R_
        go : diamond _R*_
        go {s} {s} {q} (rfl s) sR*q = q , (sR*q , refl q)
        go {s} {p} {q} (step {s} {s'} {p} sRs' s'R*p) sR*q = hi
          where hi : ∃ λ r → p R* r ∧ q R* r
                q'step : ∀ {s s'}
                  (sRs' : s R s')
                  (sR*q : s R* q)
                  → -------------------------
                  ∃ λ q' → s' R* q' ∧ q R q'
                hi with q'step sRs' sR*q
                hi | q' , (s'R*q' , qRq') with go s'R*p s'R*q'
                hi | _ , (_ , qRq') | r , (pR*r , q'R*r) =
                  r , (pR*r , step qRq' q'R*r)
                q'step {s} {s'} sRs' (rfl s) = s' , (refl s' , sRs')
                q'step sRs' (step sRt tR*q) with diamond-R sRs' sRt
                q'step sRs' (step sRt tR*q) | t' , (s'Rt' , tRt') with q'step tRt' tR*q
                q'step sRs' (step sRt tR*q) | t' , (s'Rt' , tRt') | q' , (t'R*q' , qRq') =
                  q' , (step s'Rt' t'R*q' , qRq')

parallelogram :
  (R : Rel 𝒴 X X)
  {P : Rel 𝒵 X X} ⦃ R⊆P : R ⊆ P ⦄ ⦃ P⊂R* : P ⊆ refl-trans-close R ⦄
  (diamond-P : diamond P)
  → ----------------------
  diamond (refl-trans-close R)
parallelogram R {P} diamond-P = result
  where diamond-rtc-P : diamond (refl-trans-close P)
        result : diamond (refl-trans-close R)
        result sR*p sR*q with diamond-rtc-P (subrel sR*p) (subrel sR*q)
        result sR*p sR*q | q , (left , right) = q , (P*→R* left , P*→R* right)
          where P*→R* = subrel ⦃ subrel-rtc-to-rtc-subrel-rtc ⦄
        diamond-rtc-P = diamond-to-rtc-diamond diamond-P

