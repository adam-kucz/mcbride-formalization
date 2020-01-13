{-# OPTIONS --exact-split --safe --prop  #-}
module Basic where

open import Universes
open import Structure.Hemiring
open import Data.Nat.Definition hiding (zero)
import Data.Nat.Syntax
open import Data.FinNat.Definition hiding (zero)

-- Definition 1 (rig)

open import Proposition.Identity using (_==_; refl)

Rig : (X : 𝒰 ˙) → 𝒰 ˙
Rig = Hemiring

-- Definition 2 (none-one-tons)
None-one-tons : 𝒰₀ ˙
None-one-tons = Finℕ 3

ω : None-one-tons
ω = 2

-- Definition 3 (sort ordering)

record WellFoundedSorts (𝒰 𝒱 : Universe) (S : 𝒲 ˙) : (𝒰 ⊔ 𝒱) ⁺ ⊔ 𝒲 ˙ where
  field
    _≻_ : (i : S) → (j : S) → 𝒰 ˙
    
    trans : ∀ {i j k}
      (k≻j : k ≻ j) → (j≻i : j ≻ i)
      → --------------------------
      k ≻ i
    
    wf : ∀ {j} {P : S → 𝒱 ˙} →
      (all≺ : ∀ i { j≻i : j ≻ i } → P i)
      → ------------------------
      ∀ k → P k

open WellFoundedSorts ⦃ ... ⦄ public

wfs : ∀ 𝒰 𝒱 (S : 𝒲 ˙) → (𝒰 ⊔ 𝒱) ⁺ ⊔ 𝒲 ˙
wfs = WellFoundedSorts