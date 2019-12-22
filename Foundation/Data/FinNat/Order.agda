{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Data.FinNat.Order where

open import Foundation.Data.FinNat.Definition
open import Foundation.Data.FinNat.Arithmetic
open import Foundation.Data.FinNat.Property
open import Foundation.Data.Nat using (ℕ; _<_; _≤_; z<s; s<s; min; min<s)

open import Foundation.PropUniverses
open import Foundation.Prop'.Identity
  renaming (Idₚ to Id) using (_==_)
open import Foundation.Logic
open import Foundation.Prop'.Function using (_$_; _∘_)

open import Foundation.Relation.Binary
open import Foundation.Prop'.Decidable
open import Foundation.Function.Proof
open import Foundation.Proof
open import Foundation.Data.Nat.Proof

private
  variable
    n m : ℕ
    a b : Finℕ n

infix 35 _<ₛ_
data _<ₛ_ : Finℕ n → Finℕ m → 𝒰₀ ᵖ where
  z<ₛs : zero {n} <ₛ suc a
  s<ₛs : (a<ₛb : a <ₛ b) → suc a <ₛ suc b

s<s→-<- : (p : suc a <ₛ suc b) → a <ₛ b
s<s→-<- (s<ₛs p) = p

instance
  Irreflexive<ₛ : Irreflexive (_<ₛ_ {n} {n})
  irrefl ⦃ Irreflexive<ₛ ⦄ zero ()
  irrefl ⦃ Irreflexive<ₛ ⦄ (suc n) sn<sn = irrefl n (s<s→-<- sn<sn)

  Asymmetirc<ₛ : Asymmetric (_<ₛ_ {n} {n})
  asym ⦃ Asymmetirc<ₛ ⦄ z<ₛs ()
  asym ⦃ Asymmetirc<ₛ ⦄ (s<ₛs a<b) (s<ₛs b<a) = asym b<a a<b
  
  Transitive<ₛ : Transitive (_<ₛ_ {n} {n})
  trans ⦃ Transitive<ₛ ⦄ z<ₛs (s<ₛs _) = z<ₛs
  trans ⦃ Transitive<ₛ ⦄ (s<ₛs a<b) (s<ₛs b<c) = s<ₛs (trans a<b b<c)

  Decidable<ₛ : ∀ {n} {a b : Finℕ n} → Decidable (a <ₛ b)
  Decidable<ₛ {a = zero} {zero} = false (λ ())
  Decidable<ₛ {a = zero} {suc n} = true z<ₛs
  Decidable<ₛ {a = suc m} {zero} = false (λ ())
  Decidable<ₛ {a = suc m} {suc n} with decide (m <ₛ n)
  Decidable<ₛ {a = suc m} {suc n} | true n<m = true (s<ₛs n<m)
  Decidable<ₛ {a = suc m} {suc n} | false ¬n<m = false λ m<n → ¬n<m (s<s→-<- m<n)
  
  Relating-suc-<ₛ : ∀ {n} → Relating (suc {n}) _<ₛ_ _<ₛ_
  rel-preserv ⦃ Relating-suc-<ₛ ⦄ = s<ₛs

  Postfix-suc-<ₛ : ∀ {n} → UniversalPostfix (suc {n}) _<ₛ_
  UniversalPostfix.postfix Postfix-suc-<ₛ zero = z<ₛs
  UniversalPostfix.postfix Postfix-suc-<ₛ (suc x) = s<ₛs $ postfix suc x

  Relating-maxFinℕ : Relating (λ n → maxFinℕ {n}) _<_ _<ₛ_
  rel-preserv ⦃ Relating-maxFinℕ ⦄ z<s = z<ₛs
  rel-preserv ⦃ Relating-maxFinℕ ⦄ (s<s rab) = s<ₛs (rel-preserv rab)

  Relating-toℕ : Relating (toℕ {n}) _<ₛ_ _<_
  rel-preserv ⦃ Relating-toℕ ⦄ z<ₛs = z<s
  rel-preserv ⦃ Relating-toℕ ⦄ (s<ₛs rab) = s<s (rel-preserv rab)

infix 35 _≤ₛ_
_≤ₛ_ : Finℕ n → Finℕ n → 𝒰₀ ᵖ
a ≤ₛ b = a == b ∨ a <ₛ b

instance
  Reflexive≤ₛ : Reflexive (_≤ₛ_ {n})
  refl ⦃ Reflexive≤ₛ ⦄ a = ∨left (refl a)
  
  Transitive≤ₛ : Transitive (_≤ₛ_ {n})
  trans ⦃ Transitive≤ₛ ⦄ (∨left (Id.refl a)) a≤b = a≤b
  trans ⦃ Transitive≤ₛ ⦄ (∨right a<b) (∨left (Id.refl b)) = ∨right a<b
  trans ⦃ Transitive≤ₛ ⦄ (∨right a<b) (∨right b<c) = ∨right $ trans a<b b<c
  
  Antisym≤ₛ : Antisymmetric (_≤ₛ_ {n})
  antisym ⦃ Antisym≤ₛ ⦄ (∨left a==b) _ = a==b
  antisym ⦃ Antisym≤ₛ ⦄ (∨right _) (∨left b==a) = sym b==a
  antisym ⦃ Antisym≤ₛ ⦄ (∨right a<b) (∨right b<a) = ⊥-recursion _ (asym a<b b<a)

  Relating-suc-≤ₛ : Relating suc (_≤ₛ_ {n}) (_≤ₛ_ {ℕ.suc n})
  rel-preserv ⦃ Relating-suc-≤ₛ ⦄ (∨left (Id.refl x)) = refl (suc x)
  rel-preserv ⦃ Relating-suc-≤ₛ ⦄ (∨right a<b) = ∨right (ap suc a<b)

  Relating-cap : Relating (λ m → toℕ (cap m n)) _≤_ _≤_
  rel-preserv ⦃ Relating-cap {n} ⦄ {m} {m'} m≤m' = 
    proof toℕ $' cap m n
      〉 _==_ 〉 toℕ $' toFinℕ (min m n) (min<s m n) :by: refl _
      〉 _==_ 〉 min m n :by: toℕ-toFinℕ (min<s m n)
      〉 _≤_  〉 min m' n :by: rel-preserv m≤m'
      〉 _==_ 〉 toℕ $' toFinℕ (min m' n) (min<s m' n)
        :by: sym $ toℕ-toFinℕ (min<s m' n)
      〉 _==_ 〉 toℕ $' cap m' n :by: refl _
    qed
    where open import Foundation.Function
            renaming (_$_ to _$'_) using ()

