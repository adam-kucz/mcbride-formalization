{-# OPTIONS --without-K --exact-split --safe --prop #-}
module Foundation.Prop'.Function where

open import Foundation.PropUniverses

id : (x : 𝑋) → 𝑋
id x = x
  
𝑖𝑑 : (𝑋 : 𝒰 ᵖ) (x : 𝑋) → 𝑋
𝑖𝑑 𝑋 = id

type-of : {𝑋 : 𝒰 ᵖ} (x : 𝑋) → 𝒰 ᵖ
type-of {𝑋 = 𝑋} _ = 𝑋

infixr 16 _$_
_$_ : {𝐴 : (p : 𝑋) → 𝒱 ᵖ}
  (f : (p : 𝑋) → 𝐴 p)
  (p : 𝑋)
  → -----------------------
  𝐴 p
f $ x = f x

infixl 25 _∘_
_∘_ : {𝐴 : (p : 𝑋) → 𝒰 ᵖ} {𝐾 : (p : 𝑋) (q : 𝐴 p) → 𝒱 ᵖ}
  (f : {p : 𝑋} (q : 𝐴 p) → 𝐾 p q)
  (g : (p : 𝑋) → 𝐴 p)
  → ----------------------------
  (p : 𝑋) → 𝐾 p (g p)
(f ∘ g) x = f (g x)
